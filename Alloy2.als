open util/boolean
sig Email{}
sig Password{}
abstract sig BatteryState{}
abstract sig TimeUnlock{}
abstract sig Availability{}
abstract sig Payment{}
abstract sig PluginFee{}
abstract sig PluginDiscount{}
abstract sig PassengerDiscount{}
abstract sig BatteryDiscount{}


sig Fee30 extends Payment{}
sig Discount30 extends Payment{}
sig Discount20 extends Payment{}
sig Discount10 extends Payment{}
sig NormalPay extends Payment{}




sig Upper20Battery extends BatteryState{}{#Upper20Battery=1}
sig Lower20Battery extends BatteryState{}{#Lower20Battery=1}

sig Available extends Availability{}{#Available=1}
sig NotAvailable extends Availability{}{#NotAvailable=1}

sig InTime extends TimeUnlock{}{#InTime=1}
sig OutTime extends TimeUnlock{}{#OutTime=1}

sig YesPassengers extends PassengerDiscount{}{#YesPassengers=1 }
sig NoPassengers extends PassengerDiscount{}{#NoPassengers=1}

sig YesBattery extends BatteryDiscount{}{#YesBattery=1}
sig NoBattery extends BatteryDiscount{}{#NoBattery=1}

sig YesPluginDiscount extends PluginDiscount{}{#YesPluginDiscount =1}
sig NoPluginDiscount extends PluginDiscount{}{#NoPluginDiscount = 1}

sig YesPluginFee extends PluginFee{}{#YesPluginFee =1}
sig NoPluginFee extends PluginFee{}{#NoPluginFee =1}

sig User{
 	email: one Email,
	password :one Password,

}
sig Car{
	availability: one Availability,	
	batteryState: one BatteryState
}

sig Reservation{
	driver:User,
	carDrive: Car,
	timeUnlock: one TimeUnlock
	
}

sig Journey{
	reservation : one Reservation,
	passengerDiscount: one PassengerDiscount,
	batteryDiscount: one BatteryDiscount,
	pluginFee : one PluginFee,
	pluginDiscount:one PluginDiscount	
 }

sig Bill{
	journey: one Journey,
	payment: one Payment 
	
}


//    ________________________________Facts______________________________________

fact noAloneThings{
no p1:Password|!(p1 in User.password) 
no m1:Email|!(m1 in User.email)

}

fact noUserWithMoreReserv{
	no r1,r2:Reservation | r1!=r2 and (r1.driver=r2.driver or r1.carDrive=r2.carDrive)
}

fact twoTypeUser{
	no u1,u2: User | u1!=u2 and (u1.password=u2.password or u1.email=u2.email)
}

fact journeyOnlyTimeIsNotExpired{ 
	no j1: Journey | j1.reservation.timeUnlock=OutTime 
	no j1,j2: Journey | j1!=j2 and (j1.reservation=j2.reservation)
}

fact eachReservationInTimeHasJourney{
	no r1:Reservation | r1.timeUnlock=OutTime && r1 in Journey.reservation
}

fact carAvailableOnlyRegisterForReservation{
	no r1:Reservation | r1.carDrive.availability=Available
	no r1:Reservation | r1.carDrive.batteryState=Lower20Battery
	all c1:Car | c1.batteryState=Lower20Battery  implies c1.availability=NotAvailable
	no c1:Car|c1.batteryState=Upper20Battery && c1.availability=NotAvailable && !(c1 in Reservation.carDrive)
}

fact noBillWithMoreJourney{

	no b1,b2:Bill | b1!=b2 and (b1.journey=b2.journey)
}

fact whatDiscountOrFee{
	all b1:Bill|b1.journey.passengerDiscount=NoPassengers && b1.journey.batteryDiscount=NoBattery && b1.journey.pluginDiscount=NoPluginDiscount && b1.journey.pluginFee=NoPluginFee=>b1.payment=NormalPay
	no b1:Bill|(b1.journey.passengerDiscount=YesPassengers || b1.journey.batteryDiscount=YesBattery || b1.journey.pluginDiscount=YesPluginDiscount ||b1.journey.pluginFee=YesPluginFee) &&b1.payment=NormalPay
	no b1:Bill|b1.journey.pluginFee=YesPluginFee && b1.payment!=Fee30
	no b1:Bill|b1.journey.pluginFee=NoPluginFee && b1.journey.pluginDiscount=YesPluginDiscount &&b1.payment!=Discount30
	no b1:Bill|b1.journey.pluginFee=NoPluginFee && b1.journey.pluginDiscount=NoPluginDiscount && b1.journey.batteryDiscount=YesBattery && b1.payment!=Discount20
	no b1:Bill|b1.journey.pluginFee=NoPluginFee && b1.journey.pluginDiscount=NoPluginDiscount && b1.journey.batteryDiscount=NoBattery && b1.journey.passengerDiscount=YesPassengers && b1.payment!=Discount10
}

fact onlyPassengerSensorUntilTheBill{
	no j1:Journey|!(j1 in Bill.journey) && (j1.batteryDiscount=YesBattery ||j1.pluginDiscount=YesPluginDiscount||j1.pluginFee=YesPluginFee)
}

//   ______________________________Assertions______________________________________


/*assert NoJourneyWithAvailableCar{
	no j1:Journey| j1.reservation.carDrive.availability=Available
}

assert NoReservationWithNoBattery{
	no r1:Reservation|r1.carDrive.batteryState=Lower20Battery
}
check NoJourneyWithAvailableCar 

 check NoReservationWithNoBattery
 */
pred show{

}
 run show for 4
