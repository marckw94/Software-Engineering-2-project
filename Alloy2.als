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

//The system must generate password only when user wants  to register,no useless password 
fact noAlonePassoword{
	no p1:Password|!(p1 in User.password) 

}
// There is only one Email for one user
fact noAloneEmail{
	no m1:Email|!(m1 in User.email)
}
// An user can't reserve more than one car at the same type
fact noUserWithMoreReserv{
	no r1,r2:Reservation | r1!=r2 and (r1.driver=r2.driver or r1.carDrive=r2.carDrive)
}
// There aren't user with same passowrd or email, an user can register only one time
fact twoTypeUser{
	no u1,u2: User | u1!=u2 and (u1.password=u2.password or u1.email=u2.email)
}
// An user have a journey (ride car) if only if reservation time is not over
fact journeyOnlyTimeIsNotExpired{ 
	no j1: Journey | j1.reservation.timeUnlock=OutTime 

}
// A reservation correspond only one journey, reservation is unique
fact notExistTwoSameJourney{
	no j1,j2: Journey | j1!=j2 and (j1.reservation=j2.reservation)
}
// If user unlock the car in time,he has a journey, nott exist a journey if the reservation time is over
fact eachReservationInTimeHasJourney{
	no r1:Reservation | r1.timeUnlock=OutTime && r1 in Journey.reservation
}
//when a user reserve a car,car state must change into not available, not exist reserved car with available state
fact reservedCarMustBeNotAvailable{
	no r1:Reservation | r1.carDrive.availability=Available
}
//It's not possible reserve a car with its battery is 20%
fact noReservedCarWithLowerBattery{
	no r1:Reservation | r1.carDrive.batteryState=Lower20Battery
}
// if a carBattery is lower than 20%,car state must be not available
fact lowerBatteryChangeState{
	all c1:Car | c1.batteryState=Lower20Battery  implies c1.availability=NotAvailable
}
// There aren't any cars with batteries upper than 20 and  not-available states that they are not a reserved cars
fact noOtherConditionToReservedCar{
	no c1:Car|c1.batteryState=Upper20Battery && c1.availability=NotAvailable && !(c1 in Reservation.carDrive)
}
// A bill correspond at one and only one journey 
fact noBillWithMoreJourney{
	no b1,b2:Bill | b1!=b2 and (b1.journey=b2.journey)
}
// if user takes more than one discount,he will take only the bigger one
//if user takes a fee during the ride and other discount, the bill will count only the fee.
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

/*
assert NoJourneyWithAvailableCar{
	no j1:Journey| j1.reservation.carDrive.availability=Available
}

assert NoReservationWithNoBattery{
	no r1:Reservation|r1.carDrive.batteryState=Lower20Battery
}
check NoJourneyWithAvailableCar 

 check NoReservationWithNoBattery*/
 
pred show{

}
 run show for 4
