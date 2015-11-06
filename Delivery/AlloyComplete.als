//--------Signatures--------//

abstract sig User{}

sig TaxiDriver extends User {
		license: one License,
		aval: one Availability
}

sig License{}

sig Customer extends User {}

abstract sig Trip {
	    customer: one Customer,
        taxidriver: one TaxiDriver,
		zone: one Zone
}

sig Request extends Trip{} 

sig Reservation extends Trip{
		destination: one Zone
}

abstract sig Notification {}

sig NotificationRequest extends Notification{
		request: one Request
}

sig NotificationReservation extends Notification {
		reservation: one Reservation
}

sig NotificationCall extends Notification{
		customer: one Customer,
		taxidriver: one TaxiDriver,
		zone: one Zone
} 

sig Availability {
		aval: one Int
}{aval>=0 aval<=1}

sig Zone {
		queuetaxi: set TaxiDriver
}
	
//--------Facts--------//

//Each Request corresponds only to one NotificationRequest
fact OneNotReqPerRequest{
		all r:Request | (one nr:NotificationRequest| nr.request=r)
}

//Each Reservtion corresponds to only one NotificationReservation
fact OneNotiResPerReservation{
		all r:Reservation | (one nr:NotificationReservation | nr.reservation=r)
}

//There are only different Trips
fact OneTaxiDriverCustomePerTrip{
	    no disj tp1,tp2: Trip | (tp1.customer=tp2.customer or
										  tp1.taxidriver=tp2.taxidriver )
}

//Each TaxiDriver has different license
fact DifferenctLicense{
		all l:License | (one t:TaxiDriver | t.license = l)
}

//A TaxiDriver is not available iff he does a Trip
fact NotAvailableStatus{
		all t:TaxiDriver | (one tp:Trip | tp.taxidriver=t) <=> t.aval.aval=0
}

//A TaxiDriver is available iff he's in a queue of taxis
fact AvailableStatus{
		all t:TaxiDriver | (one z:Zone | t in z.queuetaxi) <=> t.aval.aval=1
}

//Each TaxiDriver can be only in one queue
fact TaxiOnlyOneQueue{

		all t:TaxiDriver | (lone z:Zone| t in z.queuetaxi)
}

//Only available TaxiDrivers can receive a NotificationCall
fact CallAvailTaxi{
		all t:TaxiDriver | (one c:NotificationCall | c.taxidriver=t) => t.aval.aval=1
}

//Only Customer that they aren't on a taxi can call one
fact CallCustomer{
		all c:Customer| (one nc:NotificationCall | nc.customer=c) => (all t:Trip | c!=t.customer)
}

//A Customer can do only one request/reservation at time
fact OneNotificationCallPerCustomer{
		all c:Customer | (lone n:NotificationCall | n.customer=c)
}


//Each NotificationCall corresponds to only one available TaxiDriver
fact OneNotCallPerTaxi{
		all t:TaxiDriver | (lone n:NotificationCall | n.taxidriver=t)
}

//A NotificationCall must be send to a TaxiDriver in the right Zone
fact NotificationCallInRightZone{
		all n:NotificationCall | (one z:Zone | n.taxidriver in z.queuetaxi and n.zone=z)
}

//--------Asserts--------//

//Check that a Customer can requests/reserves only one Taxi at time
assert OneRequestPerCustomer{
		no n1,n2:Request | (n1.customer=n2.customer and n1!=n2)
}

check OneRequestPerCustomer

//Check that each TaxiDriver can do at most one Trip
assert NoOneTaxiForDifferentTrips{
		no t1,t2:Trip | (t1.taxidriver=t2.taxidriver and t1!=t2)
}
check NoOneTaxiForDifferentTrips

//Check when a TaxiDriver confirms a call
assert RequestTrip{
		all t:Trip, z1,z2:Zone, t1,t2:TaxiDriver | 
						((t1.aval.aval=1 and t1 in z1.queuetaxi and RequestTrip[t,z1,z2,t1,t2]) implies 
									(t2.aval.aval=0) and t2 not in z2.queuetaxi and t.taxidriver=t2)
}
check RequestTrip

//Check when a TaxiDriver became available after a Trip
assert AvailableTaxi{
	    all t1,t2:TaxiDriver, z1,z2:Zone, t:Trip |
						(t1.aval.aval=0 and t.taxidriver=t1 and t1 not in z1.queuetaxi and AvailableTaxi[t1,t2,z1,z2,t] implies
									(t2.aval.aval=1) and t.taxidriver!=t2 and t2 in z2.queuetaxi)
}
check AvailableTaxi

//--------Predicates--------//

//Show a world with a TaxiDriver that confirms a call
pred RequestTrip(t: Trip,  z1, z2:Zone, t1, t2:TaxiDriver){ 
		t1.aval.aval=1 implies t2.aval.aval=0 and
		(t1 in z1.queuetaxi implies t2 not in z2.queuetaxi) and
		t.taxidriver=t2 
		#Zone =2
		#Availability =2
}
run RequestTrip

//Show a world with a TaxiDriver that finishes his trip and he became available
pred AvailableTaxi(t1,t2:TaxiDriver, z1,z2: Zone, t:Trip){
		t1.aval.aval=0 implies t2.aval.aval=1 and (t1 not in z1.queuetaxi implies t2 in z2.queuetaxi) 
		and (t.taxidriver=t1 implies t.taxidriver!=t2)
		#Availability=2
		#Zone=2
}
run AvailableTaxi	


//Show a complete world
pred show1 {
#TaxiDriver=7
#Customer=6
#Request=2
#Reservation=2
#Zone=4
#Availability=2
#NotificationCall=2
}
run show1 for 15

//Show another a complete world
pred show2{
#Notification=3
#Zone=2
#Availability=2
}
run show2 for 8


	
		
