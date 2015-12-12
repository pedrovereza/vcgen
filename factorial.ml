#use "vcgen.ml"

let fat =
  Seq ( Seq ( Asg ( "y" , Num 1 ) , Asg ( " z " , Num 0 )),
  Wh(PUneq ( Var ( " z " , Prog ) , Var ( "x" , Prog )),
  AEq( Var ( "y" , Prog ) , Fat ( Var ( " z " , Prog ))),
  Seq ( Asg ( " z " , Sum( Var ( " z " , Prog ) , Num 1 )),
  Asg ( "y" , Mult ( Var ( "y" , Prog ) , Var (" z " , Prog))))))

let fatstr = astnTostr(vcgen ((ALeq (Num 0 , Var ( "x" , Prog ))), fat, AEq( Var ( "y" , Prog ) , Fat ( Var ( "x" , Prog )))))
let () = print_string fatstr;;
