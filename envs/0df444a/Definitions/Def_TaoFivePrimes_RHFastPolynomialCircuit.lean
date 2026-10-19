-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuit
-- name    : TaoFivePrimes_RHFastPolynomialCircuit
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:30:53.920119+00:00
-- url     : https://prove2.me/theorems/dd9ec811-770e-4347-af2e-7894341a0279
-- title:
--   Short center polynomial integer circuit
-- statement:
--   A transparent expression circuit for the degree28 center approximation, evaluated by ordinary fixed-point ball polynomial operations. Analytic accuracy is a separate theorem.
-- source:
--   Platt DOI10.1090/mcom/3198; original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_TaoFivePrimes_RHFastBallPolynomialArithmetic
namespace RHFastPolynomialCircuit
open RHFastBallArithmetic
inductive Expr where
 | zero | one | imag | variable | input (i:Nat)
 | rational (p:Int) (q:Nat)
 | add (a b:Expr) | mul (a b:Expr)
 | divide (a:Expr) (n:Nat)
 | power (a:Expr) (n:Nat)
noncomputable def powerList (D:Nat) (a:List Ball) : Nat→List Ball
 |0=>[integer D 1]
 |n+1=>RHFastBallPoly.mulList D (powerList D a n) a
noncomputable def evaluate (D:Nat) (inputs:List Ball) : Expr→List Ball
 |.zero=>[zero]
 |.one=>[integer D 1]
 |.imag=>[rotate (integer D 1) 3]
 |.variable=>[zero,integer D 1]
 |.input i=>[RHFastBallPoly.entry inputs i]
 |.rational p q=>[rational D p (q+1)]
 |.add a b=>RHFastBallPoly.addList (evaluate D inputs a) (evaluate D inputs b)
 |.mul a b=>RHFastBallPoly.mulList D (evaluate D inputs a) (evaluate D inputs b)
 |.divide a n=>RHFastBallPoly.divideList (evaluate D inputs a) (n+1)
 |.power a n=>powerList D (evaluate D inputs a) n
noncomputable def sum (es:List Expr) : Expr:=es.foldl Expr.add .zero
noncomputable def neg (a:Expr) : Expr:=.mul (.rational (-1) 0) a
noncomputable def sub (a b:Expr) : Expr:=.add a (neg b)
-- Input order: center, inverse center, log center, pi, carrier frequency.
noncomputable def increment : Expr:=
 let u:=Expr.mul (.mul (.rational 128 0) .imag) .variable
 let s:=Expr.mul u (.input 1)
 let l:=sum ((List.range 6).map (fun r=>Expr.mul
   (.rational ((-1:Int)^(r+2)) r) (.power s (r+1))))
 let geometric:=sum ((List.range 7).map (fun r=>Expr.power (neg s) r))
 Expr.add
   (.add (.mul u (sub (.input 2) .one))
     (.mul (.add (sub (.input 0) (.rational 1 1)) u) l))
   (.add (.mul (.divide (.input 1) 11) (sub geometric .one))
     (.mul (sub (.mul (.rational 64 0) (.input 3))
       (.mul (.mul (.rational 256 0) .imag) (.input 4))) .variable))
noncomputable def approximation : Expr:=
 sum ((List.range 5).map (fun r=>Expr.divide (.power increment r) (r.factorial-1)))
end RHFastPolynomialCircuit
noncomputable def TaoFivePrimes_RHFastPolynomialCircuit : Nat:=28


