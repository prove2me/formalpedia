-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastComplexBallArithmetic
-- name    : TaoFivePrimes_RHFastComplexBallArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T09:26:26.867494+00:00
-- url     : https://prove2.me/theorems/38771f71-a362-491c-93ba-b17d6375293c
-- title:
--   Integer arithmetic for complex error balls
-- statement:
--   Transparent integer arithmetic on complex error balls, with exact addition and outward error-radius formulas for fixed-point multiplication and division. All operations are ordinary Lean definitions. Their analytic containment properties require separate soundness proofs; no numerical enclosure or RH window is asserted.
-- source:
--   Fixed-point complex ball arithmetic. Application: Platt DOI10.1090/mcom/3198 and the Gaussian/Hermite center route. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Init
namespace RHFastBallArithmetic
structure Ball where
 re : Int
 im : Int
 radius : Nat
 deriving DecidableEq, Repr
noncomputable def zero : Ball := ⟨0,0,0⟩
noncomputable def magnitude (a:Ball) : Nat := a.re.natAbs+a.im.natAbs
noncomputable def integer (D:Nat) (n:Int) : Ball := ⟨n*(D:Int),0,0⟩
noncomputable def rational (D:Nat) (p:Int) (q:Nat) : Ball := ⟨p*(D:Int)/(q:Int),0,1⟩
noncomputable def add (a b:Ball) : Ball := ⟨a.re+b.re,a.im+b.im,a.radius+b.radius⟩
noncomputable def neg (a:Ball) : Ball := ⟨-a.re,-a.im,a.radius⟩
noncomputable def sub (a b:Ball) : Ball := add a (neg b)
noncomputable def mul (D:Nat) (a b:Ball) : Ball :=
 ⟨(a.re*b.re-a.im*b.im)/(D:Int),(a.re*b.im+a.im*b.re)/(D:Int),
  3+(magnitude a*b.radius+magnitude b*a.radius+a.radius*b.radius)/D⟩
noncomputable def divide (a:Ball) (n:Nat) : Ball :=
 ⟨a.re/(n:Int),a.im/(n:Int),3+a.radius/n⟩
noncomputable def scale (a:Ball) (n:Int) : Ball :=
 ⟨n*a.re,n*a.im,n.natAbs*a.radius⟩
noncomputable def rotate (a:Ball) (n:Nat) : Ball :=
 if n%4=0 then a else if n%4=1 then ⟨a.im,-a.re,a.radius⟩
 else if n%4=2 then ⟨-a.re,-a.im,a.radius⟩ else ⟨-a.im,a.re,a.radius⟩
noncomputable def inflate (a:Ball) (n:Nat) : Ball := ⟨a.re,a.im,a.radius+n⟩
noncomputable def power (D:Nat) (a:Ball) : Nat→Ball
 |0=>integer D 1
 |n+1=>mul D (power D a n) a
end RHFastBallArithmetic
noncomputable def TaoFivePrimes_RHFastComplexBallArithmetic : Nat := 128


