-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastComplexBallInterface
-- name    : TaoFivePrimes_RHFastComplexBallInterface
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T09:40:03.646981+00:00
-- url     : https://prove2.me/theorems/b92e300e-6797-4c1e-ba47-de6421e4a123
-- title:
--   Soundness interface for complex error-ball arithmetic
-- statement:
--   A propositional interface for analytic soundness of twelve ordinary integer complex-ball operations. The structure merely states the required preservation of containment; a separate ordinary theorem must construct it for every positive fixed-point scale.
-- source:
--   Complex error-ball arithmetic for the Gaussian/Hermite center method; Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
namespace RHFastBallInterface
open RHFastBallArithmetic RHFastBallSemantics
structure Sound (D:Nat) : Prop where
 self_mem : ∀a:Ball,encloses D a (value D a)
 integer_mem : ∀n:Int,encloses D (integer D n) (n:ℂ)
 rational_mem : ∀(p:Int)(q:Nat),0<q → encloses D (rational D p q) ((p:ℂ)/(q:ℂ))
 add_mem : ∀(a b:Ball)(x y:ℂ),encloses D a x → encloses D b y → encloses D (add a b) (x+y)
 neg_mem : ∀(a:Ball)(x:ℂ),encloses D a x → encloses D (neg a) (-x)
 sub_mem : ∀(a b:Ball)(x y:ℂ),encloses D a x → encloses D b y → encloses D (sub a b) (x-y)
 mul_mem : ∀(a b:Ball)(x y:ℂ),encloses D a x → encloses D b y → encloses D (mul D a b) (x*y)
 divide_mem : ∀(a:Ball)(x:ℂ)(n:Nat),0<n → encloses D a x → encloses D (divide a n) (x/(n:ℂ))
 scale_mem : ∀(a:Ball)(x:ℂ)(n:Int),encloses D a x → encloses D (scale a n) ((n:ℂ)*x)
 rotate_mem : ∀(a:Ball)(x:ℂ)(n:Nat),encloses D a x → encloses D (rotate a n) ((-Complex.I)^(n%4)*x)
 inflate_mem : ∀(a:Ball)(x:ℂ)(n:Nat),encloses D a x → encloses D (inflate a n) x
 power_mem : ∀(a:Ball)(x:ℂ)(n:Nat),encloses D a x → encloses D (power D a n) (x^n)
end RHFastBallInterface
noncomputable def TaoFivePrimes_RHFastComplexBallInterface : Nat := 12


