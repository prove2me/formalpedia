-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastRoundedLogArithmetic
-- name    : TaoFivePrimes_RHFastRoundedLogArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T21:30:35.746979+00:00
-- url     : https://prove2.me/theorems/523efbb8-37ef-43d3-b4a8-6b9aad3ddf2e
-- title:
--   Logarithm polynomial evaluation with bounded intermediate integers
-- statement:
--   Alternative exact integer algorithm for the same fixed40-term logarithm polynomial. Each Horner step divides before the next multiplication. Algorithms only; comparison accuracy is proved separately. No analytic logarithm, gamma or RH assertion.
-- source:
--   Platt Fourier construction, DOI10.1090/mcom/3198. The arithmetic comparison is a new ordinary Lean induction over rounded Horner evaluation. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
namespace RHFastRoundedLogArithmetic
noncomputable def evaluate : List Nat → Nat → Nat → Nat → Nat → Nat
  | [],_,_,_,_ => 0
  | c::cs,x,y,F,D => c*D/F+x*evaluate cs x y F D/y
noncomputable def rounded (p q D : Nat) : Nat :=
  2*p*evaluate RHFastKernelLogData.coefficients (p^2) (q^2) RHFastKernelLogData.F D/q
end RHFastRoundedLogArithmetic
noncomputable def TaoFivePrimes_RHFastRoundedLogArithmetic : Nat := 40


