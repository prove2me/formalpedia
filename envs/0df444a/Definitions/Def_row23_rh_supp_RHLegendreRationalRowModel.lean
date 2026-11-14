-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRationalRowModel
-- name    : row23_rh_supp_RHLegendreRationalRowModel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:56:30.034707+00:00
-- url     : https://prove2.me/theorems/2aefe17e-3014-4205-970b-4e64f8c402fe
-- title:
--   Rational row parameters for the Dusart Table 1 reduction
-- statement:
--   This supporting Lean module defines exact rational parameters used in the finite-range Chebyshev psi estimates. It is a component of the locally checked row-23 proof reduction and makes no independent claim that the row estimate has been proved.
-- source:
--   Supporting rational framework for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Algebra.Order.Field.Rat
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace DusartLegendreSmoothing.RationalRows
structure Parameters where
  b : ℕ
  m : ℕ
  T : ℕ
  δ : ℚ
  M : ℚ
  B₁ : ℚ
  B₂ : ℚ
  B₃ : ℚ
  ε : ℚ
  q : ℚ
def arithmeticChecks (p : Parameters) : Prop :=
  1 ≤ p.q ∧ 0 < p.δ ∧ p.δ ≤ 1 ∧
  p.q^8*(1+p.δ) ≤ (27182818283/10^10:ℚ)^p.b ∧
  p.δ/2+((1+p.δ/2)*p.B₁+p.M/p.δ^p.m*p.B₂)/p.q^4+
    (p.M/p.δ^p.m*p.B₃)/p.q+2/p.q^8+
    (4096/3+32*(p.m:ℚ)/p.δ)/p.q^12 ≤ p.ε
end DusartLegendreSmoothing.RationalRows


