-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kArithmetic
-- name    : row23_rh_supp_RHLocalMoment380kArithmetic
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:25.211201+00:00
-- url     : https://prove2.me/theorems/60059ca1-b127-448c-90c8-9aeeb285aff2
-- title:
--   Row 23 RH support: RHLocalMoment380kArithmetic
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kModel
set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace DusartLegendreSmoothing.Moment380k
open RationalRows
def p23 : Parameters := {
  b := 23, m := 8, T := 92500, δ := 156/1000000, M := 1845000000,
  B₁ := 15329/1000, B₂ := 74/10^42, B₃ := 104/10^47, ε := 2431/10000000, q := 709/40 }
def d23 : Data := {
  S := 2028657/1000000, L0 := 253/50, U0 := 127/25, V0 := 7/1,
  LT := 95969/10000, UT := 95974/10000, VT := 114352/10000,
  LH := 110099/10000, UH := 110103/10000, VH := 128481/10000 }
theorem p23_arithmetic : arithmeticChecks p23 := by
  unfold arithmeticChecks p23
  decide +kernel
theorem d23_checks : checks p23 d23 := by
  unfold checks lowUpper bandUpper tailUpper slopeUpper slopeLower primitive
    lowHeight highHeight piLower piUpper p23 d23
  decide +kernel
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.p23_arithmetic
#print axioms DusartLegendreSmoothing.Moment380k.d23_checks


