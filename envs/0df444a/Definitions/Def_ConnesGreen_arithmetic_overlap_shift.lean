-- Prove2me | Definitions.Def_ConnesGreen_arithmetic_overlap_shift
-- name    : ConnesGreen_arithmetic_overlap_shift
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T03:39:49.906922+00:00
-- url     : https://prove2.me/theorems/a0b60d9d-77e7-4ae6-9dee-f227935c89ff
-- title:
--   Original arithmetic shift with individual prime overlaps
-- statement:
--   For a real support cap $R$, let $A_R$ be the original finite set of prime powers with $\log n<2R$, $P_R=\sum_{n\in A_R}\Lambda(n)/\sqrt n$, and $\gamma(r)=\Re\psi(1/4+ir/2)-\log\pi$. Define $$C_R=\sum_{n\in A_R}\frac{4\Lambda(n)}{\sqrt n}\max(2R-\log n,0),\qquad K_R=4\max(-\gamma(0),0)+\min(16R^2e^R,8(\sinh R-R))+C_R.$$ Also recover the unchanged preceding shift $K_R^{\mathrm{old}}=4\max(-\gamma(0),0)+16R^2e^R+8RP_R$. These are auxiliary arithmetic scalar costs in the ORIGINAL physical test energy. No carrier, actor, actual-zero index, selected correction or admissible test is replaced.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/OverlapShiftCertificates.lean and the unchanged preceding arithmeticEnergyShift in ArithmeticRegularization.lean; compiling local source abb28946186c33032e4c9aef21f4ec7b71236b51

import Definitions.Def_ConnesGreen_prime_overlap_loss
import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability
namespace ConnesGreen
noncomputable def arithmeticEnergyShift (R : ℝ) : ℝ :=
  4 * max (-Zeta23.EF.gammaBracket 0) 0 +
    16 * R ^ 2 * Real.exp R + 8 * R * activePrimeWeight R
def primeOverlapEnergyCost (R : ℝ) : ℝ :=
  ∑ n ∈ activePrimePowerFinset R,
    4 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * max (2*R-Real.log n) 0
def arithmeticOverlapShift (R : ℝ) : ℝ :=
  4 * max (-Zeta23.EF.gammaBracket 0) 0 +
    min (16*R^2*Real.exp R) (8*(Real.sinh R-R)) + primeOverlapEnergyCost R
end ConnesGreen


