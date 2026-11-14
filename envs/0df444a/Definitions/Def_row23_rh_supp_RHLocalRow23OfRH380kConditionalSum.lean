-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalRow23OfRH380kConditionalSum
-- name    : row23_rh_supp_RHLocalRow23OfRH380kConditionalSum
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:34:05.53727+00:00
-- url     : https://prove2.me/theorems/30f2956f-8eab-4c6d-858e-2363a5865608
-- title:
--   Row 23 RH support: RHLocalRow23OfRH380kConditionalSum
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kRow
import Definitions.Def_row23_rh_supp_RHLocalMoment380kLogs
import Definitions.Def_row23_rh_supp_RHLocalMass8Row23_380k
import Definitions.Def_row23_rh_supp_RHLocalRow23TrivialStripFinal380k
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace DusartLegendreSmoothing.Moment380k
open DusartSmoothing

theorem row23_of_RH380k_and_low_sum
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hRH : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ (380000:ℝ) → ρ.val.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ) * x := by
  have hM : derivativeMass p23.m (p23.δ:ℝ) ≤ (p23.M:ℝ) := by
    simpa [p23] using DusartLegendreSmoothing.mass8_for_row23_380k
  have hS : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ (lowHeight:ℝ)) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (d23.S:ℝ) := by
    simpa [lowHeight,d23] using hFine
  have h := row_of_RH_and_low_sum p23 d23 p23_arithmetic d23_checks d23_logBounds
    (by norm_num [p23]) hM (by simpa [highHeight] using hRH) hS
    p23_trivial_strip_final x (by simpa [p23] using hx)
  convert h using 1 <;> norm_num [p23]
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_RH380k_and_low_sum


