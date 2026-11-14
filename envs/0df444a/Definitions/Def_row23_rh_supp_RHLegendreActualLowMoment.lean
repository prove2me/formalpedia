-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreActualLowMoment
-- name    : row23_rh_supp_RHLegendreActualLowMoment
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:11:35.647748+00:00
-- url     : https://prove2.me/theorems/80f1ae3d-0f8a-42ca-a356-5884e5fa2154
-- title:
--   Row 23 RH support: RHLegendreActualLowMoment
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreActualHighMoments
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing
noncomputable def positiveLowMomentBound (a b S : ℝ) : ℝ :=
  S+2*(9*Real.log (a+5)+79)/a+zeroCountSlope a*
    ((Real.log (b/(2*Real.pi)))^2-(Real.log (a/(2*Real.pi)))^2)/2
 theorem finite_positive_reciprocal_bound (a b S : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b)
    (hS : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ a) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ S)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ b) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ positiveLowMomentBound a b S := by
  classical
  let L := Z.filter (fun ρ => ρ.im ≤ a)
  let U := Z.filter (fun ρ => ¬ρ.im ≤ a)
  have hL : (∑ ρ ∈ L, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ S := by
    apply hS
    intro ρ hρ
    obtain ⟨hz,ht⟩ := Finset.mem_filter.mp hρ
    exact ⟨(hZ ρ hz).1,(hZ ρ hz).2.1,ht⟩
  have hU := finite_positive_zero_power_density_bound 0 U
    (fun ρ hρ => ⟨(hZ ρ (Finset.mem_filter.mp hρ).1).1,(hZ ρ (Finset.mem_filter.mp hρ).1).2.1⟩)
    a b ha hab (fun ρ hρ => ⟨lt_of_not_ge (Finset.mem_filter.mp hρ).2,
      (hZ ρ (Finset.mem_filter.mp hρ).1).2.2⟩)
  norm_num only [Nat.zero_add,pow_one] at hU
  rw [integral_log_div_self a b (by linarith) hab] at hU
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) =
      (∑ ρ ∈ L, (RvM.zeroMult ρ:ℝ)*(1/ρ.im))+
      (∑ ρ ∈ U, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) :=
    (Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.im ≤ a)
      (fun ρ => (RvM.zeroMult ρ:ℝ)*(1/ρ.im))).symm
  rw [he]
  exact (add_le_add hL hU).trans_eq (by unfold positiveLowMomentBound; ring)
 theorem actual_low_moment (a b S : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b)
    (hS : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ a) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ S) :
    Summable (heightMoment (fun ρ : NontrivialZetaZero => ρ.val)
      (fun ρ => RvM.zeroMult ρ.val) 1 (fun t => t ≤ b)) ∧
    (∑' ρ : NontrivialZetaZero, heightMoment (fun τ : NontrivialZetaZero => τ.val)
      (fun τ => RvM.zeroMult τ.val) 1 (fun t => t ≤ b) ρ) ≤
      2*positiveLowMomentBound a b S := by
  apply actual_height_moment_of_finite_bound
  intro Z hZ
  exact finite_absolute_moment_of_positive_bound 1 (fun t => t ≤ b)
    (positiveLowMomentBound a b S)
    (fun W hW => by
      simpa only [pow_one] using finite_positive_reciprocal_bound a b S ha hab hS W hW)
    Z (fun ρ hρ => (hZ ρ hρ).1) (fun ρ hρ => (hZ ρ hρ).2)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.actual_low_moment


