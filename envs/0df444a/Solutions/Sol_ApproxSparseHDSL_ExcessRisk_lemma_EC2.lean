-- Prove2me | solution 1 for ApproxSparseHDSL.ExcessRisk.lemma_EC2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:34:09.216457+00:00
-- url     : https://prove2.me/submissions/fe0e150a-0b80-404f-98ff-5ca6a084d3a9

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace Aux_EC2W31
open ApproxSparseHDSL.ExcessRisk

lemma mcp_bounds (a lam θ : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hθ : 0 ≤ θ) :
    0 ≤ mcp a lam θ ∧ mcp a lam θ ≤ lam * θ := by
  unfold mcp
  have hc : Continuous fun t : ℝ => max (a * lam - t) 0 / a := by fun_prop
  constructor
  · apply intervalIntegral.integral_nonneg hθ
    intro u _
    exact div_nonneg (le_max_right _ _) ha.le
  · have h := intervalIntegral.integral_mono_on (μ := volume) hθ (hc.intervalIntegrable 0 θ)
      (continuous_const.intervalIntegrable 0 θ) (g := fun _ => lam) (fun u hu => by
        rw [div_le_iff₀ ha]
        exact max_le (by nlinarith [hu.1]) (by positivity))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    linarith [mul_comm θ lam]

end Aux_EC2W31

open ApproxSparseHDSL.ExcessRisk in
theorem solution {E : Type} {p n : ℕ} (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E)
    (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) (betaL1 betaStar : Fin p → ℝ)
    (hopt : ∀ β : Fin p → ℝ, lassoObj lam L z betaL1 ≤ lassoObj lam L z β) :
    regRisk a lam L z betaL1 ≤ regRisk a lam L z betaStar + lam * l1 betaStar := by
  have h := hopt betaStar
  unfold lassoObj at h
  unfold regRisk
  have h1 : ∑ j, mcp a lam |betaL1 j| ≤ lam * l1 betaL1 := by
    unfold l1
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      (Aux_EC2W31.mcp_bounds a lam _ ha hlam (abs_nonneg _)).2
  have h2 : 0 ≤ ∑ j, mcp a lam |betaStar j| :=
    Finset.sum_nonneg fun j _ => (Aux_EC2W31.mcp_bounds a lam _ ha hlam (abs_nonneg _)).1
  linarith
