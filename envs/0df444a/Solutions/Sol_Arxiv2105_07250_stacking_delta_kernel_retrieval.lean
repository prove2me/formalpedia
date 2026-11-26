-- Prove2me | solution 1 for Arxiv2105_07250.stacking_delta_kernel_retrieval
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:56:12.627661+00:00
-- url     : https://prove2.me/submissions/a0a64d4e-42f8-42d5-addc-ad9a2c5f1cc9

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S76SK

lemma diag_emb : MeasurableEmbedding (fun x : ℝ => (x, x)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := Prod.fst)
  · exact measurable_id.prodMk measurable_id
  · have : Set.range (fun x : ℝ => (x, x)) = {p : ℝ × ℝ | p.1 = p.2} := by
      ext p; constructor
      · rintro ⟨x, rfl⟩; rfl
      · intro h; exact ⟨p.1, by ext <;> simp [h.symm] <;> exact h⟩
    rw [this]
    exact measurableSet_eq_fun measurable_fst measurable_snd
  · exact measurable_fst
  · intro x; rfl

end S76SK

open Arxiv2105_07250 S76SK in
theorem solution (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (GA GB : ℝ → ℂ)
    (hint : Integrable (fun x' : ℝ => starRingEnd ℂ (GA x') * GB x')) (s : ℂ) (C : ℝ) (hC : 0 < C) :
    stackedRetrievalOfKernel ρ c (ENNReal.ofReal C • deltaKernel s) GA GB =
        ((C * Complex.normSq s : ℝ) : ℂ) * directRetrieval ρ c GA GB ∧
      (s ≠ 0 → Complex.arg (stackedRetrievalOfKernel ρ c (ENNReal.ofReal C • deltaKernel s) GA GB) =
        Complex.arg (directRetrieval ρ c GA GB)) := by
  have h1 : stackedRetrievalOfKernel ρ c (ENNReal.ofReal C • deltaKernel s) GA GB =
      ((C * Complex.normSq s : ℝ) : ℂ) * directRetrieval ρ c GA GB := by
    unfold stackedRetrievalOfKernel deltaKernel directRetrieval
    rw [integral_smul_measure, integral_smul_measure, diag_emb.integral_map]
    rw [ENNReal.toReal_ofReal hC.le, ENNReal.toReal_ofReal (Complex.normSq_nonneg s)]
    simp only [Complex.real_smul]
    push_cast
    ring
  refine ⟨h1, fun hs => ?_⟩
  rw [h1]
  have : 0 < C * Complex.normSq s := mul_pos hC (Complex.normSq_pos.2 hs)
  exact Complex.arg_real_mul _ this
