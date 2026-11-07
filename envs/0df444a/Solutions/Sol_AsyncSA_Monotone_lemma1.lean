-- Prove2me | solution 1 for AsyncSA.Monotone.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:42:35.164814+00:00
-- url     : https://prove2.me/submissions/af1ed5cc-836a-447e-b0d9-feea84bc0aab

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model
import Theorems.Thm_AsyncSA_Contraction_lemma1

open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (α w B W : ℕ → Ω → ℝ) (C : ℝ)
    (hα_meas : ∀ t, Measurable[𝓕 t] (α t))
    (hw_meas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hB_meas : ∀ t, Measurable[𝓕 t] (B t))
    (ha : ∀ t, AsyncSA.Monotone.CondMeanZero (𝓕 t) P (w t))
    (hb : ∀ t, AsyncSA.Monotone.CondSqLe (𝓕 t) P (w t) (B t))
    (hc : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ᵐ ω ∂P, Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (he : ∀ᵐ ω ∂P, ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K)
    (hW : ∀ t ω, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t => W t ω) atTop (𝓝 0) := by
  refine AsyncSA.Contraction.lemma1 P 𝓕 α w (fun t ω => max (B t ω) 0) W C hα_meas hw_meas
    (fun t => (hB_meas t).max measurable_const) ha ?_ hc hd he ?_ hW
  · intro t
    refine ⟨Filter.Eventually.of_forall fun ω => le_max_right _ _, ?_⟩
    intro S hS
    have h := hb t S hS
    have heq : (fun ω => ENNReal.ofReal (max (B t ω) 0)) = fun ω => ENNReal.ofReal (B t ω) := by
      funext ω
      rcases le_total (B t ω) 0 with h0 | h0
      · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
      · rw [max_eq_left h0]
    simp only [heq]
    exact h
  · filter_upwards [hB_bdd] with ω ⟨K, hK⟩
    refine ⟨K, fun t => ?_⟩
    have := hK t
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (le_abs_self _) this) (le_trans (abs_nonneg _) this)
