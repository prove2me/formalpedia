-- Prove2me | solution 1 for AdaptiveBaseStock.Regret.demand_sum_tail
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:03:27.457998+00:00
-- url     : https://prove2.me/submissions/35e3b303-1841-4140-978c-709ed9bc50b2

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

open MeasureTheory ProbabilityTheory AdaptiveBaseStock.Regret

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (η : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    P.real {ω | ∑ ℓ ∈ Finset.range t, D ℓ ω ≤ η} ≤ demandCdf P (D 0) η ^ t := by
  have hsub : {ω | ∑ ℓ ∈ Finset.range t, D ℓ ω ≤ η} ⊆
      ⋂ ℓ ∈ Finset.range t, D ℓ ⁻¹' Set.Iic η := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
    intro ℓ hℓ
    have := Finset.single_le_sum (f := fun l => D l ω) (fun l _ => hD.nonneg l ω) hℓ
    exact this.trans hω
  have hind := hD.indep.measure_inter_preimage_eq_mul (S := Finset.range t)
    (sets := fun _ => Set.Iic η) (fun _ _ => measurableSet_Iic)
  have hF : ∀ ℓ, P (D ℓ ⁻¹' Set.Iic η) = P (D 0 ⁻¹' Set.Iic η) :=
    fun ℓ => (hD.identDistrib ℓ).measure_mem_eq measurableSet_Iic
  calc P.real {ω | ∑ ℓ ∈ Finset.range t, D ℓ ω ≤ η}
      ≤ P.real (⋂ ℓ ∈ Finset.range t, D ℓ ⁻¹' Set.Iic η) := measureReal_mono hsub
    _ = demandCdf P (D 0) η ^ t := by
      rw [measureReal_def, hind]
      simp only [hF, Finset.prod_const, Finset.card_range, ENNReal.toReal_pow]
      rfl
