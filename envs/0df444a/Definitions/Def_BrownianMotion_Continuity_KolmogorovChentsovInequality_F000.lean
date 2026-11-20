-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F000
-- name    : BrownianMotion_Continuity_KolmogorovChentsovInequality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:22:38.799454+00:00
-- url     : https://prove2.me/theorems/bf0fa047-eb80-4bcb-84ea-c49e3c9b15b0
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsovInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsovInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F001
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003
import Mathlib.Data.Set.FiniteExhaustion

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

protected theorem Asymptotics.IsEquivalent.rpow_of_nonneg {α : Type*}
    {t u : α → ℝ} (hu : 0 ≤ u) {l : Filter α} (h : t ~[l] u) {r : ℝ} :
    t ^ r ~[l] u ^ r := by
  obtain ⟨φ, hφ, htφu⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x ↦ x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    refine Tendsto.comp ?_ hφ
    exact ContinuousAt.tendsto (Real.continuousAt_rpow_const _ _ (by left; norm_num))
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x ↦ φ x ^ r * u x ^ r
  filter_upwards [Filter.Tendsto.eventually_const_lt (zero_lt_one) hφ, htφu] with x hφ_pos htu'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hu x), htu']
lemma Set.FiniteExhaustion.subset {α : Type*} {s : Set α} (K : FiniteExhaustion s) (n : ℕ) :
    K n ⊆ s := by
  simp_rw [← K.iUnion_eq]
  exact Set.subset_iUnion K n
set_option backward.isDefEq.respectTransparency false in
lemma measure_add_ge_le_add_measure_ge {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} {x u : ℝ≥0∞} (hu : u ≤ x) :
    P {ω | x ≤ f ω + g ω} ≤ P {ω | u ≤ f ω} + P {ω | x - u ≤ g ω} := by
  calc P {ω | x ≤ f ω + g ω}
  _ = P {ω | u + (x - u) ≤ f ω + g ω} := by
    congr with ω
    congr!
    exact (add_tsub_cancel_of_le hu).symm
  _ ≤ P ({ω | u ≤ f ω} ∪ {ω | (x - u) ≤ g ω}) := by
    refine measure_mono fun ω ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_union]
    contrapose!
    rintro ⟨h₁, h₂⟩
    gcongr
  _ ≤ P {ω | u ≤ f ω} + P {ω | x - u ≤ g ω} := measure_union_le _ _
lemma measure_add_ge_le_add_measure_ge_half {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} {x : ℝ≥0∞} :
    P {ω | x ≤ f ω + g ω} ≤ P {ω | x / 2 ≤ f ω} + P {ω | x / 2 ≤ g ω} := by
  by_cases hx : x = ∞
  · simp only [hx, top_le_iff, ENNReal.add_eq_top]
    rw [ENNReal.top_div_of_ne_top (by finiteness)]
    simp only [top_le_iff]
    exact measure_union_le {ω | f ω = ∞} {ω | g ω = ∞}
  convert measure_add_ge_le_add_measure_ge ENNReal.half_le_self using 2
  rw [ENNReal.sub_half hx]
end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

end PseudoEMetricSpace

end ProbabilityTheory


