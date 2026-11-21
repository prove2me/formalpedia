-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterTruncate_F000
-- name    : LevyStochCalc_Poisson_CharacterTruncate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:48.860403+00:00
-- url     : https://prove2.me/theorems/56df7b0f-5428-49ce-a235-8664c03a4a50
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterTruncate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterTruncate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterOrthogonal_F000
import Definitions.Def_SourceProof_89ebd52e5fe73ccd194d85c2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of the window counts up to an intermediate time

Cutting a finite family of window sets at a time `t ≤ T` keeps every hypothesis of the jump chain
rule at the horizon `T`, its window sum is the exponent of the character of the counts up to `t`,
and on `(0, t]` its simple mark and its strict count agree with those of the uncut family. So the
chain rule at the fixed horizon `T` already describes the character at every intermediate time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Truncate

/-- The family of time–mark sets cut at time `t`. -/
def truncFam (Bfam : ι → Set (ℝ × E)) (t : ℝ) : ι → Set (ℝ × E) :=
  fun j => Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [Fintype ι] in
theorem measurableSet_truncFam {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (t : ℝ) (j : ι) : MeasurableSet (truncFam Bfam t j) :=
  (hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ)
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [Fintype ι] in
theorem truncFam_subset {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (t : ℝ) (j : ι) :
    truncFam Bfam t j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
  Set.inter_subset_left.trans (hBsub j)
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [Fintype ι] in
theorem truncFam_inter_Ioc {Bfam : ι → Set (ℝ × E)} {t T : ℝ} (htT : t ≤ T) (j : ι) :
    truncFam Bfam t j ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ = Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ := by
  ext p
  simp only [truncFam, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
  constructor
  · rintro ⟨⟨hB, h0, ht⟩, -⟩
    exact ⟨hB, h0, ht⟩
  · rintro ⟨hB, h0, ht⟩
    exact ⟨⟨hB, h0, ht⟩, h0, ht.trans htT⟩
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [Fintype ι] in
theorem truncFam_inter_Ioo {Bfam : ι → Set (ℝ × E)} {s t : ℝ} (hst : s ≤ t) (j : ι) :
    truncFam Bfam t j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ = Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ := by
  ext p
  simp only [truncFam, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo, Set.mem_univ,
    and_true]
  constructor
  · rintro ⟨⟨hB, -, -⟩, h0, hs⟩
    exact ⟨hB, h0, hs⟩
  · rintro ⟨hB, h0, hs⟩
    exact ⟨⟨hB, h0, hs.le.trans hst⟩, h0, hs⟩
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [Fintype ι] in
theorem iUnion_truncFam (Bfam : ι → Set (ℝ × E)) (t : ℝ) :
    ⋃ j, truncFam Bfam t j = (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ := by
  simp only [truncFam, Set.iUnion_inter]
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- On `(0, t]` the simple mark of the cut family is that of the family. -/
theorem simpleMark_truncFam (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {t : ℝ} {p : ℝ × E}
    (hp : p.1 ∈ Set.Ioc (0 : ℝ) t) :
    simpleMark w (truncFam Bfam t) p = simpleMark w Bfam p := by
  have h0 := hp.1
  have h1 := hp.2
  simp only [simpleMark, truncFam]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : p ∈ Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ ↔ p ∈ Bfam j := by
    simp [Set.mem_Ioc, h0, h1]
  by_cases hB : p ∈ Bfam j
  · rw [Set.indicator_of_mem (hmem.mpr hB), Set.indicator_of_mem hB]
  · rw [Set.indicator_of_notMem (fun h => hB (hmem.mp h)), Set.indicator_of_notMem hB]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- On `(0, t]` the strict count of the cut family is the strict-past count of the family. -/
theorem predStrict_truncFam (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    {A : Set E} {T s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htT : t ≤ T) {e : E} (he : e ∈ A)
    (ω : Ω) :
    predStrict N w (truncFam Bfam t) A T ω s e
      = ∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ)).toReal := by
  rw [predStrict_eq N w _ hs (hst.trans htT) he ω]
  simp_rw [truncFam_inter_Ioo hst]
/-- The character of the counts of a finite family up to time `t`. -/
noncomputable def charAt (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (t : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I *
    ((∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ)).toReal : ℝ) : ℂ))
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The window sum of the cut family at the horizon is the exponent of the character at `t`. -/
theorem ae_windowSum_truncFam (N : PoissonRandomMeasure P ν) {A : Set E} (hAν : ν A ≠ ⊤) {T : ℝ}
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {t : ℝ} (htT : t ≤ T) :
    ∀ᵐ ω ∂P, windowSum N (⋃ j, truncFam Bfam t j) (simpleMark w (truncFam Bfam t)) T ω
      = ∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ)).toReal := by
  filter_upwards [ae_windowSum_simple N hAν w (measurableSet_truncFam hBm t)
    (truncFam_subset hBsub t)] with ω hω
  rw [(hω T).1]
  simp_rw [truncFam_inter_Ioc htT]
/-- **The chain rule at an intermediate time.** The character of the counts up to `t ≤ T`, minus
one, is the compensated integral of the cut family's integrand at the horizon `T` plus its
compensator. -/
theorem ae_charAt_sub_one_eq_integral (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hT : 0 < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {t : ℝ} (htT : t ≤ T) :
    ∀ᵐ ω ∂P, charAt N w Bfam t ω - 1
      = ((charReIntegrand N hℱ w (measurableSet_truncFam hBm t) hA hAν
            (truncFam_subset hBsub t)).integral N hℱ ω : ℂ)
        + ((charImIntegrand N hℱ w (measurableSet_truncFam hBm t) hA hAν
            (truncFam_subset hBsub t)).integral N hℱ ω : ℂ) * Complex.I
        + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2 ∂(referenceIntensity ν) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_89ebd52e5fe73ccd194d85c2 N hℱ w (measurableSet_truncFam hBm t) hA hAν hT
      (truncFam_subset hBsub t), ae_windowSum_truncFam N hAν w hBm hBsub htT,
    charReIntegrand_integral N hℱ w (measurableSet_truncFam hBm t) hA hAν
      (truncFam_subset hBsub t),
    charImIntegrand_integral N hℱ w (measurableSet_truncFam hBm t) hA hAν
      (truncFam_subset hBsub t)] with ω h1 h2 h3 h4
  rw [charAt, ← h2, h3, h4]
  exact h1
end Truncate

end LevyStochCalc.Poisson


