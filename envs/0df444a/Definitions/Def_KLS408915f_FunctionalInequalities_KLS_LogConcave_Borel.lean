-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:25:32.33416+00:00
-- url     : https://prove2.me/theorems/e430370f-f525-49e5-adf2-36e354f5358c
-- title:
--   Borel log-concavity and compact inner measure
-- statement:
--   `FunctionalInequalities.KLS.innerMeasure` assigns to an arbitrary set S the supremum in $[0,\infty]$ of the measures of its compact subsets, while `BorelLogConcave` uses this inner measure on the affine combination of measurable sets. For finite-dimensional real normed Borel spaces, `LogConcave.borel_iff` proves that compact-set log-concavity is equivalent to this Borel formulation. The bundle also records monotonicity and compact-subset bounds for `innerMeasure`, compactness and monotonicity of affine combinations, and the positive-power supremum identity `rpow_iSup`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Borel.lean#L25-L126 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Borel`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Inner measure of an arbitrary set, using compact subsets, including the empty set.
No outer-measure evaluation of the arbitrary set occurs in this definition. -/
def innerMeasure (μ : Measure E) (S : Set E) : ENNReal :=
  ⨆ (K : Set E) (_ : K ⊆ S) (_ : IsCompact K), μ K
/-- Bobkov's Borel-set formulation, with inner measure on the Minkowski combination.
The exponent range excludes both endpoints, exactly as in the compact-set predicate. -/
def BorelLogConcave (μ : ProbabilityMeasure E) : Prop :=
  ∀ (B₀ B₁ : Set E), MeasurableSet B₀ → MeasurableSet B₁ →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ : Measure E) B₀ ^ t * (μ : Measure E) B₁ ^ (1 - t) ≤
        innerMeasure (μ : Measure E)
          {z | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y}
section InnerMeasureProperties
omit [NormedSpace ℝ E] [BorelSpace E]
/-- Inner measure is monotone in the set. -/
theorem innerMeasure_mono (μ : Measure E) {S T : Set E} (h : S ⊆ T) :
    innerMeasure μ S ≤ innerMeasure μ T := by
  unfold innerMeasure
  exact iSup₂_le fun K hK ↦ iSup_le fun hc ↦ le_iSup₂_of_le K (hK.trans h) (le_iSup_of_le hc le_rfl)
/-- Inner measure never exceeds the outer-measure value of the set. -/
theorem innerMeasure_le (μ : Measure E) (S : Set E) : innerMeasure μ S ≤ μ S := by
  unfold innerMeasure
  exact iSup₂_le fun K hK ↦ iSup_le fun _ ↦ measure_mono hK
/-- Every compact subset gives a lower bound for the inner measure. -/
theorem le_innerMeasure_of_isCompact (μ : Measure E) {K S : Set E} (hK : IsCompact K)
    (hKS : K ⊆ S) : μ K ≤ innerMeasure μ S :=
  le_iSup₂_of_le K hKS (le_iSup_of_le hK le_rfl)
end InnerMeasureProperties
section CompactCombinations
omit [MeasurableSpace E] [BorelSpace E]
/-- The Minkowski combination of two compact sets is compact: it is the continuous image of
the compact product. Finite dimension is not needed for this step. -/
theorem isCompact_combination {K₀ K₁ : Set E} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (t : ℝ) : IsCompact {z : E | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} := by
  have he : {z : E | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} =
      (fun p : E × E ↦ t • p.1 + (1 - t) • p.2) '' (K₀ ×ˢ K₁) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  rw [he]
  exact (hK₀.prod hK₁).image (by fun_prop)
/-- The Minkowski combination is monotone in both sets. -/
theorem combination_mono {A₀ A₁ B₀ B₁ : Set E} (h₀ : A₀ ⊆ B₀) (h₁ : A₁ ⊆ B₁) (t : ℝ) :
    {z : E | ∃ x ∈ A₀, ∃ y ∈ A₁, z = t • x + (1 - t) • y} ⊆
      {z : E | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y} := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, h₀ hx, y, h₁ hy, rfl⟩
end CompactCombinations
 theorem rpow_iSup {ι : Sort*} (f : ι → ENNReal) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, f i ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup f
/-- Compact-set log-concavity is equivalent to the Borel/inner-measure formulation.
Compact sets are Borel and the inner measure is dominated by the measure, so the Borel
formulation specializes. Conversely, compact inner regularity writes each Borel mass as a
supremum over compact subsets; positive powers and products commute with these suprema, and
the compact combination of two compact subsets is a compact subset of the Borel combination.
The empty compact subset handles null sets; finite dimension includes the zero space. -/
theorem LogConcave.borel_iff [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    LogConcave μ ↔ BorelLogConcave μ := by
  constructor
  · intro h B₀ B₁ hB₀ hB₁ t ht0 ht1
    have ht1' : 0 < 1 - t := by linarith
    have key : ∀ K₀ K₁ : Set E, K₀ ⊆ B₀ → IsCompact K₀ → K₁ ⊆ B₁ → IsCompact K₁ →
        (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
          innerMeasure (μ : Measure E) {z | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y} :=
      fun K₀ K₁ h₀ hK₀ h₁ hK₁ ↦
        (h K₀ K₁ hK₀ hK₁ t ht0 ht1).trans
          (le_innerMeasure_of_isCompact _ (isCompact_combination hK₀ hK₁ t)
            (combination_mono h₀ h₁ t))
    calc (μ : Measure E) B₀ ^ t * (μ : Measure E) B₁ ^ (1 - t)
        = (⨆ (K : Set E) (_ : K ⊆ B₀) (_ : IsCompact K), (μ : Measure E) K) ^ t *
            (⨆ (K : Set E) (_ : K ⊆ B₁) (_ : IsCompact K), (μ : Measure E) K) ^ (1 - t) := by
          rw [hB₀.measure_eq_iSup_isCompact, hB₁.measure_eq_iSup_isCompact]
      _ = ⨆ (K₀ : Set E) (_ : K₀ ⊆ B₀) (_ : IsCompact K₀) (K₁ : Set E) (_ : K₁ ⊆ B₁)
            (_ : IsCompact K₁), (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) := by
          simp_rw [FunctionalInequalities.KLS.rpow_iSup _ ht0, FunctionalInequalities.KLS.rpow_iSup _ ht1', ENNReal.iSup_mul, ENNReal.mul_iSup]
      _ ≤ _ := by
          refine iSup₂_le fun K₀ h₀ ↦ iSup_le fun hK₀ ↦ iSup₂_le fun K₁ h₁ ↦ iSup_le fun hK₁ ↦ ?_
          exact key K₀ K₁ h₀ hK₀ h₁ hK₁
  · intro h K₀ K₁ hK₀ hK₁ t ht0 ht1
    exact (h K₀ K₁ hK₀.measurableSet hK₁.measurableSet t ht0 ht1).trans (innerMeasure_le _ _)
end KLS
end FunctionalInequalities


