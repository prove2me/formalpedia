-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
-- name    : KLS408915f_FunctionalInequalities_Probability_Domination_Local
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:38:03.418832+00:00
-- url     : https://prove2.me/theorems/95894277-038c-4fcf-9ec0-dac3bae758b6
-- title:
--   Local domination of measures on compact sets
-- statement:
--   `Probability.LocallyDominatesOn ν m Ω` means that for every compact K contained in Ω, there is a finite nonnegative constant C such that m restricted to K is at most C times ν restricted to K. `Probability.LocallyDominates` specializes this to the interior of the support of ν. The auxiliary theorem `LocallyDominatesOn.exists_lintegral_le` gives the corresponding lower-integral comparison for ENNReal-valued functions, and `measure_inter_eq_zero` transfers ν-nullity to m-nullity inside such compact sets under Borel-space assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Domination/Local.lean#L19-L71 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Domination.Local`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Domination_Local`; the repository is private at upload time).

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace FunctionalInequalities
namespace Probability
universe u
variable {V : Type u} [NormedAddCommGroup V] [MeasurableSpace V]
/-- On every compact subset of the set `Ω`, the reference measure `m` is dominated by a constant
multiple of `ν`. For a law with a density this says the density is locally bounded below by
positive constants on `Ω`. -/
def LocallyDominatesOn (ν : ProbabilityMeasure V) (m : Measure V) (Ω : Set V) : Prop :=
  ∀ K : Set V, IsCompact K → K ⊆ Ω →
    ∃ C : ℝ≥0, m.restrict K ≤ (C : ℝ≥0∞) • (ν : Measure V).restrict K
/-- On every compact subset of the interior of the support of `ν`, the reference measure `m` is
dominated by a constant multiple of `ν`. For a law with a density this says the density is
locally bounded below by positive constants on the interior of the support. -/
abbrev LocallyDominates (ν : ProbabilityMeasure V) (m : Measure V) : Prop :=
  LocallyDominatesOn ν m (interior (ν : Measure V).support)
namespace LocallyDominatesOn
variable {ν : ProbabilityMeasure V} {m : Measure V} {Ω : Set V}
/-- Lower integrals over a compact subset of `Ω` compare with a constant. -/
theorem exists_lintegral_le (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : V → ℝ≥0∞,
      ∫⁻ x in K, u x ∂m ≤ (C : ℝ≥0∞) * ∫⁻ x in K, u x ∂(ν : Measure V) := by
  obtain ⟨C, hC⟩ := h K hK hKΩ
  refine ⟨C, fun u ↦ ?_⟩
  calc ∫⁻ x in K, u x ∂m ≤ ∫⁻ x, u x ∂((C : ℝ≥0∞) • (ν : Measure V).restrict K) :=
        lintegral_mono' hC le_rfl
    _ = (C : ℝ≥0∞) * ∫⁻ x in K, u x ∂(ν : Measure V) := lintegral_smul_measure _ _
variable [BorelSpace V]
/-- `ν`-null sets inside a compact subset of `Ω` are `m`-null. -/
theorem measure_inter_eq_zero (h : LocallyDominatesOn ν m Ω) {K : Set V} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {s : Set V} (hs : (ν : Measure V) s = 0) :
    m (s ∩ K) = 0 := by
  obtain ⟨C, hC⟩ := h K hK hKΩ
  have h1 := Measure.le_iff'.mp hC s
  rw [Measure.smul_apply, Measure.restrict_apply' hK.measurableSet,
    Measure.restrict_apply' hK.measurableSet] at h1
  have h2 : (ν : Measure V) (s ∩ K) = 0 := measure_mono_null Set.inter_subset_left hs
  rw [h2, smul_zero] at h1
  exact le_antisymm h1 bot_le
end LocallyDominatesOn
end Probability
end FunctionalInequalities


