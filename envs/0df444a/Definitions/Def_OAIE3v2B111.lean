-- Prove2me | Definitions.Def_OAIE3v2B111
-- name    : OAIE3v2B111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:51:35.65963+00:00
-- url     : https://prove2.me/theorems/4334c9f6-a312-4713-aa9a-b8a5b28e4e9d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 113 of 311
-- statement:
--   Definitions bundle 113 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B090`, `OAIE3v2B091`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B095`, `OAIE3v2B096`, `OAIE3v2B097`, `OAIE3v2B098`, `OAIE3v2B099` of this split.
--
--   Modules: `Dynamics/CoefficientAmbientBudget.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedRefinedLongJetComparison.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/AllocatedSlicedCoveredComparison.lean`, `Estimates/AllocatedTailProfileIdentity.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/ExternalPivotMaskSelection.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/OneCubePrincipalSliceRiemann.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Geometry/AllocatedJetSupportBudget.lean`, `Geometry/AllocatedLayerQuarterSupport.lean`, `Geometry/CenteredCoefficientDeckChartMeasurable.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/MixedRealCoordinates.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/AllocatedIntegerKernelComparison.lean`, `Lattices/ForecastIntegerAxisSplit.lean`, `Lattices/PrincipalJoinedResidues.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/SpatialAffineFullMass.lean`, `Linear/AllocatedFixedKernelReplacement.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Probability/AllocatedDensityParameterBounds.lean`, `Probability/AllocatedLongJetMixture.lean`, `Probability/AllocatedSlicedIdealDensity.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/OrthonormalMixedLaw.lean`, `Probability/RelativeSliceFiniteLaw.lean`, `Probability/ScaledArrayLaw.lean`, `Sampling/AllocatedCoefficientSampler.lean`, `Sampling/AllocatedFrozenGridLaw.lean`, `Sampling/AllocatedLongGridCoordinates.lean`, `Sampling/AllocatedOriginalSampleForecastAtom.lean`, `Sampling/ForecastJointScaleNormalization.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B091
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B095
import Definitions.Def_OAIE3v2B096
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B098
import Definitions.Def_OAIE3v2B099

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem affineCoefficientMeasure_probability (c : ℝ) {w : ℝ} (hw : 0 < w) :
    IsProbabilityMeasure (affineCoefficientMeasure c w) :=
  realDensityMeasure_probability volume _ (affineProbabilityProfile_integrable c hw)
    (affineProbabilityProfile_nonneg c hw) (affineProbabilityProfile_integral c hw)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

noncomputable def principalResidueWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) m (hL j)
    (fun _ => m) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def principalTupleWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights α (L j) (hL j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedCoefficientLaw_probability {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    IsProbabilityMeasure (mixedCoefficientLaw c w p) := by
  let : ∀ i, IsProbabilityMeasure (affineCoefficientMeasure (c i) (w i)) :=
    fun i => affineCoefficientMeasure_probability (c i) (hw i)
  unfold mixedCoefficientLaw
  infer_instance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_measurable (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) : Measurable (orthonormalMixedDensity b c w p) := by
  have hf : Measurable (mixedCoefficientDensity c w p) :=
    binaryDensity_measurable (affineProductProfile_contDiff c w).continuous.measurable
      (measurable_of_countable (fun z : J → ℤ => ∏ j, (p j (z j)).toReal))
  exact hf.comp (orthonormalMixedChart b).symm.measurable

theorem orthonormalMixedDensity_law (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    Measure.map (orthonormalMixedChart b) (mixedCoefficientLaw c w p) =
      realDensityMeasure (volume.prod Measure.count) (orthonormalMixedDensity b c w p) := by
  rw [mixedCoefficientLaw_count_density c w hw p,
    realDensityMeasure_map_equiv (orthonormalMixedChart b),
    (orthonormalMixedChart_measurePreserving b).map_eq]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedScalarArrayLaw_regroup {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    Measure.map (mixedArrayRegroup I Z J) (mixedScalarArrayLaw c w p) =
      Measure.pi (fun j => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun z => p z j)) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  exact (mixedArrayRegroup_measurePreserving (fun i j => affineCoefficientMeasure (c i j) (w i j))
    (fun z j => (p z j).toMeasure)).map_eq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

theorem translatedQuotientChart_map_restrict (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    Measure.map (translatedQuotientChart Λ v) ((volume.prod (Measure.count : Measure T)).restrict S) =
      ENNReal.ofReal (ZLattice.covolume Λ) • μ.restrict (translatedQuotientChart Λ v '' S) := by
  have hq := translatedQuotientChart_measurable Λ v
  ext B hB
  rw [Measure.map_apply hq hB, Measure.restrict_apply (hB.preimage hq),
    Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  have hm := (hB.preimage hq).inter hS
  have hi := hinj.mono (inter_subset_right : (translatedQuotientChart Λ v ⁻¹' B ∩ S) ⊆ S)
  have he := translatedQuotientChart_haar_image Λ b μ v hm hi
  have hs : translatedQuotientChart Λ v '' (translatedQuotientChart Λ v ⁻¹' B ∩ S) =
      B ∩ translatedQuotientChart Λ v '' S := by
    ext q
    constructor
    · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
      exact ⟨hx, x, hxs, rfl⟩
    · rintro ⟨hqB, x, hxS, rfl⟩
      exact ⟨x, ⟨hqB, hxS⟩, rfl⟩
  have hc : ENNReal.ofReal (ZLattice.covolume Λ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
  have hx := (ENNReal.eq_div_iff hc ENNReal.ofReal_ne_top).mp he
  rw [hs] at hx
  exact hx.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedLatticeQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    Measurable (normalizedLatticeQuotient W b hb) := translatedQuotientChart_measurable _ _

theorem normalizedLatticeQuotient_map_restrict (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Measure.map (normalizedLatticeQuotient W b hb)
      ((volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
        (normalizedLatticePoint W b ⁻¹' Ω)) =
      ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) •
        μ.restrict (normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)) :=
  translatedQuotientChart_map_restrict _ (Free.chooseBasis ℤ _) μ _
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedQuotientDensity_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : Measurable f) :
    Measurable (normalizedQuotientDensity W b hb Ω f) :=
  embeddingDensity_measurable _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ _
    (hf.comp measurable_subtype_coe)

theorem normalizedQuotientDensity_bound (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x, ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * f x ≤ B) (y) :
    normalizedQuotientDensity W b hb Ω f y ≤ B :=
  embeddingDensity_bound _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective hB _
    (fun x => hf x.val) y

theorem normalizedQuotientDensity_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, normalizedLatticePoint W b x ∉ Ω → f x = 0) :
    Measure.map (normalizedLatticeQuotient W b hb)
      (realDensityMeasure (volume.prod (Measure.count : Measure (Fin n → ℤ))) f) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω f) :=
  restrictedChartDensity_law _ (normalizedLatticeQuotient_measurable W b hb)
    (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_embedding W b hb hΩm hΩ) _ μ
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
    (normalizedLatticeQuotient_map_restrict W b hb μ hΩm hΩ) f hf

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem mixedCoefficient_quotient_law (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (e : OrthonormalBasis I ℝ W)
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : (Fin n) → PMF ℤ)
    (hsupport : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart e x) ∈ Ω) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart e x))
      (mixedCoefficientLaw c w p) =
      realDensityMeasure μ (normalizedQuotientDensity W b hb Ω (orthonormalMixedDensity e c w p)) := by
  change Measure.map (normalizedLatticeQuotient W b hb ∘ orthonormalMixedChart e)
    (mixedCoefficientLaw c w p) = _
  rw [← Measure.map_map (normalizedLatticeQuotient_measurable W b hb) (orthonormalMixedChart e).measurable,
    orthonormalMixedDensity_law e c w hw p]
  apply normalizedQuotientDensity_law W b hb μ hΩm hΩ
  intro x hx
  by_contra hf
  have h := hsupport ((orthonormalMixedChart e).symm x) hf
  rw [(orthonormalMixedChart e).apply_symm_apply] at h
  exact hx h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_measurable (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    Measurable (canonicalMixedDensity W b hb o c w p) :=
  normalizedQuotientDensity_measurable W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_measurable o c w p)

theorem canonicalMixedDensity_bound
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    canonicalMixedDensity W b hb o c w p y ≤
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) * profileWidthFactor w := by
  have hv := (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (mul_nonneg hv (profileWidthFactor_pos w hw).le)
    (fun x => mul_le_mul_of_nonneg_left (mixedCoefficientDensity_width_cap c w hw p ((orthonormalMixedChart o).symm x)) hv) y

theorem canonicalMixedDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x))
      (mixedCoefficientLaw c w p) = realDensityMeasure μ (canonicalMixedDensity W b hb o c w p) :=
  mixedCoefficient_quotient_law W b hb o μ (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) c w hw p hs

theorem canonicalMixedDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalMixedDensity W b hb o c w p) μ ∧
      (∫ y, canonicalMixedDensity W b hb o c w p y ∂μ) = 1 := by
  have hlaw := canonicalMixedDensity_law W b hb o μ c w hw p hs
  let : IsProbabilityMeasure (mixedCoefficientLaw c w p) := mixedCoefficientLaw_probability c w hw p
  let : IsProbabilityMeasure (realDensityMeasure μ (canonicalMixedDensity W b hb o c w p)) := by
    rw [← hlaw]
    exact Measure.isProbabilityMeasure_map
      ((normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable).aemeasurable
  exact boundedDensity_mass μ _ (canonicalMixedDensity_measurable W b hb o c w p)
    (canonicalMixedDensity_nonneg W b hb o c w hw p) (canonicalMixedDensity_bound W b hb o c w hw p)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

omit [Fintype J] in
theorem mixedArrayQuotient_measurable (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) : Measurable (mixedArrayQuotient (J := J) W b hb o) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (normalizedLatticeQuotient_measurable W b hb).comp
    ((orthonormalMixedChart o).measurable.comp
      ((measurable_pi_apply j).comp (mixedArrayRegroup I (Fin n) J).measurable))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalArrayDensity_measurable (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ) :
    Measurable (canonicalArrayDensity W b hb o c w p) :=
  Finset.measurable_prod _ (fun j _ =>
    (canonicalMixedDensity_measurable W b hb o _ _ _).comp (measurable_pi_apply j))

theorem canonicalArrayDensity_mass
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Integrable (canonicalArrayDensity W b hb o c w p) (Measure.pi (fun _ : J => μ)) ∧
      (∫ y, canonicalArrayDensity W b hb o c w p y ∂Measure.pi (fun _ : J => μ)) = 1 := by
  have hslot (j) := canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)
  refine ⟨Integrable.fintype_prod_dep (fun j => (hslot j).1), ?_⟩
  unfold canonicalArrayDensity
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun j _ => (hslot j).2)

theorem canonicalArrayDensity_law
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (μ : Measure (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup))
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun i => p i j) x ≠ 0 →
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D) :
    Measure.map (mixedArrayQuotient W b hb o) (mixedScalarArrayLaw c w p) =
      realDensityMeasure (Measure.pi (fun _ : J => μ)) (canonicalArrayDensity W b hb o c w p) := by
  let q := fun x => normalizedLatticeQuotient W b hb (orthonormalMixedChart o x)
  have hq : Measurable q := (normalizedLatticeQuotient_measurable W b hb).comp (orthonormalMixedChart o).measurable
  have hqa : Measurable (fun x : J → (I → ℝ) × (Fin n → ℤ) => fun j => q (x j)) :=
    measurable_pi_iff.mpr (fun j => hq.comp (measurable_pi_apply j))
  change Measure.map ((fun x j => q (x j)) ∘ mixedArrayRegroup I (Fin n) J) (mixedScalarArrayLaw c w p) = _
  rw [← Measure.map_map hqa (mixedArrayRegroup I (Fin n) J).measurable, mixedScalarArrayLaw_regroup c w hw p]
  exact productDensity_pushforward _ (fun _ : J => μ) (fun _ => q) (fun _ => hq)
    (fun j => canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j))
    (fun j => (canonicalMixedDensity_mass W b hb o μ _ _ (fun i => hw i j) _ (hs j)).1)
    (fun j => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _)
    (fun j => canonicalMixedDensity_law W b hb o μ _ _ (fun i => hw i j) _ (hs j))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

theorem canonicalCoefficientDensity_measurable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    Measurable (canonicalCoefficientDensity U b hb o c w p) := by
  apply Finset.measurable_prod
  intro j _
  exact (canonicalArrayDensity_measurable _ (b j) (hb j) (o j) (c j) (w j) (p j)).comp
    ((measurable_pi_apply j).comp (euclideanCoefficientEquiv_continuous U).measurable)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hw : ∀ j i d, 0 < w j i d)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))

include ν hw hs

theorem canonicalCoefficientDensity_mass :
    Integrable (canonicalCoefficientDensity U b hb o c w p) μ ∧
      (∫ y, canonicalCoefficientDensity U b hb o c w p y ∂μ) = 1 := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  have hi : Integrable (tensorCutoffWeight f)
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) :=
    Integrable.fintype_prod_dep (fun j => (hm j).1)
  have hp := euclideanCoefficient_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hi, ?_⟩
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (tensorCutoffWeight f) (Measure.map (euclideanCoefficientEquiv U) μ) from
      hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  change (∫ y, tensorCutoffWeight f (euclideanCoefficientEquiv U y) ∂μ) = 1
  rw [← he, hp.map_eq]
  change (∫ y : EuclideanCoefficientLayers (K := K) U, (∏ j, f j (y j))
    ∂Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun j _ => (hm j).2)

omit [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem canonicalCoefficientLayers_law :
    Measure.map (fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
      mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j))
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
      realDensityMeasure
        (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)))
        (fun y : EuclideanCoefficientLayers (K := K) U => ∏ j,
          canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j)
            (c j) (w j) (p j) (y j)) := by
  let f := fun j => canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
  let q := fun j => mixedArrayQuotient (J := BoundedCoefficientExponent K (j.val + 1))
    (euclideanSubspace (U j)) (b j) (hb j) (o j)
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  have hq (j) : Measurable (q j) := mixedArrayQuotient_measurable _ (b j) (hb j) (o j)
  have hm (j) := canonicalArrayDensity_mass _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j)
  exact productDensity_pushforward (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) q hq f
    (fun j => (hm j).1)
    (fun j => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j) (c j) (w j) (hw j) (p j))
    (fun j => canonicalArrayDensity_law _ (b j) (hb j) (o j) (ν j) (c j) (w j) (hw j) (p j) (hs j))

theorem canonicalCoefficientDensity_law :
    Measure.map (canonicalCoefficientSample (K := K) U b hb o)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) =
        realDensityMeasure μ (canonicalCoefficientDensity U b hb o c w p) := by
  let q := fun a : CoefficientSamplerArrays (K := K) I n => fun j =>
    mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (a j)
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let e := euclideanCoefficientMeasurableEquiv (K := K) U
  have hq : Measurable q := measurable_pi_iff.mpr (fun j =>
    (mixedArrayQuotient_measurable _ (b j) (hb j) (o j)).comp (measurable_pi_apply j))
  have hp : Measure.map e μ = ξ := (euclideanCoefficient_measurePreserving U μ ν).map_eq
  have hinv : Measure.map e.symm ξ = μ := by rw [← hp]; exact e.map_symm_map
  change Measure.map (e.symm ∘ q) _ = _
  rw [← Measure.map_map e.symm.measurable hq,
    canonicalCoefficientLayers_law U b hb o c w p ν hw hs,
    realDensityMeasure_map_equiv, hinv]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem allocatedArrayProfiles_bound {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (hT : ∀ v, 1 ≤ T v) (Pc : I → Finset J) (j₀ : J) (hc₀ : ∀ i, j₀ ∉ Pc i)
    {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (i : I) (j : J) :
    |allocatedArrayCenters e T Pc R i j| + allocatedArrayWidths e T Pc j₀ R σ i j ≤ R := by
  apply scaledProfile_div_bound (continuousPolynomialDensity_width_pos (Pc i) j₀ hR hσ j).le
    (one_le_monomialScale T hT (e j))
  exact (allocatedProfile_term_bound (Pc i) j₀ (hc₀ i) hR hσ hσ1 j).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_chart (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D := by
  apply mixedCoefficient_small_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include hR hσ in
theorem allocatedLayerColumns_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (d) (x) (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArrayColumns_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedLayerQuarterSupport
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem mixedCoefficient_quarter_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart W b).symm x‖ ≤ C * ‖x‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1/4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R)
    (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  obtain ⟨hu, hz⟩ := (mixedCoefficientDensity_support c w p x).mp hx
  have hn := mixedRealPoint_norm_le W b o hC hR hchart x.1
    (fun i => (x.2 i : ℝ) / basisAxisScale b i)
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hu i)).trans (hcw i))
    (fun i => hp i _ (hz i))
  rw [mixedRealPoint_integer] at hn
  have hquarter : ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ ≤ 1/4 :=
    hn.trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd : |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤
      ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart o x)) d
  exact hd.trans hquarter

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_quarter_support (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  apply mixedCoefficient_quarter_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem allocatedLayerColumns_quarter_support (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (j : Fin m) (d) (x)
    (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    ∀ a, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4 := by
  exact allocatedArrayColumns_quarter_support (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealCoordinates_integer (u : I → ℝ) (z : Fin n → ℤ) :
    mixedRealCoordinates W b o (normalizedLatticePoint W b (orthonormalMixedChart o (u, z))) =
      (u, fun i => (z i : ℝ) / basisAxisScale b i) := by
  rw [← mixedRealPoint_integer W b o]
  exact mixedRealCoordinates_point W b o _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientSlot_card_le {K : Type*} [Fintype K] (m : ℕ) :
    Fintype.card (CoefficientSlot K m) ≤ m * (m + 1) * (Fintype.card K + 1) ^ m := by
  simp only [CoefficientSlot, Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : Fin m, (m + 1) * (Fintype.card K + 1) ^ m := by
      apply Finset.sum_le_sum
      intro j _
      apply (boundedCoefficientExponent_card_le (j.val + 1)).trans
      apply Nat.mul_le_mul (by omega)
      exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt j.isLt)
    _ = _ := by simp; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientAmbientIndex_card_le_real {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤
      (m : ℝ) * (m + 1) * (P + 1)^m * P := by
  have hs : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ (m : ℝ) * (m + 1) * (P + 1)^m := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by gcongr)
  calc
    _ = ∑ s : CoefficientSlot K m, (Fintype.card (J s.1) : ℝ) := by
      rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _s : CoefficientSlot K m, P := Finset.sum_le_sum (fun s _ => hJ s.1)
    _ = (Fintype.card (CoefficientSlot K m) : ℝ) * P := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hP

theorem coefficient_ambient_input_exp_bounds {m : ℕ} {K : Type*} [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P A L Q : ℝ}
    (hP : 0 ≤ P) (hK : (Fintype.card K : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hbudget : (m : ℝ) * (m + 1) * (P + 1)^m * (P + 1) + P + 1 ≤ Q) :
    P ≤ Q ∧ (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q ∧
      A^Fintype.card (CoefficientSlot K m) ≤ Real.exp Q ∧
      (Fintype.card (CoefficientSlot K m) : ℝ) * L * A^Fintype.card (CoefficientSlot K m) ≤
        Real.exp Q := by
  let T := (m : ℝ) * (m + 1) * (P + 1)^m
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoly' : T * (P + 1) + P + 1 ≤ Q := hbudget
  have hN : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ T := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by dsimp [T]; gcongr)
  have hNP : (Fintype.card (CoefficientSlot K m) : ℝ) * P ≤ T * P :=
    mul_le_mul_of_nonneg_right hN hP
  have hcap : A^Fintype.card (CoefficientSlot K m) ≤
      Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP (Fintype.card (CoefficientSlot K m))
  have hNexp : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ Real.exp T :=
    hN.trans (by linarith [Real.add_one_le_exp T])
  refine ⟨(by nlinarith), ?_, ?_, ?_⟩
  · exact (coefficientAmbientIndex_card_le_real hP hK hJ).trans (by dsimp [T] at hpoly'; nlinarith)
  · exact hcap.trans (Real.exp_le_exp.mpr (by nlinarith))
  · calc
      _ ≤ Real.exp T * Real.exp P * Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by gcongr
      _ = Real.exp (T + P + (Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

noncomputable def coefficientJetAxisMap {K : Type*} [Fintype K] {O : Fin m → Type*}
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ) :
    ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a → CoefficientJetAxisRow O a
  | ⟨j, .inl _⟩, c => (A j).map (Int.cast : ℤ → ℝ) *ᵥ c
  | ⟨j, .inr _⟩, c => A j *ᵥ c

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hσ1 C hC hchart hsmall ν

theorem allocatedCoefficientDensity_spec :
    Measurable (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ y, 0 ≤ allocatedCoefficientDensity B U b hb o hR hσ S y) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ y, allocatedCoefficientDensity B U b hb o hR hσ S y ∂μ) = 1 ∧
      Measure.map (canonicalCoefficientSample U b hb o) (allocatedCoefficientSource B U b hR hσ S) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have hw := allocatedLayerWidths_pos B U b hR hσ S
  have hs := allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
  have hm := canonicalCoefficientDensity_mass U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S) μ ν hw hs
  exact ⟨canonicalCoefficientDensity_measurable U b hb o _ _ _,
    canonicalCoefficientDensity_nonneg U b hb o _ _ _ hw, hm.1, hm.2,
    canonicalCoefficientDensity_law U b hb o _ _ _ μ ν hw hs⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedCoefficient_fourier_input_budget
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (C V : Fin m → ℝ≥0)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    let A := allocatedAmbientFactorCap (G := G) B R σ L V
    let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    P ≤ allocatedFourierLogBudget m P ∧
      (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ allocatedFourierLogBudget m P ∧
      (A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) ∧
      (N : ℝ)*F*(A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) := by
  let A := allocatedAmbientFactorCap (G := G) B R σ L V
  let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
  let T := P + allocatedAmbientLog m P
  have hPT : P ≤ T := le_add_of_nonneg_right (allocatedAmbientLog_nonneg m hP)
  have hT : 0 ≤ T := hP.trans hPT
  obtain ⟨ha, hf⟩ := allocatedAmbientConstants_exp_bounds B R σ L hL _ C V hP hm
    hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have he : Real.exp (allocatedAmbientLog m P) ≤ Real.exp T :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hP)
  have h := coefficient_ambient_input_exp_bounds
    hT (hK.trans hPT) (fun j => (hJ j).trans hPT) A.coe_nonneg (ha.trans he) F.coe_nonneg (hf.trans he)
    (coefficientAmbientBudgetExponent_bound m hT)
  exact ⟨hPT.trans h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedFourierOutputBudget_dominates (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    2*Q*(2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      (2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      2*Q*(2*Q+2)^4+Q ≤ allocatedFourierOutputBudget m P := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hpow : 0 ≤ (2*allocatedFourierLogBudget m P+2)^4 := by positivity
  have hprod : 0 ≤ 2*allocatedFourierLogBudget m P*(2*allocatedFourierLogBudget m P+2)^4 := by positivity
  dsimp only [allocatedFourierOutputBudget]
  constructor
  · linarith
  constructor <;> linarith

theorem exists_allocatedFourierOutputBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierOutputBudget m P ≤ (P+a)^a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b
  let output : Polynomial ℕ := 2*q*(2*q+2)^4+q+(2*q+2)^4
  obtain ⟨a, ha, hout⟩ := exists_natPolynomial_eval_budget output
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hqb := hb P hP
  have hbound : 2*((P+b)^b)*(2*((P+b)^b)+2)^4+(P+b)^b+(2*((P+b)^b)+2)^4 ≤ (P+a)^a := by
    simpa [output, q, Polynomial.eval₂_pow] using hout P hP
  apply le_trans _ hbound
  dsimp only [allocatedFourierOutputBudget]
  gcongr

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPivotMaskSelection
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem sum_externalNet_masked_complex_scores
    {J X Y I : Type*} [Fintype J] [Fintype I]
    (p : FiniteProbabilityWeights J) (idx : X → I)
    (physical : J → X) (point : J → Y) (w : X → ℂ) (centers : I → Y → ℂ) :
    (∑ i, p.complexMean (fun j =>
      (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))) =
    p.complexMean (fun j => w (physical j) * centers (idx (physical j)) (point j)) := by
  simp only [FiniteProbabilityWeights.complexMean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  simp only [ite_mul, zero_mul]
  simp

theorem exists_externalNet_large_masked_complex_score
    {J X Y I : Type*} [Fintype J] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights J) (F : X → Y → ℂ) (centers : I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (physical : J → X) (point : J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ j, ‖w (physical j)‖ ≤ B)
    (hscore : δ ≤ ‖p.complexMean (fun j => w (physical j) * F (physical j) (point j))‖) :
    ∃ i, δ / (2 * Fintype.card I) ≤ ‖p.complexMean (fun j =>
      (if externalNetIndex F centers hnet (physical j) = i then w (physical j) else 0) *
        centers i (point j))‖ := by
  let idx := externalNetIndex F centers hnet
  let scores := fun i => p.complexMean (fun j =>
    (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))
  have hnear := p.norm_complexMean_weighted_lower_of_perturbation
    (fun j => w (physical j)) (fun j => centers (idx (physical j)) (point j))
    (fun j => F (physical j) (point j)) hB hw
    (fun j => by rw [norm_sub_rev]; exact externalNetIndex_approx F centers hnet _ _) hscore
  have hsum : δ / 2 ≤ ‖∑ i, (1 : ℂ) * scores i‖ := by
    simp only [one_mul]
    rw [show (∑ i, scores i) = p.complexMean (fun j =>
      w (physical j) * centers (idx (physical j)) (point j)) from
        sum_externalNet_masked_complex_scores p idx physical point w centers]
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ)) scores
    (by positivity : 0 < δ / 2) (show 0 < (Fintype.card I : ℝ) from Nat.cast_pos.mpr Fintype.card_pos)
    (by simp) hsum
  refine ⟨i, ?_⟩
  simpa only [scores, idx, div_div] using hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable instance allocatedGridAxisDecidable (L : ℕ) :
    DecidablePred (allocatedGridAxis (I := I) U basis L) := Classical.decPred _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

abbrev AllocatedFrozenCoefficients := ∀ a : {a // grid a}, CoefficientAxisRow vars a.val

abbrev AllocatedLongCoefficients := ∀ a : {a // ¬grid a}, CoefficientAxisRow vars a.val

noncomputable def allocatedCoefficientSplit :
    CoefficientSamplerArrays (K := vars) I n ≃ᵐ
      AllocatedFrozenCoefficients B U basis S × AllocatedLongCoefficients B U basis S :=
  coefficientAxisSplitEquiv vars I n grid

noncomputable def allocatedCoefficientAxisLaw :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow vars a) :=
  coefficientAxisLaw (allocatedLayerCenters B U basis S) (allocatedLayerWidths B U basis S)
    (allocatedLayerIntegerPMFs B U basis hR hσ S)

noncomputable def allocatedFrozenCoefficientSource : Measure (AllocatedFrozenCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

abbrev AllocatedNonkernelCoefficient (j : Fin m) :=
  NonkernelCoefficient G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

noncomputable def allocatedKernelCoefficientEquiv (j : Fin m) :
    BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j ≃
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) :=
  kernelCoefficientEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1)

def allocatedNonkernelExponent (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    LayerSamplerVariables G I n B →₀ ℕ := d.val.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

noncomputable def allocatedPartitionedJetMatrix (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ :=
  integerMappedJetMatrix Subtype.val input fixedInteger (rows j) (principalTupleIntegers v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

noncomputable def allocatedNonkernelJetMatrix
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) ℤ :=
  integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger (rows j)
    (principalTupleIntegers v)

noncomputable def allocatedIntegerKernelMask (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    (O j → ℤ) → ℝ :=
  coefficientResidueMultiplier (scalarKernelIntegerJet x (j.val+1) (rows j)) residue

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

abbrev AllocatedLongJetRows (O : Fin m → Type*) :=
  ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

noncomputable def allocatedLongJetOutputScale : {a // ¬grid a} → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => 1
  | ⟨⟨j, .inr i⟩, _⟩ => (basisAxisScale (basis j) i : ℝ)^Fintype.card (O j)

noncomputable def allocatedLongJetMask (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => fun _ => 1
  | ⟨⟨j, .inr _⟩, _⟩ => allocatedIntegerKernelMask B U basis S x rows j modulus (residue j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedKernelReplacementLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P e : ℝ) : ℝ :=
  ∑ j, coefficientFrontLog (Fintype.card (O j))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (allocatedKernelLog G α O P) (4*(P+8)) e

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalJoinedResidues
namespace OAI

section

namespace Erdos3

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

def principalAxisResidueJoin (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L) (m : ℕ)
    (r : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → Option α → ZMod m) :
    PrincipalTupleIndex B h → Option α → ZMod m :=
  fun j i => if hp : P j.1 then ((u ⟨⟨j.1, hp⟩, j.2⟩ i : ℤ) : ZMod m)
    else r ⟨⟨j.1, hp⟩, j.2⟩ i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

abbrev AllocatedFrozenJetRows (O : Fin m → Type*) :=
  ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val

variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

noncomputable def allocatedFrozenJetMap (a : AllocatedFrozenCoefficients B U b S) :
    AllocatedFrozenJetRows B U b S O :=
  fun i => coefficientJetAxisMap (allocatedPartitionedJetMatrix B U b S x u v rows) i.val (a i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedDensityColumnLog (α : Type*) [Fintype α] (j : Fin m) : ℝ :=
  Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) +
    3*(Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) : ℝ)*(j.val+1) +
    (Fintype.card α : ℝ)*(j.val+2)

noncomputable def allocatedDensityLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8)) +
    P + ∑ j, allocatedDensityColumnLog (G := G) B α j

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedJetSupportBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedJetSupportLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  allocatedDensityLog (G := G) B α O P + P +
    ∑ j : Fin m,
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

def fiberPointInBox (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (u : ∀ k, Fin (S.length k)) : integerBox N :=
  ⟨S.fiberIntegerPoint fixed u, S.fiberIntegerPoint_mem_integerBox fixed hfixed u⟩

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedLongJetRealCoordinates (z : AllocatedLongJetRows B U basis S O) :
    realOutput → ℝ
  | ⟨⟨⟨j, .inl i⟩, ha⟩, o⟩ => z ⟨⟨j, .inl i⟩, ha⟩ o
  | ⟨⟨⟨j, .inr i⟩, ha⟩, o⟩ => (z ⟨⟨j, .inr i⟩, ha⟩ o : ℝ) / (basisAxisScale (basis j) i : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

noncomputable def activeAveragedSlicedProfileIdeal (ρ : ℝ≥0)
    (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    ((Σ d, O d) → ℝ) → ℝ :=
  densityMixture (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))
    (activeSlicedProfileIdeal Z h P sets ρ center width)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

noncomputable def principalProgressionSliceCenter (L : PrincipalTupleIndex B h → ℕ)
    (c : PrincipalTupleIndex B h → ℤ) : JointBlockParameter B h α → ℝ :=
  principalTupleFlatten B h α (fun j i => if i = none then (c j : ℝ) / L j else 0)

noncomputable def principalProgressionSliceWidth (L H step : PrincipalTupleIndex B h → ℕ) :
    JointBlockParameter B h α → ℝ :=
  principalTupleFlatten B h α (fun j _ => (step j : ℝ) * ((H j : ℝ) - 1) / L j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedLongGridCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

def allocatedLongIntegerCoordinate : output → Prop
  | ⟨⟨⟨_, .inl _⟩, _⟩, _⟩ => False
  | ⟨⟨⟨_, .inr _⟩, _⟩, _⟩ => True

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

def allocatedLongIntegerSelect : integerOutput ↪ output :=
  ⟨Subtype.val, Subtype.val_injective⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}

noncomputable def allocatedFixedPathLiftRowCap {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (j : Active) : ℝ≥0 :=
  SlicedProductBlock.uniformCap
    {k : Fin (degree j.val) // k ≠ ⟨0, Nat.zero_lt_succ _⟩}
    (a * δ ^ (Fintype.card {k : Fin (degree j.val) // k ≠ ⟨0, Nat.zero_lt_succ _⟩} + 1))
    (mul_pos ha (pow_pos hδ _))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedForwardSeedPolynomial
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | outer + 1 => (preparedFiniteForwardWorkPolynomial A constants innerDepth).comp
      (candidateNestedForwardSeedPolynomial A constants innerDepth outer)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CenteredCoefficientDeckChartMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

def coefficientDeckChartEvent (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) (y : CoefficientTorus (K := K) U) : Prop :=
  ∃ x : CoefficientSamplerArrays (K := K) I n, ∃ r : CoefficientDeckResidues (K := K) E q,
    (∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) ∧
    canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r = y ∧
    event (coefficientSamplerChartResidues q x r)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def AllocatedActiveIntegerAxis (L : ℕ) :=
  {a : Σ j : Fin m, Fin (n j) // L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2}

noncomputable instance instFintypeAllocatedActiveIntegerAxis (L : ℕ) : Fintype (AllocatedActiveIntegerAxis U basis L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2})

noncomputable def allocatedActiveIntegerGridScale (R : Fin m → ℝ) (L : ℕ)
    (a : AllocatedActiveIntegerAxis U basis L) : ℝ :=
  R a.val.1 * (basisAxisScale (basis a.val.1) a.val.2 : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedForecastAllAxisRowCap {δ : ℝ} (hδ : 0 < δ)
    (a : LayerSamplerAxis I n) : ℝ≥0 :=
  allocatedFixedPathLiftRowCap (fun _ : LayerSamplerAxis I n => False)
    (unitProfilePrincipalLowerBound_pos B) hδ ⟨a, not_false⟩

noncomputable def allocatedForecastAllAxisLiftCap {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  ∏ a, (allocatedForecastAllAxisRowCap B hδ a + 1)

noncomputable def allocatedForecastAllAxisLiftLip {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ *
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def forecastGeometricJacobian (R : Fin m → ℝ) (L : ℕ)
    (gridVolume τ : ℝ) : ℝ :=
  (coveredJetArrayScale (O := fun _ : Fin m => Unit) U * gridVolume *
    (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
    (∏ a, allocatedActiveIntegerGridScale U basis R L a))⁻¹

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem scaleMvPolynomialAxes_affineFrame_eq_const_add_top
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (affineFramePolynomial frame x) =
      C (frame none x) +
        scaleMvPolynomialAxes T
          (homogeneousComponent 1 (affineFramePolynomial frame x)) := by
  apply MvPolynomial.funext
  intro y
  rw [affineFramePolynomial_top_one]
  simp only [scaleMvPolynomialAxes_eval, affineFramePolynomial,
    map_add, eval_C, eval_sum, map_mul, eval_X]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

theorem modularDeckPolynomial_degree (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : (modularDeckPolynomial r j i).totalDegree ≤ j.val + 1 := by
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (r j e i)).trans e.property

end VectorPolynomial

end Erdos3

end

end OAI
end


