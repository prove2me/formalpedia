-- Prove2me | Definitions.Def_OAIE3v2B192
-- name    : OAIE3v2B192
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:56:58.933675+00:00
-- url     : https://prove2.me/theorems/6ad898e1-fecd-4adf-80c3-2b37522202a7
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 195 of 311
-- statement:
--   Definitions bundle 195 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B171`, `OAIE3v2B173`, `OAIE3v2B174`, `OAIE3v2B175` of this split.
--
--   Modules: `Dynamics/NativeAdaptedOrdinaryResetGeometry.lean`, `Estimates/AllocatedMarkedDictionaryRecovery.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/ControlledRefilteredRecoveredExpansion.lean`, `Estimates/EmptyLayerPrescribedScale.lean`, `Estimates/LowerRefilteredCyclicExpansion.lean`, `Estimates/NativeModelOrbit.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NormalizedTwistSliceVariationPairCorrelation.lean`, `Estimates/PreparedRelativeInitializerScalarInputs.lean`, `Estimates/PrescribedComplementInputPartition.lean`, `Estimates/UniformFiniteMarkedFactorParameters.lean`, `Geometry/AllocatedGeometricInputBudget.lean`, `Lattices/FixedAffineResidueDescent.lean`, `Lattices/RetainedAffineResidueEpoch.lean`, `Linear/ExternalFamilyPrecenterProjectionData.lean`, `Linear/NativeMarkedKernelFreezing.lean`, `Linear/SingleRefilteredKernel.lean`, `Nilpotent/CommonVariableDimensionNiltests.lean`, `Nilpotent/NativeCoverNiltest.lean`, `Sampling/MarkedExternalKernelProjectionScoreRestoration.lean`, `Sampling/MarkedKernelProjectionScoreRestoration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B171
import Definitions.Def_OAIE3v2B173
import Definitions.Def_OAIE3v2B174
import Definitions.Def_OAIE3v2B175

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}

structure AdaptedMapGeometryData (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  source : D.AdaptedModelData
  target : E.AdaptedModelData
  budget_nonneg : 0 ≤ q
  forward_budget : p + 1 ≤ q
  source_dimension : (finrank ℚ L : ℝ) ≤ p
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  source_geometry : source.model.GeometryComplexityLE q
  target_geometry : target.model.GeometryComplexityLE q
  source_forward : ∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1
  target_forward : ∀ i j, rationalLogHeight (E.basis.repr (target.basis i) j) ≤ p + 1
  source_inverse : ∀ i j, rationalLogHeight (source.basis.repr (D.basis i) j) ≤ q
  target_inverse : ∀ i j, rationalLogHeight (target.basis.repr (E.basis i) j) ≤ q
  source_structure : ∀ i j k,
    rationalLogHeight (source.basis.repr ⁅source.basis i, source.basis j⁆ k) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}

structure FixedSourceAdaptedMarkGeometryData
    (D : RationalFilteredNilmanifold L s d)
    (Fmark : RationalFilteredNilmanifold M t f)
    (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) (p q : ℝ) where
  target : Fmark.AdaptedModelData
  target_geometry : target.model.GeometryComplexityLE q
  target_dimension : (finrank ℚ M : ℝ) ≤ p
  target_forward : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (target.basis i) j) ≤ p + 1
  target_inverse : ∀ i j,
    rationalLogHeight (target.basis.repr (Fmark.basis i) j) ≤ q
  target_structure : ∀ i j k,
    rationalLogHeight (target.basis.repr ⁅target.basis i, target.basis j⁆ k) ≤ q
  entries_height : ℕ
  entries_height_pos : 0 < entries_height
  entries_bound : (entries_height : ℝ) ≤ Real.exp q
  entries : ∀ i j,
    RationalHeightLE (target.basis.repr (φ (source.basis j)) i) entries_height
  entries_logHeight : ∀ i j,
    rationalLogHeight (target.basis.repr (φ (source.basis j)) i) ≤ q

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

theorem optionOriginalObservable_adapted_member_nets
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y : adapted.model.Space,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η :=
  optionOriginalObservable_member_nets D₀ D observable sites entropy hnets

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeAdaptedOrdinaryResetGeometry
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L QL ML : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing QL] [LieAlgebra ℚ QL] [LieRing ML] [LieAlgebra ℚ ML]
    {s t r d e f : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {Q : RationalFilteredNilmanifold QL t e}
    {Mmark : RationalFilteredNilmanifold ML r f}
    {ψ : L →ₗ⁅ℚ⁆ QL} {φ : QL →ₗ⁅ℚ⁆ ML}
    {pg qg pm qm p0 : ℝ}

namespace AdaptedMapGeometryData

theorem ordinaryResetGeometry
    (geometry : D.AdaptedMapGeometryData Q ψ pg qg)
    (markGeometry : Q.FixedSourceAdaptedMarkGeometryData Mmark geometry.target φ pm qm)
    (hp0 : 0 ≤ p0) (hgeom : qg ≤ p0) (hmark : qm ≤ p0) (hgen : pg ≤ p0) :
    geometry.target.model.GeometryComplexityLE p0 ∧
    markGeometry.target.model.GeometryComplexityLE p0 ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (markGeometry.target.basis j) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.basis.repr (φ (geometry.target.basis j)) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (φ (geometry.target.model.basis j)) i) ≤ p0) ∧
    (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ QL)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ ML)) : ℝ) ≤ p0 := by
  have hsourceGeometry := geometry.target_geometry.mono geometry.target.model hgeom
  have hmarkedGeometry := markGeometry.target_geometry.mono markGeometry.target.model hmark
  refine ⟨hsourceGeometry, hmarkedGeometry, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change rationalLogHeight (markGeometry.target.basis.repr
      (markGeometry.target.basis j) i) ≤ p0
    rw [Basis.repr_self]
    simp only [Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp0
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · simpa only [Fintype.card_fin] using geometry.source_dimension.trans hgen
  · simpa only [Fintype.card_fin] using geometry.target_dimension.trans hgen
  · simpa only [Fintype.card_fin] using hmarkedGeometry.1

end AdaptedMapGeometryData
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    let := D.metricSpace
    ∃ g : D.RealGroup, g.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅g.coord, y⁆ = 0) ∧
      ∀ x, iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x = g • x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact D.exists_iteratedCentralCircle_translation K hK (Module.finBasis ℚ K)
    (List.finRange (finrank ℚ K)) t

noncomputable def kernelProjectionTranslation (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) : D.RealGroup :=
  (D.exists_kernelProjectionTranslation K hK t).choose

theorem kernelProjectionTranslation_mem (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) :
    (D.kernelProjectionTranslation K hK t).coord ∈ K.baseChange ℝ :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.1

theorem kernelProjectionTranslation_central (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K)
    (y : ℝ ⊗[ℚ] L) : ⁅(D.kernelProjectionTranslation K hK t).coord, y⁆ = 0 :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.1 y

theorem kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (t : KernelProjectionParameters K) (x : D.Space) :
    let := D.metricSpace
    iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
      (List.finRange (finrank ℚ K)) t x = D.kernelProjectionTranslation K hK t • x :=
  (D.exists_kernelProjectionTranslation K hK t).choose_spec.2.2 x

theorem continuous_kernelProjectionTranslation_act (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    let := D.metricSpace
    Continuous (fun t => D.kernelProjectionTranslation K hK t • x) := by
  let := D.metricSpace
  have he : (fun t => D.kernelProjectionTranslation K hK t • x) =
      (fun t => iteratedCircleAction (D.kernelProjectionCircleFamily K hK)
        (List.finRange (finrank ℚ K)) t x) :=
    funext (fun t => (D.kernelProjectionTranslation_act K hK t x).symm)
  rw [he]
  exact continuous_iteratedCircleAction_parameter _ _ _

namespace Niltest

variable {D} {σ : Type*} {w : σ → ℕ}

theorem continuous_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Continuous (fun t => T.observable (D.kernelProjectionTranslation K hK t • x)) := by
  let := D.metricSpace
  exact T.lipschitz.continuous.comp (D.continuous_kernelProjectionTranslation_act K hK x)

theorem integrable_kernelProjectionTranslation_observable (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    Integrable (fun t => T.observable (D.kernelProjectionTranslation K hK t • x))
      (circleAverageTupleMeasure (List.finRange (finrank ℚ K))) :=
  (T.continuous_kernelProjectionTranslation_observable K hK x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem kernelProjection_observable_eq_integral (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (x : D.Space) :
    (T.kernelProjection K hK).observable x =
      ∫ t, T.observable (D.kernelProjectionTranslation K hK t • x)
        ∂circleAverageTupleMeasure (List.finRange (finrank ℚ K)) := by
  let := D.metricSpace
  change iteratedCircleAverage (D.kernelProjectionCircleFamily K hK)
    (List.finRange (finrank ℚ K)) T.observable x = _
  rw [iteratedCircleAverage_eq_integral _ _ T.lipschitz.continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => congrArg T.observable
    (D.kernelProjectionTranslation_act K hK t x))

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open MeasureTheory Module CircleFourier
open scoped TensorProduct

variable {L σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_common_translation
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (path : Ω → J → D.Space) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * ((T (physical a j)).kernelProjection K hK).observable
        (path a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
          (fun j => weight a j * (T (physical a j)).observable (z • path a j))).re := by
  let μ := circleAverageTupleMeasure (List.finRange (finrank ℚ K))
  let obs (a : Ω) (j : J) (t : KernelProjectionParameters K) :=
    (T (physical a j)).observable (D.kernelProjectionTranslation K hK t • path a j)
  let score (a : Ω) := (localLaw a).finiteScore (weight a) (obs a)
  have hmeas (a : Ω) (j : J) : Measurable (obs a j) :=
    ((T (physical a j)).continuous_kernelProjectionTranslation_observable
      K hK (path a j)).measurable
  have hi (a : Ω) (j : J) : Integrable (obs a j) μ :=
    (T (physical a j)).integrable_kernelProjectionTranslation_observable K hK (path a j)
  have hscoreMeas (a : Ω) : Measurable (score a) :=
    (localLaw a).finiteScore_measurable (weight a) (obs a) (hmeas a)
  have hscoreInt (a : Ω) : Integrable (score a) μ :=
    (localLaw a).finiteScore_integrable μ (weight a) (obs a) (hi a)
  have hcap (a : Ω) (ha : a ∈ H) (t : KernelProjectionParameters K) : score a t ≤ B :=
    (localLaw a).finiteScore_le (weight a) (obs a) hB.le (hweight a ha)
      (fun j _ => (hT (physical a j)).norm_le_one _) t
  have havg (a : Ω) (ha : a ∈ H) : δ ≤ ∫ t, score a t ∂μ := by
    rw [(localLaw a).integral_finiteScore μ (weight a) (obs a) (hi a)]
    simpa only [obs, μ, ← kernelProjection_observable_eq_integral] using hscore a ha
  obtain ⟨t, H', hsub, hpos, hmass, hs⟩ :=
    exists_common_translation_retained_scores outer H hH μ score hB hδ
      (fun a _ => hscoreMeas a) (fun a _ => hscoreInt a) hcap havg
  exact ⟨D.kernelProjectionTranslation K hK t,
    D.kernelProjectionTranslation_mem K hK t,
    D.kernelProjectionTranslation_central K hK t,
    H', hsub, hpos, hmass, hs⟩

theorem exists_external_kernelProjection_restored_orbit
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((T (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ x, ((T x).withLeftTranslatedOrbit z orbit).observable = (T x).observable ∧
        ((T x).withLeftTranslatedOrbit z orbit).UnitIntervalValued ∧
        ∀ p, ((T x).withLeftTranslatedOrbit z orbit).ComplexityLE p ↔ (T x).ComplexityLE p) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight a j *
          ((T (physical a j)).withLeftTranslatedOrbit z orbit).eval (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_common_translation T hT K hK outer H hH localLaw
      physical (fun a j => QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval v (point a j) orbit))
      weight hB hδ hweight hscore
  refine ⟨z, hz, fun x => ⟨rfl, hT x, fun _ => Iff.rfl⟩,
    H', hsub, hpos, hmass, ?_⟩
  intro a ha
  simpa only [withLeftTranslatedOrbit_eval] using hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeCoverNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (Λ : Subgroup D.filtration.Group) (m : ℕ) (hm : 0 < m)
  (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m) (hΛ : Λ ≤ D.lattice)

noncomputable def onSublattice : (D.withLattice Λ m hm hin hout).Niltest w where
  orbit := T.orbit
  observable := T.observable ∘ sublatticeProjection D (D.withLattice Λ m hm hin hout) hΛ
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le _ := T.norm_le _
  lipschitz := sublattice_pullback_lipschitz D (D.withLattice Λ m hm hin hout) hΛ rfl
    T.observable T.lipschitz

theorem onSublattice_complexity {p : ℝ} (hT : T.ComplexityLE p)
    (hD : (D.withLattice Λ m hm hin hout).GeometryComplexityLE p) :
    (T.onSublattice Λ m hm hin hout hΛ).ComplexityLE p := ⟨hD, hT.2⟩

theorem onSublattice_unit_interval (hT : T.UnitIntervalValued) :
    (T.onSublattice Λ m hm hin hout hΛ).UnitIntervalValued := fun _ => hT _

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)

namespace NativeModelEquiv

variable {D E} (e : NativeModelEquiv D E)

noncomputable def symm : NativeModelEquiv E D where
  toLieEquiv := e.toLieEquiv.symm
  map_basis i := by
    apply e.toLieEquiv.injective
    change e.toLieEquiv (e.toLieEquiv.symm (E.basis i)) = e.toLieEquiv (D.basis i)
    rw [LieEquiv.apply_symm_apply, e.map_basis]
  mem_layer n x := by
    have h := e.mem_layer n (e.toLieEquiv.symm x)
    rw [LieEquiv.apply_symm_apply] at h
    exact h.symm
  mem_lattice g := by
    have h := e.mem_lattice (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group)
    have heq : NilpotentLieBCHGroup.map (hM := E.filtration.lowerCentralSeries_eq_bot)
        e.toLieEquiv.toLieHom (⟨e.toLieEquiv.symm g.coord⟩ : D.filtration.Group) = g := by
      apply NilpotentLieBCHGroup.ext
      exact e.toLieEquiv.apply_symm_apply g.coord
    rw [heq] at h
    exact h.symm

end NativeModelEquiv

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

open scoped TensorProduct

theorem realificationLieEquiv_inverse
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : L ≃ₗ⁅ℚ⁆ M) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom e.symm.toLieHom (realificationLieHom e.toLieHom x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change a ⊗ₜ[ℚ] e.symm (e x) = a ⊗ₜ[ℚ] x
    rw [LieEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E)

noncomputable def realGroupEquiv : D.RealGroup ≃* E.RealGroup :=
  { realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.toLieHom with
    invFun := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) e.toLieEquiv.symm.toLieHom
    left_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv g.coord
    right_inv g := by
      apply NilpotentLieBCHGroup.ext
      exact realificationLieEquiv_inverse e.toLieEquiv.symm g.coord }

theorem symm_realGroupEquiv_apply (g : D.RealGroup) :
    e.symm.realGroupEquiv (e.realGroupEquiv g) = g :=
  e.realGroupEquiv.symm_apply_apply g

theorem real_lattice_le : D.realLattice ≤ E.realLattice.comap e.realGroupEquiv.toMonoidHom := by
  apply realificationMap_subgroup e.toLieEquiv.toLieHom D.lattice E.lattice
  intro g hg
  exact (e.mem_lattice g).mpr hg

noncomputable def spaceMap : D.Space → E.Space :=
  cosetMap D.realLattice E.realLattice e.realGroupEquiv.toMonoidHom e.real_lattice_le

theorem spaceMap_mk (g : D.RealGroup) :
    e.spaceMap (QuotientGroup.mk g) = QuotientGroup.mk (e.realGroupEquiv g) := rfl

theorem symm_spaceMap_apply (x : D.Space) : e.symm.spaceMap (e.spaceMap x) = x := by
  induction x using Quotient.inductionOn with
  | _ g =>
    rw [e.spaceMap_mk, e.symm.spaceMap_mk, e.symm_realGroupEquiv_apply]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem spaceMap_lipschitz :
    letI := D.metricSpace
    letI := E.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) e.spaceMap := by
  have hmatrix : ∀ k i, RationalHeightLE (E.basis.repr (e.toLieEquiv (D.basis i)) k) 1 := by
    intro k i
    rw [e.map_basis]
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> norm_num [RationalHeightLE]
  have hh :=
    lipschitz_realificationMap_quotient D.basis E.basis e.toLieEquiv.toLieHom
      D.lattice E.lattice (fun g hg => (e.mem_lattice g).mpr hg)
      D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid 1 hmatrix
  simp only [Fintype.card_fin, Nat.cast_one] at hh
  convert hh using 1
  rfl

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def mapOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    E.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (VectorPolynomial.map ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log)
    (D.filtration.realification.adapted_map E.filtration.realification
      ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ)
      (D.filtration.realificationLieHom_mem_layer E.filtration e.toLieEquiv.toLieHom
        (fun n x hx => (e.mem_layer n x).mpr hx)) w g.adapted)

theorem mapOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit g) =
      e.realGroupEquiv (D.filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval_map (fun i => (x i : ℚ))
    ((realificationLieHom e.toLieEquiv.toLieHom).toLinearMap.restrictScalars ℚ) g.log

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CommonVariableDimensionNiltests
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M s d}
  (e : NativeModelEquiv D E) {w : σ → ℕ}

noncomputable def transport (T : D.Niltest w) : E.Niltest w where
  orbit := e.mapOrbit T.orbit
  observable := T.observable ∘ e.symm.spaceMap
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le x := T.norm_le _
  lipschitz := by
    let := D.metricSpace
    let := E.metricSpace
    exact T.lipschitz.comp e.symm.spaceMap_lipschitz

theorem transport_eval (T : D.Niltest w) (x : σ → ℤ) : (e.transport T).eval x = T.eval x := by
  change T.observable (e.symm.spaceMap
    (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval w x (e.mapOrbit T.orbit)))) = _
  rw [e.mapOrbit_eval, ← e.spaceMap_mk, e.symm_spaceMap_apply]
  rfl

theorem transport_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (e.transport T).UnitIntervalValued := fun x => hT (e.symm.spaceMap x)

theorem transport_complexity (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hT : T.ComplexityLE p) (hE : E.GeometryComplexityLE p) :
    (e.transport T).ComplexityLE (p + (p + 2) ^ 2) := by
  have hK : (coordinateLipschitzBound d d 1 : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hE.1 (Real.one_le_exp_iff.mpr hp)
  have h1 : 1 ≤ Real.exp ((p + 2) ^ 2) := Real.one_le_exp_iff.mpr (sq_nonneg _)
  refine ⟨hE.mono E (le_add_of_nonneg_right (sq_nonneg _)), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * coordinateLipschitzBound d d 1) ≤ p + (p + 2) ^ 2
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * coordinateLipschitzBound d d 1 ≤
        (2 + (T.normBound : ℝ)) * Real.exp ((p + 2) ^ 2) +
          (T.lipBound : ℝ) * Real.exp ((p + 2) ^ 2) :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hK T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp ((p + 2) ^ 2) := by ring
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) :=
      mul_le_mul_of_nonneg_right (Niltest.observable_budget hT) (Real.exp_pos _).le
    _ = Real.exp (p + (p + 2) ^ 2) := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.NativeModelEquiv

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SingleRefilteredKernel
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

noncomputable def nativeRefilteredMap :=
  optionProductMap (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i : {i : ι // i ≠ a} => refilteredComponentMap D W i.val)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let T := nativeRefilteredTarget D a W E Q
  let N := ∀ j : Option {i : ι // i ≠ a}, optionLieSpace
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1))
    (fun i : {i : ι // i ≠ a} => L i.val) j
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  letI := realification_moduleTopology_t2 T.basis
  ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
    (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
    (Λ.subgroupOf T.lattice).FiniteIndex ∧
    (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
    ∃ (B : ℕ) (hB : 0 < B)
      (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
      (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
      let V := T.withLattice Λ B hB hin hout
      V.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : V.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := V.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              (∀ x, ‖v x‖ ≤ 1) ∧ ∀ x : E.RealGroup,
              v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := T.filtration.lowerCentralSeries_eq_bot) (nativeRefilteredMap D a W E) x)) =
              S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                (refilteredComponentMap D W a) x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def LowerRefilteredRecoveryFamily (p : ℝ) (q k : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I, L i.val) (s + 1)
        (Fintype.card (Σ i : I, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      ∀ {J : Type u} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (eta j)) x = 0) →
        ∀ l r : (D a).RealGroup,
          (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
            (letI := (D a).metricSpace; LipschitzWith ℓ S) →
            (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
            (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
            ∃ (v : Q'.Space × Z.Space → ℂ) (K : ℝ≥0),
              (K : ℝ) ≤ Real.exp cost ∧
              (letI := Q'.metricSpace; letI := Z.metricSpace; LipschitzWith K v) ∧
              (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
              ∀ x : E.RealGroup,
                v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Q'.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x),
                  QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := Z.filtration.lowerCentralSeries_eq_bot)
                    (liePiMap (fun i : I => refilteredComponentMap D W i.val)) x)) =
                  S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := (D a).filtration.lowerCentralSeries_eq_bot)
                    (refilteredComponentMap D W a) x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def LowerRefilteredCyclicExpansionSpec
    (p : ℝ) (q k : ℕ) (cost : ℝ) (C : ℕ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ Z : RationalFilteredNilmanifold (∀ i : I₀, L i.val) (s + 1)
        (Fintype.card (Σ i : I₀, Fin (d i.val))),
      Z.filtration = Z₀.filtration ∧ Z.basis = Z₀.basis ∧ Z.lattice ≤ Z₀.lattice ∧
      Z.GeometryComplexityLE cost ∧
      letI := Z.metricSpace
      let w := fun _ : Unit => 1
      let φ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
      let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Z.filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
      ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
          realifyFunctional (piFrequency (freq j)) x = 0) →
        ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
          (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) {ρ η : ℝ},
          0 < ρ → 0 ≤ η →
          (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
          (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
          ∀ (S : ZMod N → (D a).Niltest w),
            (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
            (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
              (∀ j, realifyFunctional (freq j a) z.coord = 0) →
              ∀ x, (S h).observable (z • x) = (S h).observable x) →
            ∀ (slow middle rat : ZMod N → ((D a).filtration.realification.adaptedPolynomialFiltration w).Group)
              (κ : ZMod N → (D a).RealGroup)
              (g : ZMod N → E.filtration.realification.PolynomialOrbit w),
              (∀ h, κ h ∈ (D a).realLattice) →
              (∀ h, slow h * middle h * rat h * (D a).filtration.realification.adaptedConstantGroupHom w (κ h) =
                ⟨⟨(S h).orbit.log, (S h).orbit.property⟩⟩) →
              (∀ h, (D a).filtration.PolynomialSlowBound (D a).basis w
                (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) (slow h)) →
              (∀ h x, (D a).filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (middle h) =
                φ (E.filtration.realification.polynomialOrbitEval w x (g h))) →
              ∀ (anchor : I → ZMod N → ℝ) (r₀ : I → ZMod N → (D a).RealGroup),
                (∀ i h, |anchor i h| ≤ N) →
                (∀ i h b, |((D a).basis.baseChange ℝ).repr
                  ((D a).filtration.adaptedPolynomialRealValueHom w (fun _ => anchor i h) (slow h)).coord b| ≤
                    Real.exp ((p + 2) ^ k)) →
                (∀ i h, ((D a).basis.baseChange ℝ).equivFun (r₀ i h).coord ∈ realDenominatorGrid q) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  |(x.val : ℝ) - anchor i h| ≤ (N : ℝ) * ρ) →
                (∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
                  (QuotientGroup.mk ((D a).filtration.adaptedPolynomialRealValueHom w
                    (fun _ => (x.val : ℝ)) (rat h)) : (D a).Space) = QuotientGroup.mk (r₀ i h)) →
                (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                  0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                  dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                    (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
                    (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
                      (fun _ => (y.val : ℤ)) (g h)))) ≤ η) →
                ∃ U : I → J → ZMod N → Q'.Niltest w,
                  (∀ i j h, (U i j h).UnitIntervalValued) ∧
                  (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                  (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                    ∀ x, (U i j h).eval x = 0) ∧
                  ∃ err : ZMod N → ZMod N → ℝ,
                    (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                      (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                    ∀ h, (𝔼 x, |err h x|) ≤
                      Real.exp ((p + C) ^ C) * ρ + Real.exp cost * η + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

def AllocatedMarkedDiagramRecoveryCovers (k q : ℕ) (p cost : ℝ) : Prop :=
  ∃ Q' : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ,
    Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
    Q'.GeometryComplexityLE cost ∧
    ∃ F' : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF,
      F'.filtration = Fref.filtration ∧ F'.basis = Fref.basis ∧ F'.lattice ≤ Fref.lattice ∧
      F'.GeometryComplexityLE cost ∧
      let K : ℝ≥0 := ⟨Real.exp cost, (Real.exp_pos _).le⟩
      letI := Q'.metricSpace
      letI := F'.metricSpace
      let diagram := Dref.markedTopQuotientDiagram F'
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q'
      ∀ a r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
        ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
          (letI := D.metricSpace; LipschitzWith ℓ S) →
          (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
          let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
            (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
          ∀ x : Dref.RealGroup,
            positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Conclusion

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

section Conclusion

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
      Dref.filtration.layerIdeal (s + 1)))]

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem NativeGridRightDictionary.markedTopQuotient_recovery
    {inputDenominator : ℕ} {bound : ℝ}
    (dictionary : D.NativeGridRightDictionary inputDenominator bound)
    (K : ℝ≥0) (observable : D.Space → ℂ) (a r : D.RealGroup)
    (hr : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid inputDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ j : Fin dictionary.count,
        let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * dictionary.representative j))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let frozen := fun source : Dref.RealGroup => observable (QuotientGroup.mk
      (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source * r))
    ∀ source, positiveImageSlice diagram K frozen
      (diagram source).2 (diagram source).1 = frozen source := by
  let := Q.metricSpace
  let := Fref.metricSpace
  dsimp only at hrecovery ⊢
  obtain ⟨label, hlabel⟩ := dictionary.labeling (fun _ : Unit => r) (fun _ => hr)
  let inclusion : Dref.RealGroup → D.RealGroup :=
    realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl
  have hfrozen : (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * r))) =
      (fun source : Dref.RealGroup => observable (QuotientGroup.mk
        (a * inclusion source * dictionary.representative (label ())))) := by
    funext source
    exact congrArg observable ((hlabel ()).2 (a * inclusion source))
  change ∀ source, positiveImageSlice
    (Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (fun x => observable (QuotientGroup.mk (a * inclusion x * r)))
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).2
    ((Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) source).1 =
      (fun x => observable (QuotientGroup.mk (a * inclusion x * r))) source
  rw [hfrozen]
  exact hrecovery (label ())

end Conclusion

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_correlating_vertical_mode (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨η, U, hU, hOrbit, hheight, hchar, hint, _, hCorr⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp hT hρ hρp hQ f hf hcorr
  exact ⟨η, U, hU, hOrbit, hheight, hchar, hint, hCorr⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_detection_vertical_mode (a : ℕ)
    (ha : ∀ q : ℝ, 0 ≤ q → verticalDecompositionBudget q ≤ (q + a) ^ a)
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w), U.ComplexityLE (p + 1) ∧
      Real.exp (-boxModeBudget a p) ≤ ‖finiteCorrelation Q f U.eval‖ ∧
      ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have herror : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div]; simp [Real.exp_neg]
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg p)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨η, U, hU, _, _, hvert, _, hcorrU⟩ :=
    T.exists_correlating_vertical_mode hp1 (hT.mono (by linarith)) (Real.exp_pos (-p))
      herror hQ f hf hcorr
  refine ⟨η, U, hU, ?_, hvert⟩
  apply le_trans _ hcorrU
  have hv := ha (p + 1) hp1
  calc
    _ ≤ Real.exp ((-p - verticalDecompositionBudget (p + 1)) - 1) := by
      apply Real.exp_le_exp.mpr
      unfold boxModeBudget
      linarith
    _ ≤ Real.exp (-p - verticalDecompositionBudget (p + 1)) / 2 := exp_sub_one_le_half_exp _
    _ = _ := by rw [Real.exp_sub]; ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

def NativeCyclicRecoverySpec (s k C : ℕ) : Prop :=
    ∀ {L : Type u} {M : Type v} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid l),
            let Q := D.withLattice Λ l hl hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group,
              E.filtration.PolynomialRationalGrid E.basis (fun _ : Unit => 1) q R →
              ∃ z : (Unit → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (Unit → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (N : ℕ) [NeZero N]
                      (S : (E.filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group),
                      E.filtration.PolynomialSlowBound E.basis (fun _ : Unit => 1)
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ k)) S →
                      (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom (fun _ : Unit => 1)
                        (fun i => (x i : ℝ)) S) →
                      ∀ {I J : Type w} (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
                        (label : I → ZMod P) {ρ K : ℝ}, 0 < ρ →
                        (∀ i x, 0 ≤ A i x) →
                        (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                        (∀ i x y, 0 < A i x → 0 < A i y →
                          dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                        ∀ (h : ZMod N) i j x y,
                          x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                          0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                          dist (QuotientGroup.mk (f (fun _ => (x.val : ℤ))) : Q.Space)
                            (QuotientGroup.mk (f (fun _ => (y.val : ℤ)))) ≤ K * ρ →
                          dist (QuotientGroup.mk (ψ (b (fun _ => (x.val : ℤ)))) : E.Space)
                            (QuotientGroup.mk (ψ (b (fun _ => (y.val : ℤ))))) ≤
                              Real.exp ((p + C) ^ C) * (K + 1) * ρ

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedComplementInputPartition
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedComplementInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ s d₀),
      let Z₀ := pi (optionComplementFactors D₀ Z)
      ∀ (Γ : Subgroup Z₀.filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates Z₀.basis Γ)
        (houtΓ : bchSubgroupCoordinates Z₀.basis Γ ⊆ denominatorGrid mΓ),
      let W := Z₀.withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      let KC := ∀ j : {j : Option (κ ⊕ ι) // j ≠ none}, optionLieSpace L₀ KL j.val
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] KC)
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] KC)
      letI := realification_moduleTopology_t2 Z₀.basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → W.GeometryComplexityLE p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => ((optionComplementFactors D₀ Z) i).filtration)
              (optionComplementOrbits D₀ Z (sumOrbits E Q g qSq))
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelFreezing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L Q : Type*} [LieRing L] [LieAlgebra ℚ L] [Group Q] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_freeze_marked_kernel_factors
    (T : D.Niltest w) (π : D.RealGroup →* Q) (ρ : Q → D.RealGroup)
    (hρ : Function.RightInverse ρ π)
    (a b r : D.RealGroup) (aF rF : Q)
    (kE kR : D.RealGroup) (hkE : π kE = 1) (hkR : π kR = 1)
    (hcoset : (QuotientGroup.mk ((ρ rF)⁻¹ * r) : D.Space) = QuotientGroup.mk kR) :
    π (kE * ρ aF) = aF ∧ π (ρ rF * kR) = rF ∧
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ‖T.observable (QuotientGroup.mk (a * b * r)) -
        T.observable (QuotientGroup.mk ((kE * ρ aF) * b * (ρ rF * kR)))‖ ≤
          (T.lipBound : ℝ) * dist (a * (ρ aF)⁻¹) kE := by
  let := rightMetricSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hright : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk (ρ rF * kR) := by
    have h := congrArg (fun x : D.Space => (ρ rF) • x) hcoset
    change QuotientGroup.mk (ρ rF * ((ρ rF)⁻¹ * r)) =
      (QuotientGroup.mk (ρ rF * kR) : D.Space) at h
    simpa only [mul_inv_cancel_left] using h
  refine ⟨by rw [map_mul, hkE, hρ, one_mul], by rw [map_mul, hkR, hρ, mul_one], ?_⟩
  have hfreeze := T.observable_freeze_factors a (kE * ρ aF) b r (ρ rF * kR) hright
  have hdist : dist a (kE * ρ aF) = dist (a * (ρ aF)⁻¹) kE := by
    rw [← dist_mul_right a (kE * ρ aF) (ρ aF)⁻¹, mul_inv_cancel_right]
  exact hfreeze.trans_eq (congrArg (fun z : ℝ => (T.lipBound : ℝ) * z) hdist)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerPrescribedScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerSamplerTailScaleFloor (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  32 * (probabilityProfileLipschitz : ℝ) *
    ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1) / (σ j * R j)

theorem layerSamplerTailWidth_of_scaleFloor
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {S0 : ℕ} (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0 := by
  intro j
  have hj := (div_le_iff₀ (mul_pos (hσ j) (hR j))).mp (hfloor j)
  change 8 * (probabilityProfileLipschitz : ℝ) ≤
    (σ j * R j / (4 * ((Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1))) * S0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  convert hj using 1 <;> ring

theorem layerSamplerTailScaleFloor_le_exp
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t) :
    ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ Real.exp (a + c + r + t) := by
  intro j
  calc
    _ = (8 * (probabilityProfileLipschitz : ℝ)) *
        (4 * ((Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1)) *
        (R j)⁻¹ * (σ j)⁻¹ := by
      unfold layerSamplerTailScaleFloor
      field_simp
      ring
    _ ≤ Real.exp a * Real.exp c * Real.exp r * Real.exp t := by
      have hRj := (hR j).le
      have hσj := (hσ j).le
      gcongr <;> first
        | exact hprofile
        | exact hcount j
        | exact hradius j
        | exact htolerance j
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_add]

variable [∀ j, IsEmpty (Fin (n j))]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

def emptyLayerSamplerScale (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    LayerSamplerScale (G := G) B U b R σ where
  value := S0
  positive := hS0
  width := hwidth
  gap := fun _ i => isEmptyElim i

@[simp] theorem emptyLayerSamplerScale_value (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    (emptyLayerSamplerScale B U b S0 hS0 hwidth).value = S0 := rfl

def emptyLayerSamplerScaleOfFloor
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScale B U b S0 hS0 (layerSamplerTailWidth_of_scaleFloor B hR hσ hfloor)

@[simp] theorem emptyLayerSamplerScaleOfFloor_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    (emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 hfloor).value = S0 := rfl

def emptyLayerSamplerScaleOfExp
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 (fun j =>
    (layerSamplerTailScaleFloor_le_exp B hR hσ hprofile hcount hradius htolerance j).trans hS)

@[simp] theorem emptyLayerSamplerScaleOfExp_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    (emptyLayerSamplerScaleOfExp B U b hR hσ hprofile hcount hradius htolerance
      S0 hS0 hS).value = S0 := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace ResidueBoxSlice

theorem fin_mean_eq_translated_zero {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (T : ResidueBoxSlice P q) (f : (K → ℤ) → ℂ) :
    (𝔼 t : (∀ k, Fin (T.length k)), f (T.fullSlicePointInIntegerBox t).val) =
      𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
        f (fun k => (q : ℤ) * x k + T.start k) := by
  have hzero : translatedIntegerBox (0 : K → ℤ) T.length = integerBox T.length := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  rw [hzero, integerBox_expect_eq_fin]
  apply Finset.expect_congr rfl
  intro t _
  congr 1
  funext k
  simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, add_comm]

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

theorem exists_uniform_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    {p : ℝ} (hdim : (Fintype.card J : ℝ) ≤ p) :
    ∃ b : Basis (Fin (finrank ℝ Wᗮ)) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ z, ‖normalizedOrthogonalChart W b z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ z, ‖(normalizedOrthogonalChart W b).symm z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      0 ≤ mixedDensityCovolumeRatio W b ∧
      mixedDensityCovolumeRatio W b ≤ Real.exp (allocatedUniformChartLog p) := by
  have hn : finrank ℝ Wᗮ ≤ Fintype.card J := by
    simpa only [finrank_euclideanSpace] using Wᗮ.finrank_le
  have hnp : (finrank ℝ Wᗮ : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hdim
  have hlog : 20 * ((finrank ℝ Wᗮ : ℝ) + 1) ^ 3 ≤ allocatedUniformChartLog p := by
    unfold allocatedUniformChartLog
    gcongr
  have he := Real.exp_le_exp.mpr hlog
  obtain ⟨b, hb, _, hf, hi, _, hv⟩ := exists_quantitative_projected_chart W
  exact ⟨b, hb, fun z => (hf z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    fun z => (hi z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    (mixedDensityCovolumeRatio_pos W b).le, hv.trans he⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3
open VectorPolynomial

structure PreparedRelativeInitializerScalarInputs
    {X : Type*} {s D E q : ℕ} (oldPatch : PolynomialPatch X s (D + E))
    (coordinates : Fin q → ℕ) (variableCount : ℕ)
    (p pRelative precisionBudget chartLog a Λ : ℝ) (n₀ d₀ : ℕ) : Prop where
  hpInit : 2 ≤ pRelative
  hDlog : (D : ℝ) ≤ Real.exp pRelative
  hqlog : (q : ℝ) ≤ Real.exp pRelative
  hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp pRelative
  hNlog : ∀ j, (coordinates j : ℝ) ≤ Real.exp pRelative
  hClog : ∀ _j : Fin q, Real.exp chartLog ≤ Real.exp pRelative
  hgainlog : Real.exp (-pRelative) ≤ Real.exp (-p)
  hδearly : Real.exp (-precisionBudget) ≤ Real.exp (-(3 * pRelative + 130))
  hpchild : pRelative + 2 ≤ pRelative + 2
  ha : Real.exp (-pRelative) ≤ a
  habsolute : RelativePatchAbsoluteRule s n₀ pRelative a Λ d₀
  hDim : (variableCount : ℝ) ≤ pRelative + 2
  hOldComplexity : relativePatchComplexity oldPatch ≤ pRelative + 2
  hgain1 : Real.exp (-p) ≤ 1
  hδ : 0 ≤ Real.exp (-precisionBudget)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFiniteMarkedFactorParameters
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def MarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m : ℕ, 0 < M ∧ 0 < m ∧ (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧
    ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (RF : (F.realification.adaptedPolynomialFiltration w).Group),
      D.filtration.PolynomialRationalGrid D.basis w l R →
      F.PolynomialRationalGrid c w l RF →
      D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
      ∃ r : (σ → ZMod M) → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
        ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
              ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
            r (fun j => (x j : ZMod M)) * γ ∧
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                (D.filtration.filteredRealPolynomialSection F w S hS RF) *
              r (fun j => (x j : ZMod M)) * γ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem MarkedRationalFactorFreezing.finite_enumeration
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) {B p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : B ≤ Real.exp p)
    (hfreeze : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) :
    ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
      (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
        ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
          (RF : (F.realification.adaptedPolynomialFiltration w).Group),
          D.filtration.PolynomialRationalGrid D.basis w l R →
          F.PolynomialRationalGrid c w l RF →
          D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
          ∃ label : (σ → ZMod M) → Fin n,
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
                center (label (fun j => (x j : ZMod M))) * γ ∧
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                    (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                  center (label (fun j => (x j : ZMod M))) * γ := by
  classical
  obtain ⟨M, m, hM, hm, hMb, hmb, hfactor⟩ := hfreeze
  have hB0 : 0 ≤ B := (Nat.cast_nonneg m).trans hmb
  obtain ⟨n, hn, hnb, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration_exp (D.basis.baseChange ℝ)
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ) m hm hp hB0
      (by simpa only [Fintype.card_fin] using hd) (hmb.trans hB) hB
  refine ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenters, ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfactor R RF hR hRF hmark
  choose label hlabel using fun a => hcover (r a) (hr a).1 (hr a).2.1 (hr a).2.2
  refine ⟨label, ?_⟩
  intro x
  obtain ⟨γ, hγ, hKR, hRfac⟩ := hfac x
  refine ⟨γ, hγ, ?_, ?_⟩
  · simpa only [hlabel] using hKR
  · simpa only [hlabel] using hRfac

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem MarkedRationalFactorFreezing.mono
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {B B' : ℝ}
    (h : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) (hBB' : B ≤ B') :
    D.MarkedRationalFactorFreezing F c φ hφ w S hS l B' := by
  obtain ⟨M, m, hM, hm, hMB, hmB, hfreeze⟩ := h
  refine ⟨M, m, hM, hm, hMB.trans hBB', hmB.trans hBB', ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfreeze R RF hR hRF hmark
  exact ⟨r, fun a => ⟨(hr a).1, fun i => ((hr a).2.1 i).trans hBB', (hr a).2.2⟩,
    hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def MarkedSlowFactorFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    ∃ center : (Fin d → Fin (N + 1)) → D.RealGroup,
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
      (∀ j i, |(D.basis.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        ∃ label : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)),
          ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ Tbox i) →
            (∀ i, |v i - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
            dist (D.filtration.adaptedPolynomialRealValueHom w v
              (E * (D.filtration.filteredRealPolynomialSection F w S hS EF)⁻¹))
              (center (label j)) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    ∃ center : Fin n → D.RealGroup,
      (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
      ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ label : (σ → ZMod M) → Fin n,
          ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
              center (label (fun j => (x j : ZMod M))) * γ ∧
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                center (label (fun j => (x j : ZMod M))) * γ

theorem MarkedSlowFactorFreezing.mono_bound
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {Tbox : σ → ℝ} {A ε B B' : ℝ}
    (h : D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B) (hBB' : B ≤ B') :
    D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B' := by
  obtain ⟨N, Q, hN, hQ, hNc, hQc, center, hmark, hcap, hfreeze⟩ := h
  exact ⟨N, Q, hN, hQ, hNc.trans hBB', hQc.trans hBB', center, hmark,
    fun j i => (hcap j i).trans hBB', hfreeze⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

noncomputable def FixedAffineResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ (scale : ℤ) (shift : σ → ℤ),
    FixedResidueDescent D W V (fun _ : σ => 1)
      (D.filtration.realification.scalarAffineAdaptedHom (scale : ℚ) (fun i => (shift i : ℚ)) b)
      (V.filtration.realification.scalarAffineOrbitHom (scale : ℚ) (fun i => (shift i : ℚ)) child)
      p q P hP C a cost

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def HasFixedAffineResidueChild {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
      (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
    E.filtration = D.filtration.gradedRefiltration W ∧
    ∃ (n : ℕ) (_hn : n ≤ d)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n),
      Q.filtration = E.filtration.quotientTop ∧
      let H := D.filtration.gradedRefiltrationSubalgebra W
      let N := H ⧸ E.filtration.layerIdeal (s + 1)
      let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
      let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
      let := realification_moduleTopology_t2 Q.basis
      ∃ V : RationalFilteredNilmanifold N s n,
        V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
        ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
          DegreeLE (fun _ => 1) s child.log ∧
          FixedAffineResidueDescent D W V b child p q P hP C a cost

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedExternalKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_prescribed_marked_orbit
    (tests : X → D.Niltest w) (htests : ∀ x, (tests x).UnitIntervalValued)
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (marked : G.realification.PolynomialOrbit v)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log = marked.log)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((tests (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit v,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      ∃ z : D.RealGroup,
        restored = D.filtration.realification.constantGroupOrbit v z * orbit ∧
        z.coord ∈ K.baseChange ℝ ∧
        NilpotentLieBCHGroup.realificationMap
          (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ z = 1 ∧
        (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
          ((tests x).withOrbit restored).normBound = (tests x).normBound ∧
          ((tests x).withOrbit restored).lipBound = (tests x).lipBound ∧
          ((tests x).withOrbit restored).UnitIntervalValued ∧
          ∀ p, ((tests x).withOrbit restored).ComplexityLE p ↔ (tests x).ComplexityLE p) ∧
        ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
          δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
          ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
            (fun j => weight a j * ((tests (physical a j)).withOrbit restored).eval
              (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_restored_orbit tests htests K hK orbit
      outer H hH localLaw physical point weight hB hδ hweight hscore
  have hzmark : NilpotentLieBCHGroup.realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1 :=
    (NilpotentLieBCHGroup.coord_mem_realificationKernel_iff
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z).mp
        (Submodule.baseChange_mono ℝ hkernel hz)
  let restored := D.filtration.realification.constantGroupOrbit v z * orbit
  have hrestored : map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      restored.log = marked.log :=
    (D.filtration.map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
      G φ v orbit z hzmark).trans hmark
  refine ⟨restored, hrestored, z, rfl, hz, hzmark, ?_, H', hsub, hpos, hmass, ?_⟩
  · intro x
    exact ⟨rfl, rfl, rfl, htests x, fun _ => Iff.rfl⟩
  · intro a ha
    exact hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end


