-- Prove2me | Definitions.Def_OAIE3v2B217
-- name    : OAIE3v2B217
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:18.140588+00:00
-- url     : https://prove2.me/theorems/d488cc80-9a92-476a-bdaa-d38c3687d8a8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 221 of 311
-- statement:
--   Definitions bundle 221 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B189`, `OAIE3v2B191`, `OAIE3v2B194`, `OAIE3v2B195`, `OAIE3v2B300` of this split.
--
--   Modules: `Dynamics/PreparedJointPhysicalScalarBudget.lean`, `Dynamics/PreparedNestedEndpointReturnBudget.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Fourier/AllocatedNormalizedTorusCutoff.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Geometry/AllocatedRowSlicedIdealCoordinates.lean`, `Geometry/AllocatedSupportedSlicedNaturalCap.lean`, `Geometry/JointExceptionalSpatialWidthBudget.lean`, `Geometry/PreparedModularCanonicalDetectorGeometricBoundsGeneral.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Lattices/AllocatedModularRankIntegerDecay.lean`, `Lattices/AllocatedPhysicalIntegerRankLaw.lean`, `Lattices/ForecastOriginalSampleResidueFactor.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedKernelScaleWithCutoff.lean`, `Linear/AllocatedModularRankActualRead.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/AllocatedModularRankFullProductLaw.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/AllocatedCenteredConditionalPolynomial.lean`, `Polynomial/AllocatedModularRankTaggedPolynomials.lean`, `Polynomial/CandidateNestedDegreeNetSchedule.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Probability/AllocatedNormalizedConditionalHaar.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedClippedFullGridGlobal.lean`, `Sampling/AllocatedGridlessProfileBound.lean`, `Sampling/JointMeasureProductiveNarrowSampler.lean`, `Sampling/PreparedConcreteSlicedForecastModelLogs.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B189
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195
import Definitions.Def_OAIE3v2B300

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_conditional_event_le
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
    (width : K × I → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus cells width D)
    (hlocal : ∀ a, 0 < selectedResidueDensityMass modulus cells width (D a))
    (event : B → (K × I → ℤ) → Prop) {ε : ℝ}
    (hbound : ∀ a,
      (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ
        (D a) (hD0 a) (hlocal a) z).toReal * (if event a z then 1 else 0)) ≤ ε) :
    (selectedJointFiniteLaw A hA modulus cells width hwidth hZ D hD0 hD).mean
      (fun z => if event z.1.val z.2.val then 1 else 0) ≤ ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus cells width hwidth hZ
  have hlocal' (a : A) : 0 < q.mean (fun z => D a.val z.val) := by
    rw [selectedResidueFiniteLaw_densityMass]
    exact hlocal a.val
  have hglobal : 0 < (p.prod q).mean (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells width hwidth hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hD
  apply FiniteProbabilityWeights.prod_reweightPositive_mean_le_of_conditional p q
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val) hglobal hlocal'
    (fun z => if event z.1.val z.2.val then 1 else 0)
  intro a
  change (selectedResidueTiltedFiniteLaw modulus cells width hwidth hZ
    (D a.val) (hD0 a.val) (hlocal a.val)).mean (fun z => if event a.val z.val then 1 else 0) ≤ ε
  rw [selectedResidueTiltedFiniteLaw_mean modulus cells width hwidth hZ (D a.val)
    (hD0 a.val) (hlocal a.val) (fun z => if event a.val z then 1 else 0)]
  exact hbound a.val

end Erdos3

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

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

include hR hσ hσ1 henormous in
theorem allocatedKernelProfile_sum_pos :
    0 < coefficientWeightSum (affineProductProfile (centers ∘ reindex) (widths ∘ reindex)) (scales ∘ reindex) := by
  rw [affineCoefficientWeightSum_reindex]
  exact allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

noncomputable def allocatedSlicedCubeSource
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) : ℂ :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    (fun cube =>
      (𝔼 base ∈ bases, ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences
              (commonStridePoint c step (fun k => (cube k none : ℤ)))
              (fun j k => (step : ℤ) * (cube k (some j) : ℤ)) base z) *
            (baseDensity base z : ℂ))) / (selectedJointDensityMass bases stride cells widths baseDensity : ℂ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedFixedScale_center_mixture_compare
    {m : ℕ} {X G : Type*} [Fintype X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
    (hlocal : ∀ center, 0 < selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base))
    {P : ℝ}
    (hclose : ∀ center, |selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base) - 1| ≤
        3 * positiveProjectionAccuracy P)
    (hcomparison : ∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ), (∀ v, ‖φ v‖ ≤ 1) →
      let sample := fun z => affineSampleCoefficientTorus U p hm
        (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
      let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => D₀ (coefficientConstantCenter U center + x))
        (coefficientEvaluationTorus U root (sample z))
      ‖(∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
        (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base z : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤
        3 * positiveProjectionAccuracy P) :
    ∀ ψ : (X → ℝ) → ℂ, (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base)
          (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
          (hlocal center) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ 6 * positiveProjectionAccuracy P := by
  intro ψ hψ
  let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hcap := allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
  have hbound (x) : ‖D₀ x‖ ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcap x).1]
    exact (hcap x).2
  let D := fun center => allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base
  let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    affineSampleCoefficientTorus U p hm
    (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
  let F := fun center z => coefficientFiberAverage U μ root
    (fun x => D₀ (coefficientConstantCenter U center + x))
    (coefficientEvaluationTorus U root (sample z))
  apply selectedResidue_center_mixture_compare μ stride T W hW hZ D
    (fun z => allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S p hm base z)
    (fun center => allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    hlocal F
    (fun z => coefficientMixedFiber_integrable U μ D₀ hspec.1 hbound root _)
    (fun z => (coefficientMixedFiber_average U μ D₀ hspec.1 hbound root _).trans hspec.2.2.2.1)
    (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _)
  intro center
  have hraw := hcomparison center (fun v => ψ (v - (fun i => (base i : ℝ))))
    (fun _ => hψ _)
  dsimp only at hraw
  simp only [add_sub_cancel_left] at hraw
  have herr := selectedResidueDensityPMF_error_of_bounded_test stride T W hW hZ (D center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    (hlocal center) (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _) hraw (hclose center)
  exact herr.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixedScale_centered_oneSite_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleCenteredOneSiteStatement m A := by
  obtain ⟨A₀, _, hcompare⟩ := exists_affine_oneSite_density_comparison m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths sample D₀
  let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
  let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hcap := allocatedCoefficientDensity_bounds B U basis hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
  have hbound (x) : ‖D₀ x‖ ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcap x).1]
    exact (hcap x).2
  have hlocal (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ) (hφ : ∀ u, ‖φ u‖ ≤ 1) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        ‖(∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
            (allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center base z : ℂ))) -
          (∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
              ((coefficientFiberAverage U μ root
                (fun x => D₀ (coefficientConstantCenter U center + x))
                (coefficientEvaluationTorus U root (sample base z)) : ℝ) : ℂ)))‖ ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    let ψ : (X → ℝ) → ℂ := fun v => φ ((fun i => (base i : ℝ)) + v)
    have hψ (v) : ‖ψ v‖ ≤ 1 := hφ _
    obtain ⟨hZ, he⟩ := hcompare hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      root (fun i => Fin.elim0 i) (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
      (fun s k => by
        have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
        simpa only [affineSite, hs, Finset.sum_empty, add_zero] using (hroot k).trans hExp)
      frequency (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      (fun a => coeff a * coefficientTorusCharacter U (frequency a) (coefficientConstantCenter U center))
      (Real.exp_nonneg Q) le_rfl
      (by rw [coefficientFourier_translate_norm]; exact hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank)
      0 (by simp) (fun _ => ψ) (fun _ v => hψ v) T hT widths hwidths hwidthLower
      (fun x => D₀ (coefficientConstantCenter U center + x))
      (bounded_coefficient_translate_fiber_integrable U μ D₀ hspec.1 hbound _ root)
      hη.le (fun x => by
        rw [norm_sub_rev]
        exact coefficientFourier_translate_approx U D₀ frequency coeff
          happ (coefficientConstantCenter U center) x)
    refine ⟨hZ, ?_⟩
    have hsample (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
        affineSampleCoefficientTorus U (pa base) (hma base) (fun k i => (z (k,i) : ℝ)) =
          sample base z := affineSampleCoefficientTorus_joint_frame U p hm base z
    simp only [layeredSiteWeight_physical, hsample] at he
    exact he.trans_eq (by ring)
  obtain ⟨hZ, _⟩ := hlocal 0 0 (by intro k; simpa using Real.exp_nonneg P) 0
    (fun _ => 0) (fun _ => by simp)
  refine ⟨hwidths, hZ, ?_⟩
  intro base root hroot center φ hφ
  exact (hlocal base root hroot center φ hφ).choose_spec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem narrow_sampler_width_bounds {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) :
    0 < spatialWidthFraction (2*P) (ξ*τ) ∧
    1/spatialWidthFraction (2*P) (ξ*τ) ≤ Real.exp (spatialSamplingBudget (2*P)) ∧
    ∀ z : Option (G ⊕ J) × X,
      spatialWidthFraction (2*P) (ξ*τ) * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨spatialWidthFraction_pos (2*P) hτξ,
    spatialWidthFraction_inv_le h2P hτξ hτξP, ?_⟩
  intro z
  exact (spatialWidthFraction_le_allocated_width h2P hW
    (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτξ.le N z).trans
    (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedJointPhysicalScalarBudget
namespace OAI

section

namespace Erdos3

theorem jointPhysicalScalarBudget {G J X : Type*} {Pwidth W τ ξ E V : ℝ}
    (hP : 0 ≤ Pwidth) (hW : 0 ≤ W) (hWP : W ≤ Real.exp Pwidth)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pwidth)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp Pwidth)
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp V) (stride : X → ℕ)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Pwidth) :
    let ρ := spatialWidthFraction (2 * Pwidth) (ξ * τ)
    let Smax := Real.exp (Pwidth + V + 2 * E + 6)
    let Pbase := jointPhysicalBaseLog Pwidth E V
    0 ≤ Pbase ∧ Pwidth ≤ Pbase ∧ E ≤ Pbase ∧ V ≤ Pbase ∧
      0 < ρ ∧ 1 / ρ ≤ Real.exp Pbase ∧
      0 ≤ Smax ∧ Smax ≤ Real.exp Pbase ∧
      (∀ x, ((stride x * max Q (quantitativeBadPrimeRadius E ^ 2) : ℕ) : ℝ) ≤ Smax) ∧
      ∀ (N : X → ℕ), (∀ x, 0 < N x) →
        ∀ z : Option (G ⊕ J) × X, ρ * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  intro ρ Smax Pbase
  have hbase : 0 ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; positivity
  have hPbase : Pwidth ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hEbase : E ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hVbase : V ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hρ : 0 < ρ := spatialWidthFraction_pos _ (mul_pos hξ hτ)
  have hτξ : (ξ * τ)⁻¹ ≤ Real.exp (2 * Pwidth) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp Pwidth * Real.exp Pwidth :=
        mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρinv : 1 / ρ ≤ Real.exp Pbase :=
    (spatialWidthFraction_inv_le (by positivity : 0 ≤ 2 * Pwidth) (mul_pos hξ hτ) hτξ).trans
      (Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog, spatialSamplingBudget]; linarith))
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hV Q hQexp).1
  refine ⟨hbase, hPbase, hEbase, hVbase, hρ, hρinv, (Real.exp_pos _).le,
    Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog]; linarith), ?_, ?_⟩
  · intro x
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp Pwidth * Real.exp (V + 2 * E + 6) :=
        mul_le_mul (hstride x) hcap (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Smax := by dsimp [Smax]; rw [← Real.exp_add]; congr 1; ring
  · intro N hN
    exact (narrow_sampler_width_bounds hP hW hWP hτ hτP hξ hξ1 hξP N hN).2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def allocatedWholeMaskedGridlessProfile (M : ℕ)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  allocatedGridlessCoveredProfile B U b S x (principalAxisRestrict grid y)
    (principalAxisRestrict (fun a => ¬grid a) y) rows hb o bW d
    (allocatedLongProfileDensity B U b S x rows M
      (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict grid y) rows j (principalAxisRestrict (fun a => ¬grid a) y)) M) f)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedNormalizedConditionalHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

noncomputable def allocatedWholeMaskedCoveredProfile
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  allocatedCoveredProfileDensity B U b hR hσ S x (principalAxisRestrict grid y)
    (principalAxisRestrict (fun a => ¬grid a) y) rows hb o bW d quarter
    (allocatedLongProfileDensity B U b S x rows q
      (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict grid y) rows j (principalAxisRestrict (fun a => ¬grid a) y)) q) f)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {X : Type*} [Fintype X] {pw cw : ℝ} {Lw : ℝ≥0}

noncomputable def nativeSingleSiteCoverObservable
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) (fun i => (u i : ℝ) / physicalN i)
    (fun a => coveredJetAmbientTorus U (Q / W.cover) y ⟨a.1, (), a.2⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates
    (cover : ℕ) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (ha : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly = 0 := by
  have hz (j : Fin m) : integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) = 0 := by
    ext α
    rw [integerRowPolynomial_coeff, MvPolynomial.coeff_zero, ← integerRowLinear_apply]
    exact ha j (hm j α)
  simp only [normalizedTwistFrequencyPolynomial, hz, Finset.sum_const_zero, mul_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedNaturalCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

noncomputable def allocatedSlicedGridPointCap (δ P : ℝ) (T d : ℕ) : ℝ :=
  max 1 (max ((allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ^ d)
    (max
      (positiveModerateSpectrumCardBudget j.val d ((layerTailDegree m + 1) * d) P
        (((torusA : ℝ) / (2 * gamma)) / δ ^ degree) ((torusA : ℝ) ^ d / δ ^ ((layerTailDegree m + 1) * d)) 1 + 1)
      (uniformSpectrumAbsoluteCap j.val d (degree * d) P
        ((torusI : ℝ) * cost / δ ^ degree) (((torusI : ℝ) * cost) ^ d / δ ^ (degree * d)))))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def allocatedFullGridSelectedApproximation
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : (a : {_a : gridAxes // True}) → CoefficientJetAxisRow (rowTypes) a.val.val) : ℂ :=
  allocatedFullGridSiteApproximation B U b S rowSets e (fun a => z ⟨a, True.intro⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)

local notation "selected" => (fun _ : {a // allocatedGridAxis (I := I) U b S.value a} => True)

noncomputable def allocatedFullGridSiteProfile
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (e : {a // allocatedGridAxis (I := I) U b S.value a} →
      ScalarSiteExpansion.{uα,uα} (Finset α)) (z : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell selected
      (allocatedFullGridSelectedApproximation B U b S rowSets e)
      (allocatedFullGridNaturalVolume B U b S rowSets)) z *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "volumeN" => allocatedFullGridNaturalVolume B U b S rowSets

noncomputable def allocatedFullGridRowsOfMixed
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (a : gridAxes) : CoefficientJetAxisRow O a.val := (split z).1 a

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d

noncomputable def allocatedFullGridSiteChartPrefactor (z : MixedCoveredJetSource I O E n d) : ℂ :=
  1 / (volumeN : ℂ) *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

noncomputable def allocatedRowSlicedIdeal (ρ : ℝ≥0) (center width : input → ℝ) :
    (output → ℝ) → ℝ :=
  diagonalImageDensity (fun o : output => R o.1.val.1)
    (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α)) ρ center width)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

noncomputable def allocatedBufferedTorusCutoff : (ambient → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedBufferedAmbientCutoff (R := R) U b o r hr)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem forecastSlicedEarlyLogs_le_diagonal_of_dimensions (m Dmod d : ℕ) {r : ℝ} (hr : 0 ≤ r)
    {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D ∧ D ≤ r)
    (htail : 0 ≤ ptail ∧ ptail ≤ r)
    (hv : 0 ≤ v ∧ v ≤ r)
    (hw : 0 ≤ w ∧ w ≤ r)
    (hchild : 0 ≤ vchild ∧ vchild ≤ r)
    (hsm : 0 ≤ Psm ∧ Psm ≤ r)
    (hlip : 0 ≤ Plip ∧ Plip ≤ r)
    (hbad : 0 ≤ Pbad ∧ Pbad ≤ r)
    (hpres : 0 ≤ Ppres ∧ Ppres ≤ r)
    (hE : 0 ≤ E ∧ E ≤ r)
    (hspatial : 0 ≤ Pspatial ∧ Pspatial ≤ r)
    (hcoord : 0 ≤ Pcoord ∧ Pcoord ≤ r)
    (hcut : 0 ≤ Pcut ∧ Pcut ≤ r)
    (hDmod : (Dmod : ℝ) ≤ r) (hd : (d : ℝ) ≤ r) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pnative ∧ 0 ≤ Pmass ∧ 0 ≤ Pcap ∧
      Pnative + Pmass + Pcap ≤ forecastSlicedEarlyDiagonalBudget m r := by
  intro pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have hDNonneg := hD.1
  have htailNonneg := htail.1
  have hvNonneg := hv.1
  have hwNonneg := hw.1
  have hchildNonneg := hchild.1
  have hsmNonneg := hsm.1
  have hlipNonneg := hlip.1
  have hbadNonneg := hbad.1
  have hpresNonneg := hpres.1
  have hENonneg := hE.1
  have hspatialNonneg := hspatial.1
  have hcoordNonneg := hcoord.1
  have hcutNonneg := hcut.1
  let rTail := r + slicedFixedZeroGeometryLog r r r 0 r
  let rLog := slicedFixedUniformSiteLog m rTail 0
  let rIn := r * rLog
  let rDec := (r + r) * (r + 2) * modularRankChargeFactor m
  let rV := rIn + rDec + (r + r) + 3
  let rEsite := r + r + 1 + r * rV
  let rAll := (r + rV) + slicedFixedZeroGeometryLog r r r rV r
  let rProd := slicedFixedUniformAccuracyLog m r rAll rEsite
  let rQ := slicedFixedUniformSiteLog m rAll rProd
  let rO := siteExponentialOutputLog 1 rQ
  let rPeriod := rV + r * rO
  let rFactor := r + r + rO + 1 + r
  let rNative := rPeriod + rFactor + r + r + 1
  let rMass := r + r * rV + r * rO + 1
  let rCap := r + rIn + rDec + 1
  have htail0 : 0 ≤ pTailAll := add_nonneg htail.1
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 (le_refl 0) hchild.1)
  have hlog0 : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m htail0 (le_refl 0)
  have hin0 : 0 ≤ Pin := mul_nonneg hD.1 hlog0
  have hdec0 : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hEs0 : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hsite0 : 0 ≤ psite := add_nonneg htail.1 hV0
  have hAll0 : 0 ≤ pAll := add_nonneg hsite0
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 hV0 hchild.1)
  have hcap0 : 0 ≤ slicedFixedUniformSiteLog m pAll 0 := slicedFixedUniformSiteLog_nonneg m hAll0 (le_refl 0)
  have hprod0 : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD.1 hcap0 hEs0) zero_le_one
  have hQ0 : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hAll0 hprod0
  have hO0 : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ0
  have hperiod0 : 0 ≤ Pperiod := add_nonneg hV0 (mul_nonneg hD.1 hO0)
  have hfactor0 : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hnative0 : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  have hmass0 : 0 ≤ Pmass := by dsimp only [Pmass]; positivity
  have hcapFin0 : 0 ≤ Pcap := by dsimp only [Pcap]; positivity
  have htailR : pTailAll ≤ rTail := add_le_add htail.2
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 (le_refl 0) hchild.1
      hD.2 hv.2 hw.2 le_rfl hchild.2)
  have hlogR : tailLog ≤ rLog := slicedFixedUniformSiteLog_mono m htail0 (le_refl 0) htailR le_rfl
  have hinR : Pin ≤ rIn := mul_le_mul hD.2 hlogR hlog0 hr
  have hdecR : Pdec ≤ rDec := by
    dsimp only [Pdec, rDec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add hDmod le_rfl)
        (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have hVR : V ≤ rV := add_le_add
    (add_le_add (add_le_add hinR hdecR) (add_le_add hE.2 hsm.2)) le_rfl
  have hrV : 0 ≤ rV := hV0.trans hVR
  have hEsR : Esite ≤ rEsite := add_le_add
    (add_le_add (add_le_add hE.2 hsm.2) le_rfl)
    (mul_le_mul hd hVR hV0 hr)
  have hAllR : pAll ≤ rAll := add_le_add (add_le_add htail.2 hVR)
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 hV0 hchild.1
      hD.2 hv.2 hw.2 hVR hchild.2)
  have hprodR : Eprod ≤ rProd := add_le_add
    (uniformProductAccuracyLog_mono hD.1 hcap0 hD.2
      (slicedFixedUniformSiteLog_mono m hAll0 (le_refl 0) hAllR le_rfl) hEsR) le_rfl
  have hQR : Q ≤ rQ := slicedFixedUniformSiteLog_mono m hAll0 hprod0 hAllR hprodR
  have hOR : O ≤ rO := by
    dsimp only [O, rO, siteExponentialOutputLog]
    gcongr
  have hrO : 0 ≤ rO := hO0.trans hOR
  have hperiodR : Pperiod ≤ rPeriod := add_le_add hVR (mul_le_mul hD.2 hOR hO0 hr)
  have hfactorR : Pfactor ≤ rFactor := add_le_add
    (add_le_add (add_le_add (add_le_add hlip.2 hD.2) hOR) le_rfl) hspatial.2
  have hnativeR : Pnative ≤ rNative := add_le_add
    (add_le_add (add_le_add (add_le_add hperiodR hfactorR) hcoord.2) hcut.2) le_rfl
  have hmassR : Pmass ≤ rMass := add_le_add
    (add_le_add (add_le_add hsm.2 (mul_le_mul hd hVR hV0 hr))
      (mul_le_mul hD.2 hOR hO0 hr)) le_rfl
  have hcapR : Pcap ≤ rCap := add_le_add (add_le_add (add_le_add hsm.2 hinR) hdecR) le_rfl
  refine ⟨hnative0, hmass0, hcapFin0, ?_⟩
  change Pnative + Pmass + Pcap ≤ rNative + rMass + rCap
  exact add_le_add (add_le_add hnativeR hmassR) hcapR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem kernelRankCoefficientSlot_eq_block_sum (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    (kernelRankCoefficientSlot (B := B) degree e a).val =
      ∑ k ∈ kernelRankBlock degree e a, Finsupp.single k 1 := by
  simp only [kernelRankCoefficientSlot, productBlockExponent, kernelRankBlock,
    Finset.sum_map]

theorem kernelRankCoefficientSlot_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a b : A) (v : Fin h) :
    (kernelRankCoefficientSlot (B := B) degree e a).val (.inl (e (b, v))) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b <;>
    simp [kernelRankCoefficientSlot, productBlockExponent,
      Finsupp.single_apply, e.injective.eq_iff, hab]

theorem kernelRankCoefficientSlot_injective (degree : D → ℕ)
    (e : A × Fin h ↪ G) (hh : 0 < h) :
    Function.Injective (kernelRankCoefficientSlot (B := B) degree e) := by
  intro a b he
  have hv := congrArg (fun q : BoundedCoefficientExponent (SamplerTupleIndex G B degree) h =>
    q.val (.inl (e (b, ⟨0, hh⟩)))) he
  rw [kernelRankCoefficientSlot_apply, kernelRankCoefficientSlot_apply] at hv
  by_contra hab
  simp [hab] at hv

theorem kernelRankCoefficientSlot_monomial {R : Type*} [CommSemiring R]
    (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) (c : R) :
    MvPolynomial.monomial (kernelRankCoefficientSlot (B := B) degree e a).val c =
      c • ∏ k ∈ kernelRankBlock degree e a, MvPolynomial.X k := by
  rw [kernelRankCoefficientSlot_eq_block_sum, MvPolynomial.monomial_sum_index,
    MvPolynomial.smul_eq_C_mul]
  rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedSpatialRankBlock_product {R : Type*} [CommSemiring R]
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    (∏ k ∈ allocatedSpatialRankBlock (B := B) inactive spatial l,
      MvPolynomial.X k : MvPolynomial (LayerSamplerLongVariables inactive G B) R) =
        MvPolynomial.X (.inl (spatial l)) := by
  rw [allocatedSpatialRankBlock, Finset.prod_singleton]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G A R : Type*} {B : D → Type*} [CommRing R]

theorem samplerLong_killCompl_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    killCompl (samplerLongEmbedding (B := B) inactive h).injective
      (X (.inl g) : MvPolynomial (SamplerTupleIndex G B h) R) = X (.inl g) := by
  change killCompl (samplerLongEmbedding (B := B) inactive h).injective
    (X (samplerLongEmbedding inactive h (.inl g))) = _
  rw [← rename_X, killCompl_rename_app]

theorem spatialRankPolynomial_kernel_selected_long
    [Fintype D] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : D → Prop) (h : D → ℕ) (e : A ↪ G)
    (fixed : Option (SamplerTupleIndex G B h) → R) (c : A → R)
    (v : SamplerTupleIndex G B h → R) :
    homogeneousComponent 1
      (conditionPolynomial (samplerLongEmbedding inactive h)
        (samplerLongEmbedding inactive h).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (samplerLongEmbedding inactive h).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter
            (fun d => d ∉ Set.range (spatialKernelRankSlot (P := PrincipalTupleIndex B h) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (SamplerLongVariables inactive G B h) R) := by
  rw [homogeneousComponent_conditionPolynomial_top _ _ _ v 1
    (spatialRankPolynomial_degree _), spatialRankPolynomial_kernel_selected_top, map_add]
  apply congrArg₂ (fun P Q => P + Q)
  · apply congrArg (killCompl (samplerLongEmbedding inactive h).injective)
    apply congrArg (homogeneousComponent 1)
    apply Finset.sum_congr
    · exact Finset.filter_congr_decidable _ _ _
    · intro d _
      rfl
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul, samplerLong_killCompl_common]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedSpatialRankPolynomial_kernel_selected_long
    [∀ j, Fintype (I j)] [Fintype G] [∀ d, Fintype (B d)] [Fintype A]
    (inactive : LayerSamplerAxis I n → Prop) (e : A ↪ G)
    (fixed : Option (LayerSamplerVariables G I n B) → R) (c : A → R)
    (v : LayerSamplerVariables G I n B → R) :
    homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot e) c fixed))) =
      killCompl (allocatedLongEmbedding inactive).injective
        (homogeneousComponent 1
          (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
            (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) e)),
            MvPolynomial.monomial (spatialRankExponent d) (fixed d))) +
      ∑ a, c a • (X (.inl (e a)) : MvPolynomial (LayerSamplerLongVariables inactive G B) R) := by
  convert spatialRankPolynomial_kernel_selected_long inactive (layerSamplerDegree I n) e fixed c v using 1
  · rfl
  · apply congrArg₂ (fun P Q => P + Q)
    · apply congrArg (killCompl (allocatedLongEmbedding inactive).injective)
      apply congrArg (homogeneousComponent 1)
      apply Finset.sum_congr
      · congr 1
      · intro d _
        rfl
    · rfl

end VectorPolynomial
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

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

theorem samplerLongEmbedding_kernelExponent (inactive : D → Prop) (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    ((kernelRankCoefficientSlot (G := G)
      (B := fun d : {d // ¬ inactive d} => B d.val) (fun d => degree d.val) e a).val).mapDomain
        (samplerLongEmbedding inactive degree) =
      (kernelRankCoefficientSlot (B := B) degree e a).val := by
  simp only [kernelRankCoefficientSlot, productBlockExponent,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    kernelRankBlockEmbedding_apply, samplerLongEmbedding_common]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedModularRankTaggedPolynomials
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedDegreeRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr a => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedTaggedRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr o => allocatedDegreeRankResidual inactive j r projection kernel block o

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedSelectedRankCoefficients
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N
  | .inl x, l => noise (spatialKernelRankSlot spatial l,x.val)
  | .inr (.inl i), l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i
  | .inr (.inr a), l => projection a
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

noncomputable def allocatedPrincipalRankCenter : ℝ :=
  (3 * principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

noncomputable def allocatedPrincipalRankWidth : ℝ :=
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

include hR in

theorem allocatedPrincipalRankWidth_pos : 0 < allocatedPrincipalRankWidth B U basis S j i := by
  apply mul_pos (div_pos (principalProfileSize_pos (hR j) _) (by norm_num))
  exact div_pos (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _)

include hR in

theorem allocatedPrincipalRankWidth_large
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ allocatedPrincipalRankWidth B U basis S j i :=
  integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
    (principalProfileSize_pos (hR j) _) (S.gap j i hactive)

include hR in
theorem allocatedPrincipalRankMass_pos
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i) :
    0 < shiftedSmoothSampleSum (allocatedPrincipalRankCenter B U basis S j i)
      (allocatedPrincipalRankWidth B U basis S j i) :=
  shiftedSmoothSampleSum_pos _ (allocatedPrincipalRankWidth_large B U basis hR S j i hactive)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

noncomputable def allocatedDeckFullSlot (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L → CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E
  | ⟨j,e,l⟩ => ⟨j,kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l,e⟩

theorem allocatedDeckFullSlot_injective (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    Function.Injective (allocatedDeckFullSlot (I := I) (E := E) (n := n) (B := B) kernel) := by
  rintro ⟨j,e,l⟩ ⟨k,f,q⟩ he
  have hjk : j = k := congrArg Sigma.fst he
  subst k
  have hp := eq_of_heq (Sigma.mk.inj he).2
  have hl : l = q := kernelRankCoefficientSlot_injective
    (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
  have hef : e = f := congrArg Prod.snd hp
  subst q
  subst f
  rfl

noncomputable def allocatedDeckFullEmbedding (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L ↪ CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E :=
  ⟨allocatedDeckFullSlot kernel, allocatedDeckFullSlot_injective kernel⟩

def allocatedReadFullSmooth {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl x => allocatedReadNoise f x
  | .inr ⟨j,q,i⟩ => allocatedReadProjection f ⟨j,.inr i⟩ q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedFullSmoothScalarPMF
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ) :
    AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ
  | .inl x => noisePMF x
  | .inr ⟨j,q,i⟩ => allocatedLayerIntegerPMFs B U basis hR hσ S j i q

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

def allocatedCongruenceIsSpatial (inactive : LayerSamplerAxis I n → Prop)
    (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → Prop
  | .inl _ => True
  | .inr _ => False

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

def allocatedFullSmoothAffine [Semiring R] (stride : X → R)
    (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl t => residue t + stride t.2 * z (.inl t)
  | .inr t => z (.inr t)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceNaturalStride (inactive : LayerSamplerAxis I n → Prop)
    (stride : X → ℕ) (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → ℕ
  | .inl x => stride x.val
  | .inr _ => 1

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineCongruenceScalarFintype
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceScalarIndex X E inactive L) := inferInstance

noncomputable local instance affineCongruenceScalarDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceScalarIndex X E inactive L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedCongruenceIntegerSelectedCoefficients_reduce (N : ℕ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) (l : Fin L) :
    (selected ⟨j, (o,l)⟩ : ZMod N) =
      allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection j a q : ZMod N))
        spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o) l := by
  rcases o with x | i | a <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineFullWitnessSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance affineFullWitnessSmoothDecidableEq_r489fc5_1 :
    DecidableEq (AllocatedFullSmoothCoefficientIndex G X I n B) := Classical.decEq _
noncomputable local instance affineFullWitnessDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance affineFullWitnessDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReadCoefficientChartResidues_sampler
    (M : ℕ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M)) =
      coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M)) := by
  funext j q i
  cases i with
  | inl i => exact congrArg (fun z : ℤ => (z : ZMod M)) (hinteger j i q)
  | inr i => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance spatialReferenceSmoothFintype_r489fc5_1 :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance spatialReferenceDeckFintype_r489fc5_1 :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance spatialReferenceDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_lift (c : CoefficientArray (K := K) U)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) c) :
    ∃ w : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q),
      canonicalCoefficientDeckSample U bW b hb o q hq x
          (fun j e => integerResidueMap (E j) q (w j e)) =
        QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c) := by
  have hp (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩)) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) := by
    have h := congrArg (fun y => euclideanCoefficientEquiv U y j e) hx
    simpa only [canonicalCoefficientSample, AddEquiv.apply_symm_apply,
      euclideanCoefficientEquiv_mk, mixedArrayQuotient] using h.symm
  choose w hw using fun (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) =>
    exists_normalized_representative_offset (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, e⟩))
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) (hp j e)
  refine ⟨w, ?_⟩
  intro q hq
  apply (euclideanCoefficientEquiv U).injective
  funext j e
  rw [canonicalCoefficientDeckSample_coordinate, normalizedCoverLift_add_deck, hw,
    euclideanCoefficientEquiv_mk]
  congr 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficientDeck_integer_event_read
    (c : CoefficientArray (K := K) U) (x : CoefficientSamplerArrays (K := K) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) :
    ∃ w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ,
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues K n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (coefficientSamplerChartResidues q x
            (fun j e => integerResidueMap (E j) q (w j e))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_lift U bW b hb o c x hx
  refine ⟨w, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [← hw q (NeZero.pos q)]
  exact coefficientDeckChartEvent_sample_iff U bW b hb o q event x hsmall _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} {J I E : Fin m → Type*} {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_allocatedCoefficient_integer_event_read
    (c : CoefficientArray (K := LayerSamplerVariables G I n B) U)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : canonicalCoefficientSample U b hb o x = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
      allocatedReadNoise f = noise ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
      ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • c)) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q))) := by
  obtain ⟨w, hw⟩ := exists_coefficientDeck_integer_event_read U bW b hb o c x hx hsmall
  let f : AllocatedActualCoefficientIndex G X I E n B → ℤ :=
    allocatedMixedFullArray (Sum.elim noise (fun ⟨j,e,i⟩ => (x j).2 i e))
      (fun ⟨j,e,i⟩ => w j e i) (fun _ => 0)
  have hi (j : Fin m) (i : Fin (n j))
      (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e := rfl
  refine ⟨f, rfl, hi, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro event
  rw [allocatedReadCoefficientChartResidues_sampler q f x hi]
  exact hw q hq event

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedCenteredConditionalPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (c : ∀ j, U j) (a : X → ℤ)

omit [∀ j, Fintype (J j)] in
theorem allocatedCenteredConditionalPolynomial_degree
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) (j : Fin m) :
    DegreeLE (1 : X → ℕ) (j.val + 1) (allocatedCenteredConditionalPolynomial U poly c a j) :=
  degreeLE_translate _ (fun _ => by norm_num) _ _ ((hp j).subtractConstant _)

theorem allocatedCenteredConditionalPolynomial_rank
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (H : X → ℝ) (Rrank : ℝ) (j : Fin m) :
    HasLayerSamplingRank (j.val + 1) H Rrank (U j)
      (allocatedCenteredConditionalPolynomial U poly c a j) ↔
      HasLayerSamplingRank (j.val + 1) H Rrank (U j) (poly j) := by
  unfold allocatedCenteredConditionalPolynomial
  rw [hasLayerSamplingRank_translate_iff _ _ _ _ _ _ ((hp j).subtractConstant _),
    hasLayerSamplingRank_subtractConstant_iff (by omega)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedJointFrameRead_reduce (M : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (fun i => ((allocatedJointFrameRead a f i : ℤ) : ZMod M)) =
      allocatedJointFrameRead (fun x => (a x : ZMod M)) (fun i => (f i : ZMod M)) := by
  funext i
  rcases i with ⟨k,x⟩ | k
  · cases k
    · exact Int.cast_add _ _
    · rfl
  · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReplaceReadNoise_eq_jointFrame
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z) :
    allocatedReplaceReadNoise B z f = allocatedJointFrameRead (-base) f := by
  funext i
  rcases i with ⟨k,x⟩ | i
  · have h := congrFun hf (k,x)
    cases k with
    | none =>
      change z (none,x) = -base x + f (.inl (none,x))
      change f (.inl (none,x)) = base x + z (none,x) at h
      omega
    | some k =>
      change z (some k,x) = f (.inl (some k,x))
      simpa only [allocatedReadNoise, Pi.add_apply, integerBaseTranslation,
        baseArrayJoin, Pi.zero_apply, zero_add] using h.symm
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

instance coefficientTorus_zeroLayer_subsingleton {K : Type*} {J : Fin 0 → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Subsingleton (CoefficientTorus (K := K) U) where
  allEq x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    change QuotientAddGroup.mk' (coefficientIntegerLattice U) c =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) d
    apply congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    funext t
    exact Fin.elim0 t.1

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}
variable (B : LayerSamplerAxis I n → Type*)

def allocatedZeroLayerSample :
    CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n :=
  fun j => Fin.elim0 j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A Y Site : Type*} [Fintype A] [Fintype Y]
variable (selected : A → Σ j : Fin m, Fin (n j)) (R : Fin m → ℝ)
variable (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (M : ℕ) (hd : ∀ a, (e a).period (k a) ∣ M)

noncomputable def forecastNormalizedResidueFactor
    (ψ : AddChar (∀ j, Fin (n j) ⊕ E j → ZMod M) ℂ)
    (f : (Y → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ) → ℂ)
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M)
    (x : (Y → ℝ) × (LayerSamplerAxis I n → ℝ)) : ℂ :=
  star (ψ label) * f (x.1, forecastNormalizedActiveCoordinates P x.2) *
    siteFamilyFactor e k site (forecastNormalizedResidues selected e k M hd label)
      (forecastNormalizedInactiveCoordinates selected R x.2)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedConcreteSlicedForecastOutputLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Esite := E + Pκ + Psm + 1 + ((nX + m * M + 1 : ℕ) : ℝ) * V
  let pAll := preparedSlicedForecastTailLog cost + V +
    slicedFixedZeroGeometryLog D v cost V (childLog + 1)
  let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
  siteExponentialOutputLog 1 Q

noncomputable def preparedConcreteSlicedForecastNativeLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ) : ℝ :=
  let Dbase := allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Pspatial := (gainLog + nX + 8) + 8
  let Pcoord := pRadius + PF + Dbase
  let Pcut := pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1
  (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1

noncomputable def preparedConcreteSlicedForecastMassLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart +
    (Psm + ((nX + m * M + 1 : ℕ) : ℝ) * V + D * O + 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularGeneralDetector_variable_count {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * D := by
  change ((Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))) : ℝ) ≤ _
  rw [Fintype.card_sum, Nat.cast_add]
  linarith [hdim.kernel_variables, hdim.tuples]

theorem preparedModularGeneralDetector_layer_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (∀ j, (Fintype.card (I j) : ℝ) ≤ D) ∧ (∀ j, (n j : ℝ) ≤ D) := by
  constructor
  · intro j
    have hcard : Fintype.card (I j) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : I j => (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inl_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

  · intro j
    have hcard : Fintype.card (Fin (n j)) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : Fin (n j) => (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    rw [Fintype.card_fin] at hcard
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_physical_root {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * P :=
    (preparedModularGeneralDetector_variable_count B rowSets hdim).trans (by linarith)
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp (P + 8) := by
    calc
      _ ≤ 2 * P := hvars
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)])
        (by linarith [Real.add_one_le_exp P]) hP (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp (P + 8) * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JointExceptionalSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem narrow_sampler_residue_width_exp {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, Real.exp P ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  obtain ⟨hf, hfInv, hfWidth⟩ := narrow_sampler_width_bounds (G := G) (J := J)
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  intro z
  have hproduct : Real.exp P * (q z.2 : ℝ) /
      spatialWidthFraction (2*P) (ξ*τ) ≤ (N z.2 : ℝ) := by
    calc
      _ = Real.exp P * (q z.2 : ℝ) *
          (1 / spatialWidthFraction (2*P) (ξ*τ)) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (spatialSamplingBudget (2*P)) := by
        gcongr
        exact hqP z.2
      _ = Real.exp (10*P+128) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold spatialSamplingBudget
        ring
      _ ≤ _ := hsize z.2
  apply (le_div_iff₀ (show (0 : ℝ) < q z.2 by exact_mod_cast hq z.2)).mpr
  exact ((div_le_iff₀ hf).mp hproduct).trans
    (by simpa only [mul_comm] using hfWidth z)

theorem jointExceptionalSpatialWidthBudget {G J X : Type*} {P W τ ξ logwide : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hlog : logwide ≤ P)
    (hsize : ∀ i, Real.exp ((P+4)^4) ≤ (N i : ℝ))
    (e : Fin 2 × X ↪ G) :
    (∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z) ∧
    ∀ i, Real.exp logwide ≤ spatialMatrixIndexWidth e q
      (narrowTrimmedSpatialWidths (J := J) W τ ξ N) i := by
  have hsize' (i) : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (jointExceptionalSpatialSize_polynomial hP)).trans (hsize i)
  refine ⟨narrow_sampler_residue_scale hP hW hWP hτ hτP hξ hξ1 hξP
    N q hq hqP hprofile hsize', ?_⟩
  intro i
  exact (Real.exp_le_exp.mpr hlog).trans
    (narrow_sampler_residue_width_exp hP hW hWP hτ hτP hξ hξ1 hξP
      N q hq hqP hsize' (spatialMatrixBlockSlot e i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateNestedDegreeNetSchedule
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_candidateDegreeReturn_next_seed (degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ)
      {x : ℝ}, C ≤ A → 1 ≤ innerDepth → 0 ≤ x →
      candidateDegreeReturnBudget degree
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤
      candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  let P : Polynomial ℕ := Polynomial.C (3 ^ degree) * (Polynomial.X + 1)
  obtain ⟨C, hC, hbound⟩ := exists_candidateNestedForward_polynomial_next_seed P
  refine ⟨C, hC, ?_⟩
  intro A constants innerDepth outer x hCA hdepth hx
  have hpoly := hbound A constants innerDepth outer hCA hdepth hx
  have heval : P.eval₂ (Nat.castRingHom ℝ)
      (candidateNestedForwardSeed A constants innerDepth outer x) =
      (3 : ℝ) ^ degree * (candidateNestedForwardSeed A constants innerDepth outer x + 1) := by
    change (Polynomial.C (3 ^ degree) * (Polynomial.X + 1)).eval₂
      (Nat.castRingHom ℝ) _ = _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_one]
    simp only [map_pow, map_ofNat]
  rw [heval] at hpoly
  dsimp only [candidateDegreeReturnBudget]
  linarith only [hpoly]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointReturnBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedNestedEndpointReturnExponent (degree : ℕ) : ℕ :=
  (exists_candidateDegreeReturn_next_seed degree).choose

theorem preparedNestedEndpointReturnExponent_two_le (degree : ℕ) :
    2 ≤ preparedNestedEndpointReturnExponent degree :=
  (exists_candidateDegreeReturn_next_seed degree).choose_spec.1

theorem candidateDegreeReturnBudget_le_endpointParameter
    (degree A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inner : ℕ)
    {x : ℝ} (hA : preparedNestedEndpointReturnExponent degree ≤ A)
    (hdepth : 1 ≤ innerDepth) (houter : 2 * degree + 1 ≤ outerDepth) (hx : 0 ≤ x) :
    candidateDegreeReturnBudget degree
      (candidateNestedForwardSeed A constants innerDepth (2 * degree) x) ≤
        preparedFiniteForwardParameter A constants inner
          (candidateNestedForwardSeed A constants innerDepth outerDepth x) := by
  have hnext := (exists_candidateDegreeReturn_next_seed degree).choose_spec.2
    A constants innerDepth (2 * degree) hA hdepth hx
  have hAtwo := (preparedNestedEndpointReturnExponent_two_le degree).trans hA
  exact hnext.trans
    ((candidateNestedForwardSeed_monotone A constants innerDepth hAtwo hx houter).trans
      (le_preparedFiniteForwardParameter A constants inner
        (candidateNestedForwardSeed_nonneg A constants innerDepth outerDepth hx)))

end Erdos3.VectorPolynomial

end

end OAI
end


