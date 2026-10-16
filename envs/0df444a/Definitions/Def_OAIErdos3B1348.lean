-- Prove2me | Definitions.Def_OAIErdos3B1348
-- name    : OAIErdos3B1348
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T00:06:13.850191+00:00
-- url     : https://prove2.me/theorems/9a8cd641-9384-4a82-ba26-f3e243d31042
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1349 of 1379
-- statement:
--   Definitions bundle 1349 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1347`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1349 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.exists_allocated_frozen_pullbacks`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_pulled_slow`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.currentGrade_spatial_support`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.globalOrbit_chart_values`, `OAI.Erdos3.VectorPolynomial.AllocatedNormalizedCandidateConclusion`, `OAI.Erdos3.VectorPolynomial.AllocatedReturnedPatchSource.chart`, `OAI.Erdos3.VectorPolynomial.AllocatedReturnedPatchSource.chart_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedReturnedPatchSource.physical`, `OAI.Erdos3.VectorPolynomial.AllocatedReturnedPatchSource.rec`, `OAI.Erdos3.VectorPolynomial.PreparedEmptyLayerLocalScheduleBudget`, `OAI.Erdos3.VectorPolynomial.PreparedFiniteScheduleWitnessBudget`, `OAI.Erdos3.VectorPolynomial.allocatedNormalizedShearProblem`, `OAI.Erdos3.VectorPolynomial.preparedActualSlicedForecastSetupOfSourceGeometry`, `OAI.Erdos3.VectorPolynomial.preparedEmptyLayerLocalTailWidthLog`, `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleWitnessSeed`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1340
import Definitions.Def_OAIErdos3B1343

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

def PreparedEmptyLayerLocalScheduleBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  let master := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (physical k) (u k) (model k) (rho k) (target k) (gain k)
  let coarse := preparedFiniteScheduleDirectCoarse gain requestedCoarse
  let late := ∑ k, preparedUniformDegreeDirectLate (master k) scale (physical k) coarse extraLate
  pRadius ∈ Set.Icc 0 cap ∧ D ∈ Set.Icc 0 cap ∧ scale ∈ Set.Icc 0 cap ∧
    coarse ∈ Set.Icc 0 cap ∧ late ∈ Set.Icc 0 cap ∧
    ∀ k, gain k ∈ Set.Icc 0 cap ∧ Pk k ∈ Set.Icc 0 cap ∧
      physical k ∈ Set.Icc 0 cap ∧ target k ∈ Set.Icc 0 cap ∧
      rho k ∈ Set.Icc 0 cap ∧ tail k ∈ Set.Icc 0 cap ∧
      lengths k ∈ Set.Icc 0 cap ∧ master k ∈ Set.Icc 0 cap ∧
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (master k) late).Bounds cap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalTailWidthLog
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  (probabilityProfileLipschitz : ℝ) + 8 + (D + 4) + pRadius + scale

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleWitnessSeed
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  allocatedScaleLog (scale + ∑ k, lengths k + Pmin + 1)

def PreparedFiniteScheduleWitnessBudget
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse : ℝ)
    (u model : K → ℝ) (cap : ℝ) : Prop :=
  let seed := preparedFiniteScheduleWitnessSeed (G := G) m degree Cdetect nX count
    Bstruct pnum Qstride Qσ Pmin u model
  seed ∈ Set.Icc 0 cap ∧ allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 cap ∧
    PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse (allocatedWitnessScaleLog seed Qw) u model cap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredChartSlow
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] {I E : Fin m → Type*} {J : Fin m → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_pulled_slow
    [Fintype X]
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (basis '' {i | j ≤ ω i}))
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {budget : ℝ} (hcontrol : NilpotentLieFiltration.FullChartControlledFactors F basis ω hF J poly N left right budget)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    : F.SymbolSlowBound basis ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
      (F.realSymbolHomogeneousPullbackHom basis ω hF (fullTaggedVariableWeight (X := X) J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
          (integerSampledRealChart (fun z => freezePolynomial keep fixed
            (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) left) := by
  apply NilpotentLieFiltration.FullChartControlledFactors.homogeneousPullback_slow
    F basis ω hF J poly N left right hcontrol
  · intro k
    exact lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k.val)
  · have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    simpa only [one_mul] using
      mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  · exact h.integerFullChart_frozen_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall keep fixed

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedControlledFrozenPullbacks
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct Classical

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Rad σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
variable (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem FullChartControlledFactors.exists_allocated_frozen_pullbacks
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {budget allowance : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ allowance) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∀ (c : ∀ j, U j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag otag S hRad hσ
        poly hm c origin v sample read →
      ∀ (keep : LayerSamplerVariables G I n B → Prop)
        (fixed : {i // ¬keep i} → ℤ),
      let β := allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed
      let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
      (∀ l : ℕ, q ∣ l → F.SymbolRationalGrid b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l (pull right)) ∧
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1 →
      (∀ j, σ j ≤ 1) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ Cgeo : Fin m → ℝ, (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
      F.SymbolSlowBound b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => ((Sum.elim (fun _ : G => S.value)
          (allocatedPrincipalSides B U btag S) i.val : ℕ) : ℝ)) allowance (pull left) := by
  have hc := hcontrol
  obtain ⟨q, hq, hqB, Echart, hchart, hbound, hgrid⟩ := hc
  refine ⟨q, hq, hqB, ?_⟩
  intro c origin v sample read hread keep fixed
  dsimp only
  constructor
  · intro l hql
    apply F.symbolRationalGrid_mono b ω hF _ hq hql
    exact F.symbolRationalGrid_integerTopPullback_of_coefficientGrid b ω hF
      (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed)
      q right hgrid
  · intro τ ξ hτ hτ1 hξ hv hσ1 hpoly Cgeo hCgeo hgeo hsmall
    have hs := hread.integerFullChart_frozen_pulled_slow B U btag hbtag otag S hRad hσ
      poly hm F b ω hF left right hpoly c origin N hN hcontrol hτ hτ1 hξ
      v hv sample read hσ1 Cgeo hCgeo hgeo hsmall keep fixed
    have hs' := F.symbolSlowBound_mono b ω hF
      (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U btag S i.val)
      (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U btag S i.val))
      hallowance _ hs
    simp_rw [allocatedParameterBox_side_eq] at hs'
    unfold allocatedFrozenIntegerFullChart
    exact hs'

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

structure AllocatedReturnedPatchSource (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (z : A.Path) where
  supported : 0 < A.law.weight z
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I E n B → ℤ
  recovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
    centerLift z.1.val z.2.val sample read
  fixed : {i // ¬keep i} → ℤ
  fixed_in_box : ∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val

namespace AllocatedReturnedPatchSource

variable {keep : LayerSamplerVariables G I n B → Prop} {centerLift : ∀ j, U j}
    {z : A.Path} (source : AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z)

noncomputable def physical (u : {i // keep i} → ℤ) : X → ℤ :=
  jointIntegerPhysicalSite (finiteSplitPoint keep u source.fixed) (z.1.val, z.2.val)

noncomputable def chart {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i) :
    AllocatedExternalLocalChart (E := E) A cost where
  path := z
  path_supported := source.supported
  centerLift := centerLift
  center_eq := hcenter
  sample := source.sample
  read := source.read
  recovered := source.recovered
  keep := keep
  fixed := source.fixed
  fixed_in_box := source.fixed_in_box
  step := q
  step_pos := hq
  slice := slice
  dense := ⟨_, _, _, hq, hlen, slice.progression_inside, hlength,
    slice.integerPoints_eq_commonStrideBox⟩

@[simp] theorem chart_physical {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i)
    (u : {i // keep i} → ℤ) :
    (source.chart hcenter slice hq hlen hlength).physical u = source.physical u := rfl

end AllocatedReturnedPatchSource

noncomputable def allocatedNormalizedShearProblem
    {Y : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch Y s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots {i // keep i} d patch.weight)
    (q : productive → ℕ) (hq : ∀ z, 0 < q z)
    (slice : ∀ z, ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) (q z))
    (hlen : ∀ z i, 0 < (slice z).length i)
    (hlength : ∀ z i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ (slice z).length i)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ ((slice z).fullSliceLaw (hlen z)).mean
      (fun u => (f ((source z).physical u.val) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold where
  productive := productive
  mass := hmass
  chart z := (source z).chart hcenter (slice z) (hq z) (hlen z) (hlength z)
  chart_path _ := rfl
  centerLift := centerLift
  chart_centerLift _ := rfl
  frozen_side _ := hshort
  candidate z := {
    orbit := (localForm z).shearPolynomialOrbit s patch.weight_le
    mark_on_slice := by
      intro u hu
      apply NilpotentLieBCHGroup.ext
      exact Subsingleton.elim _ _ }
  score z := by
    have hs := hscore z
    rw [patch.fullSliceLaw_shearObservable_score (localForm z) (slice z)
      (hq z) (hlen z) (fun u => f ((source z).physical u)) lam] at hs
    exact hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

def AllocatedNormalizedCandidateConclusion
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (productive : Finset A.Path)
    (childCost cost : ℝ) (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) : Prop :=
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊childCost⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartOrbitValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)

theorem globalOrbit_chart_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g) =
      F.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (C.chartValues u i : ℝ))
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm g) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval]
  rfl

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFacts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem currentGrade_spatial_support (z : P.productive) :
    z.val.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
  simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
    using z.val.2.property

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSourceSlicedForecastNumerics
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
noncomputable def preparedActualSlicedForecastSetupOfSourceGeometry {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)),
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    {Cdetect : ℕ} {Bstruct Pscale Dgeometry target Pk Prho pDetect aDetect detectionGain : ℝ}
    (hInverseBound : ∀ j, inverse j ≤ Real.exp Bstruct)
    (hgeometry : PreparedUniformDegreeGeometryAt
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S 0 Cdetect nX
      Bstruct Pscale Dgeometry target Pk Prho Qstride pDetect pRadius aDetect detectionGain) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      (G := EnlargedPreparedCommonKernel m Jalloc)
      (I := PreparedSamplerContinuous L) (n := preparedSamplerTransverse L)
      (A := PreparedActualForecastShortIndex (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M)
      (preparedActualForecastShortSelection (G := EnlargedPreparedCommonKernel m Jalloc)
        (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let geometry := Classical.choice hgeometry.1
  exact preparedActualSlicedForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord Pdim
    hpRadius hGain hQstride hPF hChart hcost hratio hR hRone hRinv hσone
    forward hforward hforwardBound geometry.siteRadius geometry.T
    (fun j => by
      have h := geometry.hsource j
      norm_num only [Fintype.card_fin, Nat.cast_one, pow_one] at h
      exact h) geometry.hradius
    inverse hinverse hchart (fun j => by
      simpa only [mul_assoc] using (geometry.hbudgets inverse hinverse hInverseBound).2.2 j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end


