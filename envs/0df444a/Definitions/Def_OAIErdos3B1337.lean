-- Prove2me | Definitions.Def_OAIErdos3B1337
-- name    : OAIErdos3B1337
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T22:46:37.347781+00:00
-- url     : https://prove2.me/theorems/5d357e47-aeca-4a9a-af08-e36633aebde4
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1338 of 1373
-- statement:
--   Definitions bundle 1338 of 1373 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1336`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1338 available.
--
--   Modules: `OAI.Erdos3.PolynomialPatch.ofZeroLayerShearOrbit`, `OAI.Erdos3.PolynomialPatch.ofZeroLayerShearOrbit_complexity`, `OAI.Erdos3.PolynomialPatch.ofZeroLayerShearOrbit_kernel`, `OAI.Erdos3.ResidueBoxSlice.expect_fullSlicePoints`, `OAI.Erdos3.ResidueBoxSlice.fullSliceLaw_complexMean_eq_expect_points`, `OAI.Erdos3.ResidueBoxSlice.fullSlicePointInIntegerBox_injective`, `OAI.Erdos3.ResidueBoxSlice.fullSlicePoints`, `OAI.Erdos3.ResidueBoxSlice.fullSlicePoints_image_val`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.frozen_twist_variation`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_normalized_top_mass`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_mass`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag_mass`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.twist_variation`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.frozenTaggedContext`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.candidate`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.chart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.chart_keep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.chart_localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.context`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.context_sides`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.input`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.input_V_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.input_η`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.input_θ`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.jointOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateTaggedPairFamily.rec`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.localLaw_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.siteValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.siteValue_sliceSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.SlicePoint`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.chartValues_eq_physicalIntegerPoint`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.chartValues_eq_physicalIntegerPoint_of_center`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.chartValues_eq_physicalIntegerPoint_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.chartValues_tag_eq_round`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.localLaw_complexMean_eq_fullSliceLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.localLaw_complexMean_parameter`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.low_residual`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.physical_sliceSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedParameter`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.retainedParameter_parameter`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.sliceSite`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.sliceSite_val`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedContext.rec`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedContext.sides`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedPairInput`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedPairInput.ofCandidate`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedPairInput.ofCandidate_V_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedPairInput.ofCandidate_W_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenTaggedPairInput.ofCandidate_of_localLaw`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_sub_eval_of_component_dist`, `OAI.Erdos3.VectorPolynomial.allocatedLayerSupported_polynomial_variation`, `OAI.Erdos3.VectorPolynomial.allocatedRecoveredIntegerFullChart_spatial_top_mass`, `OAI.Erdos3.VectorPolynomial.exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop`, `OAI.Erdos3.VectorPolynomial.exists_allocated_frozen_tagged_twist_fixed_basis_step_drop`, `OAI.Erdos3.VectorPolynomial.fullTaggedPhysicalIntegerPoint`, `OAI.Erdos3.VectorPolynomial.jointIntegerFullChart_normalized_spatial_top`, `OAI.Erdos3.VectorPolynomial.layerSamplerBox_sum_le_zero_root_budget`, `OAI.Erdos3.exists_native_twist_variation_slice_fixed_basis_step_drop`, `OAI.Erdos3.exists_native_twist_variation_slice_step_drop`, `OAI.Erdos3.zeroLayerPhysicalPoint`, `OAI.Erdos3.zeroLayerSpatialChart`, `OAI.Erdos3.zeroLayerSpatialChart_support`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1329
import Definitions.Def_OAIErdos3B1332
import Definitions.Def_OAIErdos3B1338

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {K X : Type*} [Fintype K]

theorem jointIntegerFullChart_normalized_spatial_top
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ) (x : X) :
    aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart (jointIntegerFullChart J a v tag) i))
      (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)) =
      C ((N x : ℝ)⁻¹) * homogeneousComponent 1
        (affineFramePolynomial (fun k z => (jointIntegerFrame (a, v) k z : ℝ)) x) := by
  simp only [normalizedRealPolynomialChart_inl, map_mul, aeval_C, aeval_X]
  change C ((N x : ℝ)⁻¹) * homogeneousComponent 1
    (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)) = _
  rw [affineFramePolynomial_map]
  rfl

variable {G : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem layerSamplerBox_sum_le_zero_root_budget :
    (∑ k, layerSamplerBox B U b S k) ≤
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => layerSamplerBox_le B U b S k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

theorem allocatedRecoveredIntegerFullChart_spatial_top_mass [Fintype X]
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)))) ≤ τ / 8 := by
  unfold allocatedRecoveredIntegerFullChart
  rw [jointIntegerFullChart_normalized_spatial_top]
  have hT : ∀ k, 0 ≤ layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k)
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN x
  have hsum := narrowSpatial_frame_slope_sum
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hξ N hN
    (layerSamplerBox B U b S) hT (layerSamplerBox_sum_le_zero_root_budget B U b S) v hv x
  refine (spatialAffineTop_scaled_inv_mul_mass_le
    (fun k z => (jointIntegerFrame (a, v) k z : ℝ))
    (layerSamplerBox B U b S) hT x (N x) hn).trans ?_
  change (N x : ℝ)⁻¹ * (∑ k, |(v (some k, x) : ℝ)| * layerSamplerBox B U b S k) ≤ _
  calc
    _ ≤ (N x : ℝ)⁻¹ * (τ * (N x : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = τ / 8 := by field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_tag_mass
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (N : X → ℝ) (j : Fin m) (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) (Sum.inr ⟨j, i⟩)))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  rw [h.integerFullChart_normalized_top_tag B U b hb o S hR hσ poly hm hp c a v sample read N j i]
  exact (normalizedMass_neg_weightedHomogeneousComponent_le _ _ _ _).trans
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 i)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
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
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  cases i with
  | inl x =>
    apply (allocatedRecoveredIntegerFullChart_spatial_top_mass B U b S o poly hm c a
      N hN hτ hξ v hv sample x).trans
    have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hone := mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    apply (show τ / 8 ≤ 1 by linarith).trans
    simpa only [one_mul] using hone
  | inr z =>
    exact h.integerFullChart_normalized_top_tag_mass B U b hb o S hR hσ poly hm hp c a v
      sample read hσ1 C hC hchart hsmall (fun x => (N x : ℝ)) z.1 z.2

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_normalized_top_mass
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
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
    (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
        (integerSampledRealChart (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))) ≤
      ((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m := by
  change realPolynomialMass (scaleMvPolynomialAxes _
    (aeval (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)))) _)) ≤ _
  rw [aeval_frozen_integer_top (fullTaggedVariableWeight J)
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample)]
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  exact (normalizedMass_freezePolynomial_le keep _ hT 0
    (fun i => by simpa only [Pi.zero_apply, abs_zero] using (hT i.val).le) _).trans
    (h.integerFullChart_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenTaggedTwistStepDrop
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_variation
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x y : LayerSamplerVariables G I n B → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |x k| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |y k| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |x k - y k| ≤ layerSamplerBox B U b S k * δ) (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i -
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 y i| ≤
      (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) * δ := by
  rw [← mixedLiftPolynomial_eval, ← mixedLiftPolynomial_eval]
  apply abs_eval_sub_eval_normalized_mass_bound _ _
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)) x y
    (allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
      hsmall j a ha i) hδ hx hy hxy
  exact (mixedLiftPolynomial_degree (euclideanSubspace (U j)) (b j) (o j) Subtype.val
    a (fun d => d.property) i).trans (by omega)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_sub_eval_of_component_dist
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u v : X → ℤ) {ε : ℝ}
    (hres : (fun i => (u i : ZMod W.modulus)) = (fun i => (v i : ZMod W.modulus)))
    (hspatial : dist (fun i => (u i : ℝ) / N i) (fun i => (v i : ℝ) / N i) ≤ ε)
    (htag : dist (physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
      (physicalGridFactorInput W.cover poly (fun i => (v i : ℝ))) ≤ ε) :
    ‖W.eval N poly u - W.eval N poly v‖ ≤ (L : ℝ) * ε := by
  have hdist := W.smooth_lipschitz.dist_le_mul
    (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (u i : ℝ)))
    (fun i => (v i : ℝ) / N i, physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))
  have hbound : ‖W.smooth (fun i => (u i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (u i : ℝ))) -
      W.smooth (fun i => (v i : ℝ) / N i,
      physicalGridFactorInput W.cover poly (fun i => (v i : ℝ)))‖ ≤ (L : ℝ) * ε := by
    rw [dist_eq_norm, Prod.dist_eq] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (max_le hspatial htag) L.coe_nonneg)
  simp only [eval, hres, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (W.mask_bound _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hbound)

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
          (p + 2 + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_affine_cell_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hbudget : 0 ≤ (p + 2 + C) ^ C := by positivity
  have hPfreeze (k : K) : Real.exp (p + (3 * (2 * p + 2) + 16)) ≤ (P k : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hP k)
  have hperiod' : ((M : ℕ) : ℝ) ≤ Real.exp (2 * p + 2) :=
    hperiod.trans (Real.exp_le_exp.mpr (by linarith))
  have hfreeze : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) →
      ‖twist u - twist v‖ ≤ variation *
        (2 * (Real.exp (-(2 * (2 * p + 2))) / 4)) := by
    intro u v hres hnear
    exact hvariation u v hres _ (by positivity) hnear
  obtain ⟨T, hTq, hTlen, hTside, hcorr⟩ :=
    NormalizedPolynomialTwist.exists_niltest_pair_correlation_subrectangle_of_variation
      S hq hlen (by linarith : 0 ≤ 2 * p + 2) hS hPfreeze hM hperiod'
      twist htwist hfreeze V W hV hWnorm (Real.exp_pos (-p)) hbias
  have herror : Real.exp p *
      (variation * (2 * (Real.exp (-(2 * (2 * p + 2))) / 4))) ≤
      Real.exp (-p) / 4 := by
    convert nativeTwistedSlice_freezing_error hp hvariation_nonneg hvariation_bound
      (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) using 1
    ring
  have hbias' : Real.exp (-(p + 2)) ≤ ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
      V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
        W.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ :=
    (nativeTwistedSlice_bias_precision p).trans (by linarith)
  have hTside' (k : K) : Real.exp (-(7 * p + 22)) * (P k : ℝ) ≤ T.length k := by
    simpa only [show p + (3 * (2 * p + 2) + 16) = 7 * p + 22 by ring] using hTside k
  have hlong (k : K) : Real.exp ((p + 2 + C) ^ C) ≤ (T.length k : ℝ) := by
    calc
      _ = Real.exp (-(7 * p + 22)) * Real.exp ((p + 2 + C) ^ C + 7 * p + 22) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(7 * p + 22)) * (P k : ℝ) :=
        mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
      _ ≤ _ := hTside' k
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hphysical (k : K) : Real.exp (-(7 * p + 22)) *
      ((P k : ℝ) / (q * M : ℕ)) ≤ T.length k := by
    apply le_trans _ (hTside' k)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact div_le_self (hPpos k).le (by exact_mod_cast hTq)
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have htwo : 2 ≤ S.length k₀ := by
    have he := S.length_large_of_cost hS hPfreeze k₀
    have ht := Real.add_one_le_exp (3 * (2 * p + 2) + 16)
    have : (2 : ℝ) ≤ S.length k₀ := by linarith
    exact_mod_cast this
  have hstride : ((q * M : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 * Real.exp p) * Real.exp p :=
        mul_le_mul (S.stride_le_twice_exp_cost k₀ htwo (hS k₀)) hperiod
          (Nat.cast_nonneg _) (by positivity)
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) := by
        have := Real.add_one_le_exp 1
        nlinarith [mul_pos (Real.exp_pos p) (Real.exp_pos p)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp' : p ≤ p + 2 := by linarith
  obtain ⟨b, ω, hF, hb, hf⟩ := hstep D E V W (by linarith : 2 ≤ p + 2)
    (by linarith : 0 ≤ 7 * p + 22) (by linarith : 0 ≤ 2 * p + 1)
    (hV.mono hp') (hW.mono hp') _ hTq hstride (fun k => (T.start k : ℤ)) η θ
    (fun i => (hηheight i).trans hp') (fun i => (hθheight i).trans hp') hη hθ
    0 T.length (fun k => (P k : ℝ)) hTlen hPpos (hK.trans hp') hlong hphysical hbias'
  refine ⟨b, ω, hF, hb, ?_⟩
  convert hf using 1; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

theorem AllocatedCenteredFramedRecoveredSampleAt.twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (x y : LayerSamplerVariables G I n B → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hy : ∀ k, |(y k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hxy : ∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ layerSamplerBox B U b S k * δ)
    (hmod : ∀ k, (x k : ZMod W.modulus) = (y k : ZMod W.modulus))
    (hcover : ∀ k, (x k : ZMod W.cover) = (y k : ZMod W.cover)) :
    ‖W.eval N poly (jointIntegerPhysicalSite x (a, v)) -
      W.eval N poly (jointIntegerPhysicalSite y (a, v))‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  let D : ℝ := (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hε : 0 ≤ D * δ := mul_nonneg hD hδ
  have htag := h.integerFullChart_torus_dist B U b hb o S hR hσ poly hm hp c a v sample read
    W.cover W.cover_pos x y hcover hε
    (fun j i => allocatedLayerSupported_polynomial_variation B U b o hR hσ S hσ1 C hC hchart
      hsmall j (sample j) (h.2.2.1 j).2 _ _ hδ hx hy hxy i)
  have htag' : dist (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)))
      (physicalGridFactorInput W.cover poly (fun z => (jointIntegerPhysicalSite y (a, v) z : ℝ))) ≤ (1 + D) * δ := by
    apply htag.trans
    have hc : (1 : ℝ) ≤ W.cover := by exact_mod_cast W.cover_pos
    exact (div_le_self hε hc).trans (by nlinarith)
  have hspatial := narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτ1 hξ N hN
    (layerSamplerBox B U b S)
    (fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k))
    (layerSamplerBox_sum_le_zero_root_budget B U b S) a v hv x y hδ hxy
  have hres : (fun z => (jointIntegerPhysicalSite x (a, v) z : ZMod W.modulus)) =
      (fun z => (jointIntegerPhysicalSite y (a, v) z : ZMod W.modulus)) := by
    funext z
    simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
      Int.cast_add, Int.cast_sum, Int.cast_mul, hmod]
  have hout := W.eval_sub_eval_of_component_dist N poly _ _ hres
    (hspatial.trans (show δ ≤ (1 + D) * δ by nlinarith)) htag'
  exact hout.trans_eq (by dsimp [D]; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

theorem AllocatedCenteredFramedRecoveredSampleAt.frozen_twist_variation
    [Fintype X]
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (x y : integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (hres : ∀ i, (x.val i : ZMod (W.modulus * W.cover)) = (y.val i : ZMod (W.modulus * W.cover)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ i, |(x.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ) -
      (y.val i : ℝ) /
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val : ℕ) : ℝ)| ≤ δ) :
    ‖W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) x.val) -
      W.eval N poly (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) y.val)‖ ≤
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) * δ := by
  classical
  let xx := finiteSplitPoint keep x.val fixed
  let yy := finiteSplitPoint keep y.val fixed
  have hT : ∀ i, 0 < layerSamplerBox B U b S i :=
    fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)
  have hxy : ∀ i, |(xx i : ℝ) - (yy i : ℝ)| ≤ layerSamplerBox B U b S i * δ := by
    intro i
    by_cases hi : keep i
    · have hc := hcell ⟨i, hi⟩
      rw [← allocatedParameterBox_side_eq B U b S i, ← sub_div, abs_div,
        abs_of_pos (hT i)] at hc
      simpa only [xx, yy, finiteSplitPoint, dif_pos hi, mul_comm] using
        (div_le_iff₀ (hT i)).mp hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi, sub_self, abs_zero]
      exact mul_nonneg (hT i).le hδ
  have hmod : ∀ i, (xx i : ZMod W.modulus) = (yy i : ZMod W.modulus) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_right W.modulus W.cover) (ZMod W.modulus))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dif_pos hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi]
  have hcover : ∀ i, (xx i : ZMod W.cover) = (yy i : ZMod W.cover) := by
    intro i
    by_cases hi : keep i
    · have hc := congrArg (ZMod.castHom (dvd_mul_left W.cover W.modulus) (ZMod W.cover))
        (hres ⟨i, hi⟩)
      simpa only [map_intCast, xx, yy, finiteSplitPoint, dif_pos hi] using hc
    · simp only [xx, yy, finiteSplitPoint, dif_neg hi]
  rw [allocatedFrozenIntegerFullChart_spatial, allocatedFrozenIntegerFullChart_spatial]
  exact h.twist_variation B U b hb o S hR hσ poly hm hp c a N hN hτ hτ1 hξ v hv sample read
    hσ1 C hC hchart hsmall W xx yy hδ
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed x.val x.property)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed y.val y.property)
    hxy hmod hcover

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFrozenTaggedTwistFixedBasisStepDrop
namespace OAI

universe u

section

namespace Erdos3
open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_fixed_basis_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (c : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ν : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ ν i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (c i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (c.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
        ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      (pi (pairModels D E)).filtration.ControlledSymbolFactorization c ν hC
        (pairFrequency η θ) (fun k => (P k : ℝ))
        (pairOrbitSymbol D E V.orbit W.orbit c ν hC)
        ((fixedAdaptedSymbolTransferInput pGeo
          (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_twist_variation_slice_step_drop s hs
  obtain ⟨A, hA, hfixed⟩ := exists_fixed_adapted_symbol_factorization_basis s
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨c, ν, N, hc, _, _, hforward, hinverse, _, _, _, _, _, htransfer⟩ :=
    hfixed (pi (pairModels D E)) hpGeo hGeo
  refine ⟨c, ν, hc, hforward, hinverse, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  obtain ⟨b, ω, hF, hb, hfactor⟩ := hstep S hq hlen hp hS hP hM hperiod
    twist htwist hvariation_nonneg hvariation_bound hvariation
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  let cost := (p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hqGeo : pGeo ≤ pGeo + p + cost := by linarith
  have hqP : p ≤ pGeo + p + cost := by linarith
  have hqCost : cost ≤ pGeo + p + cost := by linarith
  have hbase : (p + 2 + C) ^ C ≤ cost := by
    dsimp only [cost]
    linarith [show 0 ≤ (s : ℝ) * (9 * p + 23) by positivity]
  have htransferred := htransfer hqGeo (hK.trans hqP) b ω hF
    (fun i j => (hb i j).trans (hbase.trans hqCost)) (fun k => (P k : ℝ)) hPpos
    (pairFrequency η θ) (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
    (hfactor.mono (pi (pairModels D E)).filtration b ω hF hqCost hPpos)
  rw [pairOrbitSymbol_basis_independent D E V.orbit W.orbit b ω hF c ν hc] at htransferred
  exact htransferred

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

theorem exists_allocated_frozen_tagged_twist_fixed_basis_step_drop
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (bFixed : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ωFixed : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hFixed : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (bFixed '' {i | k ≤ ωFixed i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (bFixed i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (bFixed.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I Deck J : Fin m → Type*}
      [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      (hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
      (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag R σ)
      (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j)
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (_hN : ∀ x, 0 < N x)
      {τ ξ : ℝ} (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hξ : ξ ≤ 1)
      (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
      (_hv : v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1)
      (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
      (_hread : AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag o S hR hσ poly hm c a v sample read)
      (_hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (_hCgeo : ∀ j, 0 ≤ Cgeo j)
      (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
      (_hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {p : ℝ} (_hp : 0 ≤ p)
      (_hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
      (_hvariationBound : (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
      (keep : LayerSamplerVariables G I n B → Prop) [Nonempty {i // keep i}]
      (fixed : {i // ¬keep i} → ℤ)
      (_hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val),
      let P := fun i : {i // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val
      let β := allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed
      ∀ {q : ℕ} (Q : ResidueBoxSlice P q) (_hq : 0 < q)
        (hlen : ∀ i, 0 < Q.length i)
        (_hQ : ∀ i, Real.exp (-p) * (P i : ℝ) ≤ Q.length i)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P i : ℝ))
        (V : D.Niltest (fun _ : {i // keep i} => 1))
        (W : E.Niltest (fun _ : {i // keep i} => 1))
        (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
        (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
        (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
        (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
        (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
        (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = CircleFourier.character
            ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
        (_hK : (Fintype.card {i // keep i} : ℝ) ≤ p)
        (_hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
          star (twist.eval N poly (integerSampledSpatial β t.val)) *
            (V.eval t.val * W.eval t.val))‖),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization bFixed ωFixed hFixed
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit bFixed ωFixed hFixed)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_native_twist_variation_slice_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨bFixed, ωFixed, hFixed, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨bFixed, ωFixed, hFixed, hforward, hinverse, ?_⟩
  intro m G X _ _ I Deck J _ _ n B _ U btag hbtag o R σ S hR hσ poly hm hpoly
    c a N hN τ ξ hτ hτ1 hξ v hv sample read hread hσ1 Cgeo hCgeo hchart hsmall
    periodCap coverCap L twist p hp hperiod hvariationBound keep _ fixed hfixed
  dsimp only
  intro q Q hq hlen hQ hP V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  apply hlocal Q hq hlen hp hQ hP (mul_pos twist.modulus_pos twist.cover_pos)
    hperiod (fun t => twist.eval N poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed) t.val))
    (fun _ => twist.norm_eval_le N poly _)
    (by positivity) hvariationBound ?_
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  intro x y hres δ hδ hcell
  exact hread.frozen_twist_variation B U btag hbtag o S hR hσ poly hm hpoly
    c a N hN hτ hτ1 hξ v hv sample read hσ1 Cgeo hCgeo hchart hsmallOne
    twist keep fixed hfixed x y hres hδ hcell

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw
namespace OAI

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

def retainedParameter (x : LayerSamplerVariables G I n B → ℤ) : C.Variables → ℤ :=
  fun i => x i.val

@[simp] theorem retainedParameter_parameter (u : C.Variables → ℤ) :
    C.retainedParameter (C.parameter u) = u := by
  funext i
  exact finiteSplitPoint_fixed C.keep u C.fixed i

noncomputable abbrev SlicePoint := ↥C.slice.integerPoints

noncomputable def sliceSite (u : C.SlicePoint) : A.Site :=
  C.site u.val (C.slice.integerPoints_subset_integerBox u.property)

@[simp] theorem sliceSite_val (u : C.SlicePoint) :
    (C.sliceSite u).val = C.parameter u.val := rfl

@[simp] theorem physical_sliceSite (u : C.SlicePoint) :
    A.physical C.path (C.sliceSite u) = C.physical u.val := rfl

noncomputable def localLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset C.slice.integerPoints C.dense.nonempty).finitePushforward
    C.sliceSite

theorem localLaw_complexMean_parameter (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      𝔼 u ∈ C.slice.integerPoints, f (C.parameter u) := by
  rw [localLaw, FiniteProbabilityWeights.complexMean_finitePushforward]
  exact FiniteProbabilityWeights.uniformFinset_complexMean _ _ (fun u => f (C.parameter u))

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

noncomputable def siteValue (site : A.Site) : D.Space :=
  candidate.value (C.retainedParameter site.val)

@[simp] theorem siteValue_sliceSite (u : C.SlicePoint) :
    candidate.siteValue (C.sliceSite u) = candidate.value u.val := by
  unfold siteValue
  rw [C.sliceSite_val, C.retainedParameter_parameter]

theorem localLaw_score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (C.localLaw.complexMean (fun site => weight (A.physical C.path site) *
      observable (A.physical C.path site) (candidate.siteValue site))).re =
      candidate.score observable weight := by
  unfold score siteValue
  have h := C.localLaw_complexMean_parameter (fun x =>
    weight (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)) *
    observable (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))
      (candidate.value (C.retainedParameter x)))
  simp only [C.retainedParameter_parameter] at h
  exact congrArg Complex.re h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSlicePoints (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

theorem fullSlicePoints_image_val (S : ResidueBoxSlice N q) :
    S.fullSlicePoints.image Subtype.val = S.integerPoints := by
  simp only [fullSlicePoints, integerPoints, Finset.image_image]
  rfl

theorem expect_fullSlicePoints (S : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : integerBox N → V) :
    (𝔼 x ∈ S.fullSlicePoints, f x) = 𝔼 u, f (S.fullSlicePointInIntegerBox u) :=
  Finset.expect_image (S.fullSlicePointInIntegerBox_injective hq).injOn

theorem fullSliceLaw_complexMean_eq_expect_points (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 x ∈ S.fullSlicePoints, f x := by
  rw [S.fullSliceLaw_complexMean hlen]
  exact (S.expect_fullSlicePoints hq f).symm

end Erdos3.ResidueBoxSlice

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (k : ℕ) (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (C.physical u x : ℝ)) (lowTaggedPolynomial J k poly i) -
      (C.centerLift (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k C.integerChart u i : ℝ)| ≤ 1 / 8 := by
  rw [← C.integerChart_spatial]
  exact C.recovered.integerFrozenFullChart_low_residual B U b hb o S hR hσ poly hm
    hσ1 H hH hchart hsmall hp C.centerLift C.path.1.val C.path.2.val C.sample C.read
    C.keep C.fixed C.fixed_in_box k u hu i

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def fullTaggedPhysicalIntegerPoint {m : ℕ} {X : Type*}
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  Sum.elim x (fun a => round (eval (fun i => (x i : ℝ)) (poly a.1) a.2 - c a.1 a.2))

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_tag_eq_round (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (j : Fin m) (i : J j) :
    C.chartValues u (Sum.inr ⟨j, i⟩) =
      round (eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i) := by
  have hj : j.val + 1 ≤ m + 1 := by omega
  have hr := C.low_residual hσ1 H hH hchart hsmall hp (m + 1) u hu
    (lowTaggedSlot J (m + 1) j hj i)
  rw [lowTaggedPolynomial_eval] at hr
  simp only [integerSampledLowTags] at hr
  rw [lowTaggedIndex_slot] at hr
  change |eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i -
    (C.chartValues u (Sum.inr ⟨j, i⟩) : ℝ)| ≤ 1 / 8 at hr
  symm
  apply round_eq_iff.mpr
  have hb := abs_le.mp hr
  constructor <;> linarith

theorem chartValues_eq_physicalIntegerPoint (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) := by
  funext a
  rcases a with x | ⟨j, i⟩
  · exact C.chartValues_spatial u x
  · exact C.chartValues_tag_eq_round hσ1 H hH hchart hsmall hp u hu j i

theorem chartValues_eq_physicalIntegerPoint_on_slice (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) :=
  C.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp u
    (C.slice.integerPoints_subset_integerBox hu)

theorem chartValues_eq_physicalIntegerPoint_of_center
    (c : ∀ j, U j) (hc : C.centerLift = c) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (c j).val) (C.physical u) := by
  rw [← hc]
  exact C.chartValues_eq_physicalIntegerPoint_on_slice hσ1 H hH hchart hsmall hp u hu

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

def zeroLayerPhysicalPoint (x : X → ℤ) : X ⊕ Sigma J → ℤ :=
  Sum.elim x (fun a => Fin.elim0 a.1)

noncomputable def zeroLayerSpatialChart : X ⊕ Sigma J → MvPolynomial X ℝ :=
  Sum.elim MvPolynomial.X (fun a => Fin.elim0 a.1)

theorem zeroLayerSpatialChart_support (v : X ⊕ Sigma J) :
    zeroLayerSpatialChart v ∈ weightedSupportLE (fun _ : X => 1)
      (fullTaggedVariableWeight J v) := by
  rcases v with x | a
  · exact weightedSupportLE_X (fun _ : X => 1) x
  · exact Fin.elim0 a.1

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (A : PolynomialPatch V s d)

noncomputable def ofZeroLayerShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) : PolynomialPatch X s d :=
  A.ofWeightedChartShearOrbit (fullTaggedVariableWeight J)
    zeroLayerSpatialChart zeroLayerSpatialChart_support g

@[simp] theorem ofZeroLayerShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofZeroLayerShearOrbit g).kernel = A.kernel := rfl

@[simp] theorem ofZeroLayerShearOrbit_complexity
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    relativePatchComplexity (A.ofZeroLayerShearOrbit g) = relativePatchComplexity A := rfl

variable [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
  {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]

structure AllocatedFrozenTaggedContext where
  U : ∀ j, Submodule ℝ (J j → ℝ)
  btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ
  hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))
  o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))
  R : Fin m → ℝ
  σ : Fin m → ℝ
  S : LayerSamplerScale (G := G) B U btag R σ
  hR : ∀ j, 0 < R j
  hσ : ∀ j, 0 < σ j
  poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)
  hm : ∀ j d, coefficients (poly j) d ∈ U j
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  N : X → ℕ
  hN : ∀ x, 0 < N x
  τ : ℝ
  ξ : ℝ
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  periodCap : ℝ
  coverCap : ℝ
  L : ℝ≥0

variable {B}

def AllocatedFrozenTaggedContext.sides
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (keep : LayerSamplerVariables G I n B → Prop) : {i // keep i} → ℕ :=
  fun i => Sum.elim (fun _ : G => Γ.S.value)
    (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val

variable {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG]
  [LieRing MG] [LieAlgebra ℚ MG] {s d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
  [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]

structure AllocatedFrozenTaggedPairInput
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
    (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
    (p : ℝ) where
  twist : NormalizedPolynomialTwist X (Σ j, J j) Γ.periodCap Γ.coverCap Γ.L
  c : ∀ j, Γ.U j
  a : X → ℤ
  v : Option (LayerSamplerVariables G I n B) × X → ℤ
  hv : v ∈ rectangularWeightIndices 0
    (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B Γ.U Γ.btag Γ.S (fun _ => 0))
      Γ.τ Γ.ξ Γ.N) 1
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ
  hread : AllocatedCenteredFramedRecoveredSampleAt B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S
    Γ.hR Γ.hσ Γ.poly Γ.hm c a v sample read
  fixed : {i // ¬keep i} → ℤ
  hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
    Sum.elim (fun _ : G => Γ.S.value) (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val
  q : ℕ
  Q : ResidueBoxSlice (Γ.sides keep) q
  hq : 0 < q
  hlen : ∀ i, 0 < Q.length i
  hQ : ∀ i, Real.exp (-p) * (Γ.sides keep i : ℝ) ≤ Q.length i
  V : D.Niltest (fun _ : {i // keep i} => 1)
  W : E.Niltest (fun _ : {i // keep i} => 1)
  hp : 0 ≤ p
  hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p
  hvariationBound : (Γ.L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : V.ComplexityLE p
  hW : W.ComplexityLE p
  hWnorm : W.normBound ≤ 1
  η : LG →ₗ[ℚ] ℚ
  θ : MG →ₗ[ℚ] ℚ
  hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p
  hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p
  hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    V.observable (z • x) = CircleFourier.character
      ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x
  hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
    W.observable (z • x) = CircleFourier.character
      ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
    star (twist.eval Γ.N Γ.poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B Γ.U Γ.btag Γ.o Γ.poly Γ.hm c a v sample keep fixed)
      t.val)) * (V.eval t.val * W.eval t.val))‖

theorem exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (b.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
      ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
        {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
        (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
        (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
        [Nonempty {i // keep i}] {p : ℝ}
        (input : AllocatedFrozenTaggedPairInput Γ Deck keep D E p)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency input.η input.θ) (fun k => (Γ.sides keep k : ℝ))
          (pairOrbitSymbol D E input.V.orbit input.W.orbit b ω hF)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_allocated_frozen_tagged_twist_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨b, ω, hF, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨b, ω, hF, hforward, hinverse, ?_⟩
  intro m G X _ _ I J _ _ n B _ Γ Deck keep _ p input hP
  exact hlocal B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S Γ.hR Γ.hσ Γ.poly Γ.hm Γ.hpoly
    input.c input.a Γ.N Γ.hN Γ.hτ Γ.hτ1 Γ.hξ input.v input.hv input.sample
    input.read input.hread Γ.hσ1 Γ.Cgeo Γ.hCgeo Γ.hchart Γ.hsmall input.twist
    input.hp input.hperiod input.hvariationBound keep input.fixed input.hfixed
    input.Q input.hq input.hlen input.hQ hP input.V input.W input.hV input.hW
    input.hWnorm input.η input.θ input.hηheight input.hθheight input.hη input.hθ
    input.hK input.hbias

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def frozenTaggedContext
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (periodCap coverCap : ℝ) (Lip : ℝ≥0) :
    AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B where
  U := U
  btag := b
  hbtag := hb
  o := o
  R := R
  σ := σ
  S := S
  hR := hR
  hσ := hσ
  poly := poly
  hm := hm
  hpoly := hpoly
  N := N
  hN := A.size_pos
  τ := τ
  ξ := ξ
  hτ := A.trim_pos
  hτ1 := hτ1
  hξ := hξ
  hσ1 := hσ1
  Cgeo := Cgeo
  hCgeo := hCgeo
  hchart := hchart
  hsmall := hsmall
  periodCap := periodCap
  coverCap := coverCap
  L := Lip

end AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem localLaw_complexMean_eq_fullSliceLaw
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.parameter t.val)) := by
  rw [C.localLaw_complexMean_parameter,
    C.slice.fullSliceLaw_complexMean_eq_expect_points _ C.step_pos,
    ← C.slice.fullSlicePoints_image_val]
  exact Finset.expect_image Subtype.val_injective.injOn

end AllocatedExternalLocalChart

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

def ofCandidate
    (hcorr : Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (C.physical t.val)) *
          (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p where
  twist := twist
  c := C.centerLift
  a := C.path.1.val
  v := C.path.2.val
  hv := by
    change C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  sample := C.sample
  read := C.read
  hread := C.recovered
  fixed := C.fixed
  hfixed := C.fixed_in_box
  q := C.step
  Q := C.slice
  hq := C.step_pos
  hlen := C.slice.length_pos_of_dense C.dense
  hQ := fun i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg (A.sides i.val))).trans
        (C.slice.length_lower_of_dense C.step_pos C.dense i)
  V := reference.withOrbit candidate.orbit
  W := partner.integerChartPullback (fun _ : C.Variables => 1) C.integerChart C.integerChart_support
  hp := hp
  hperiod := hperiod
  hvariationBound := hvariation
  hV := hV
  hW := hW
  hWnorm := hWnorm
  η := η
  θ := θ
  hηheight := hηheight
  hθheight := hθheight
  hη := hη
  hθ := hθ
  hK := hK
  hbias := by
    change Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (integerSampledSpatial C.integerChart t.val)) *
          ((reference.withOrbit candidate.orbit).eval t.val *
            (partner.integerChartPullback (fun _ : C.Variables => 1)
              C.integerChart C.integerChart_support).eval t.val))‖
    simp only [C.integerChart_spatial, Niltest.integerChartPullback_eval,
      Niltest.withOrbit_eval]
    exact hcorr

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

local notation "candidateInput" => ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  C candidate reference partner twist hp hcost hperiod hvariation hV hW hWnorm
  η θ hηheight hθheight hη hθ hK hcorr

@[simp] theorem ofCandidate_V_orbit :
    (candidateInput).V.orbit = candidate.orbit := rfl

@[simp] theorem ofCandidate_W_orbit :
    (candidateInput).W.orbit =
      (partner.integerChartPullback (fun _ : C.Variables => 1)
        C.integerChart C.integerChart_support).orbit := rfl

def ofCandidate_of_localLaw
    (hcorr : Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
      star (twist.eval N poly (A.physical C.path site)) *
        (reference.observable (candidate.value (C.retainedParameter site.val)) *
          partner.eval (fullTaggedPhysicalIntegerPoint J poly
            (fun j => (C.centerLift j).val) (A.physical C.path site))))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p := by
  apply ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall C candidate
    reference partner twist hp hcost hperiod hvariation hV hW hWnorm
    η θ hηheight hθheight hη hθ hK
  have he := C.localLaw_complexMean_eq_fullSliceLaw (fun x =>
    star (twist.eval N poly (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter x)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))))
  change Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
    star (twist.eval N poly (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter site.val)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val)))))‖ at hcorr
  rw [he] at hcorr
  have hf : (fun t : integerBox (fun i : C.Variables => A.sides i.val) =>
      star (twist.eval N poly (C.physical t.val)) *
        (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val))) =
      (fun t => star (twist.eval N poly
        (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))) *
          (reference.observable (candidate.value (C.retainedParameter (C.parameter t.val))) *
            partner.eval (fullTaggedPhysicalIntegerPoint J poly
              (fun j => (C.centerLift j).val)
              (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))))) := by
    funext t
    rw [C.retainedParameter_parameter,
      C.chartValues_eq_physicalIntegerPoint hσ1 Cgeo hCgeo hchart hsmall hpoly t.val t.property]
    rfl
  rw [hf]
  exact hcorr

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

theorem withKeep_localLaw {cost : ℝ} {Deck : Fin m → Type*}
    (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep) :
    (C.withKeep keep hkeep).localLaw = C.localLaw := by
  cases hkeep
  rfl

end AllocatedExternalLocalChart

structure AllocatedExternalCandidateTaggedPairFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p periodCap coverCap : ℝ) (Lip : ℝ≥0) where
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  sourceChart : Ω → AllocatedExternalLocalChart (E := Deck) A cost
  keep_eq : ∀ a, (sourceChart a).keep = keep
  sourceCandidate : ∀ a, AllocatedExternalLocalCandidate (sourceChart a) D Fmark φ marked
  reference : Ω → Pivot → D.Niltest (fullTaggedVariableWeight (X := X) J)
  ambient : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected_orbit : ∀ j, (selected j).orbit = (ambient j).orbit
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hcost : cost ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE p
  hW : ∀ j, (selected j).ComplexityLE p
  hWnorm : ∀ j, (selected j).normBound ≤ 1
  η : Pivot → LG →ₗ[ℚ] ℚ
  θ : ∀ j, MG j →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hθheight : ∀ j i, rationalLogHeight (θ j ((E j).basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hθ : ∀ j z, z ∈ (E j).filtration.realification.subgroup s → ∀ x,
    (selected j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (θ j) z.coord : ℝ) : CircleFourier.Circle) * (selected j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hcorr : ∀ a j,
    let C := (sourceChart a).withKeep keep (keep_eq a)
    let candidate := (sourceCandidate a).withKeep keep (keep_eq a)
    Real.exp (-p) ≤ ‖(sourceChart a).localLaw.complexMean (fun site =>
      star ((twist a j).eval N poly (A.physical (sourceChart a).path site)) *
        ((reference a j).observable (candidate.value (C.retainedParameter site.val)) *
          (selected j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((sourceChart a).centerLift k).val)
            (A.physical (sourceChart a).path site))))‖

namespace AllocatedExternalCandidateTaggedPairFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

def context : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B :=
  A.frozenTaggedContext F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    periodCap coverCap Lip

@[simp] theorem context_sides : F.context.sides keep = fun i => A.sides i.val := rfl

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

@[simp] theorem chart_keep (a : Ω) : (F.chart a).keep = keep := rfl

@[simp] theorem chart_localLaw (a : Ω) : (F.chart a).localLaw = (F.sourceChart a).localLaw := by
  exact (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

def input (a : Ω) (j : Pivot) :
    AllocatedFrozenTaggedPairInput F.context Deck keep D (E j) p :=
  AllocatedFrozenTaggedPairInput.ofCandidate_of_localLaw A
    F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    (F.chart a) (F.candidate a) (F.reference a j) (F.selected j) (F.twist a j)
    F.hp F.hcost (F.hperiod a j) F.hvariation (F.hV a j) (F.hW j) (F.hWnorm j)
    (F.η j) (F.θ j) (F.hηheight j) (F.hθheight j) (F.hη a j) (F.hθ j) F.hK
    (by rw [F.chart_localLaw]; exact F.hcorr a j)

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => ((F.ambient j).integerChartPullback (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

@[simp] theorem input_η (a : Ω) (j : Pivot) : (F.input a j).η = F.η j := rfl

@[simp] theorem input_θ (a : Ω) (j : Pivot) : (F.input a j).θ = F.θ j := rfl

@[simp] theorem input_V_orbit (a : Ω) (j : Pivot) :
    (F.input a j).V.orbit = (F.candidate a).orbit := rfl

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI

end


