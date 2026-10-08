-- Prove2me | Definitions.Def_OAIErdos3B013
-- name    : OAIErdos3B013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T10:24:53.849332+00:00
-- url     : https://prove2.me/theorems/2e3749d8-758c-444a-af36-d77cf0dc0752
-- title:
--   OpenAI Erdős-3 split, definitions bundle 14 of 88
-- statement:
--   Definitions bundle 14 of 88 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B012`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 14 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.integer_difference_exists_pivot`, `OAI.Erdos3.BooleanCubeKernel.mem_rectangular_zero_radius_iff`, `OAI.Erdos3.BooleanCubeKernel.mem_spatialWindow_iff`, `OAI.Erdos3.BooleanCubeKernel.spatialWindow`, `OAI.Erdos3.CellRefinement.CellBilinearBound`, `OAI.Erdos3.CellRefinement.centerChildIntegral`, `OAI.Erdos3.CellRefinement.centerChildPotential`, `OAI.Erdos3.CellRefinement.centerMatchedIntegral`, `OAI.Erdos3.CellRefinement.centerPotential`, `OAI.Erdos3.CellRefinement.centerSlice`, `OAI.Erdos3.CellRefinement.matchedIndependentAverage`, `OAI.Erdos3.CellRefinement.matchedIntegral`, `OAI.Erdos3.CellRefinement.matchedPairAverage`, `OAI.Erdos3.CellRefinement.parentMatchedAverage`, `OAI.Erdos3.CellRefinement.parentTruncatedIntegral`, `OAI.Erdos3.CellRefinement.refinementCostPolynomial`, `OAI.Erdos3.CellRefinement.refinementDepthPolynomial`, `OAI.Erdos3.CellRefinement.refinementFinalRankPolynomial`, `OAI.Erdos3.CellRefinement.refinementMatchPolynomial`, `OAI.Erdos3.CellRefinement.refinementRankPolynomial`, `OAI.Erdos3.CellRefinement.refinementRoundPolynomial`, `OAI.Erdos3.CellRefinement.refinementUnbalancedPolynomial`, `OAI.Erdos3.CellRefinement.refinementWidthPolynomial`, `OAI.Erdos3.CoordinateDecisionTree.liftOutside`, `OAI.Erdos3.CoordinateDecisionTree.outsideAssignment`, `OAI.Erdos3.CoordinateDecisionTree.relabel`, `OAI.Erdos3.CoordinateDecisionTree.relabelAssignment`, `OAI.Erdos3.PivotCompatible`, `OAI.Erdos3.PlateauSiteIndex`, `OAI.Erdos3.VectorPolynomial.allocatedFiniteIdealCoefficientLog`, `OAI.Erdos3.VectorPolynomial.allocatedFiniteIdealLipschitzLog`, `OAI.Erdos3.VectorPolynomial.allocatedFiniteIdealProfileLog`, `OAI.Erdos3.VectorPolynomial.allocatedFiniteIdeal_budget_nonneg`, `OAI.Erdos3.VectorPolynomial.idealSiteLogBudget_le_finite_profile`, `OAI.Erdos3.addCircle_int_div_eq_of_dvd_sub`, `OAI.Erdos3.affinePairLocations`, `OAI.Erdos3.affinePairModulus`, `OAI.Erdos3.affinePairRowsOfLocations`, `OAI.Erdos3.ambientL1FourierInput`, `OAI.Erdos3.ambientL1SamplingBudget`, `OAI.Erdos3.ambientL1SamplingBudget_bounds`, `OAI.Erdos3.basis_inr_repr_zero_of_mem_inl_span`, `OAI.Erdos3.blockTorusFactor`, `OAI.Erdos3.booleanSelectedInjection`, `OAI.Erdos3.chordBoxCutoff`, `OAI.Erdos3.commonExtractionParameter`, `OAI.Erdos3.commonExtractionParameter_controls`, `OAI.Erdos3.commonExtractionParameter_products`, `OAI.Erdos3.commonInitialParameter`, `OAI.Erdos3.commonTerminalParameter`, `OAI.Erdos3.commonTerminalParameter_controls`, `OAI.Erdos3.coordinate_edist_le_mul_pathELength`, `OAI.Erdos3.coordinate_edist_le_of_riemannianEDist_lt`, `OAI.Erdos3.coordinate_edist_le_of_short_path`, `OAI.Erdos3.coordinate_path_stays_in_closedBall`, `OAI.Erdos3.countingKernelAverage`, `OAI.Erdos3.doublePowerParameter`, `OAI.Erdos3.doublePowerParameter_controls`, `OAI.Erdos3.exists_allocatedMarkedCoveredLowerDiagramBudget`, `OAI.Erdos3.exists_ambientL1SamplingThreshold_bound`, `OAI.Erdos3.exists_commonInitialParameter_budget`, `OAI.Erdos3.exists_commonTerminalParameter_budget`, `OAI.Erdos3.exists_doublePowerParameter_budget`, `OAI.Erdos3.exists_fastSymbolCorrectionBudget`, `OAI.Erdos3.exists_fastTerminalParameter_budget`, `OAI.Erdos3.exists_fast_removal_factor_budget`, `OAI.Erdos3.exists_fullInitialParameter_budget`, `OAI.Erdos3.exists_initial_removal_budget`, `OAI.Erdos3.exists_native_dependent_selection_budget`, `OAI.Erdos3.exists_normalizedTwistExtractionBudget`, `OAI.Erdos3.exists_reducedRelative_budget`, `OAI.Erdos3.exists_synchronizedCorrection_budget`, `OAI.Erdos3.exists_terminalComposition_budget`, `OAI.Erdos3.exists_translationCoordinate_budget`, `OAI.Erdos3.exists_translationMajorSeparated_budget`, `OAI.Erdos3.exists_translationMajor_detected_potential_budget`, `OAI.Erdos3.exists_vertical_pair_precision`, `OAI.Erdos3.exp_repeated_add_le`, `OAI.Erdos3.fastTerminalParameter`, `OAI.Erdos3.fastTerminalParameter_controls`, `OAI.Erdos3.finiteMomentPolynomial`, `OAI.Erdos3.finiteMomentPolynomial_coeff`, `OAI.Erdos3.finiteMomentPolynomial_eval`, `OAI.Erdos3.finiteMomentPolynomial_natDegree_le`, `OAI.Erdos3.finiteMomentPolynomial_ne_zero`, `OAI.Erdos3.forecastInactiveCharacterCoefficient`, `OAI.Erdos3.fullInitialParameter`, `OAI.Erdos3.fullInitialParameter_controls`, `OAI.Erdos3.gram_det_orthogonal_block`, `OAI.Erdos3.idealSiteLogBudget`, `OAI.Erdos3.idealSiteLogBudget_bounds`, `OAI.Erdos3.integerBoxMesh`, `OAI.Erdos3.integerBoxMeshCellEquiv`, `OAI.Erdos3.integerBoxMeshPoint`, `OAI.Erdos3.integerBoxMeshPointEquiv`, `OAI.Erdos3.integerNewtonPolynomial`, `OAI.Erdos3.integerPeriod_exists_pivot`, `OAI.Erdos3.integerPolynomial_eval_addCircle_div_eq`, `OAI.Erdos3.integerPolynomial_eval_sub_dvd`, `OAI.Erdos3.integerPolynomial_eval_zmod_eq`, `OAI.Erdos3.integerVectorResidue`, `OAI.Erdos3.jointSlicedPolynomial`, `OAI.Erdos3.lieTreeEval_eq_zero_of_leaf`, `OAI.Erdos3.lieTreeEval_pi`, `OAI.Erdos3.lieTreeSupport`, `OAI.Erdos3.linearIndependent_of_fixed_kernel_period`, `OAI.Erdos3.maskedSiteFactor`, `OAI.Erdos3.matchedCellSpace`, `OAI.Erdos3.matchedFirstCell`, `OAI.Erdos3.matchedSecondCell`, `OAI.Erdos3.momentProduct`, `OAI.Erdos3.momentProduct_ne_zero_some`, `OAI.Erdos3.normalizedBoxPartitions`, `OAI.Erdos3.normalizedGridLength_bounds`, `OAI.Erdos3.normalizedSupportPlateau`, `OAI.Erdos3.pivotCellForm`, `OAI.Erdos3.pivotGridFactor`, `OAI.Erdos3.pivotKernelFactor`, `OAI.Erdos3.pivotRootFactor`, `OAI.Erdos3.pivotStageCount`, `OAI.Erdos3.pivotStageIntegrand`, `OAI.Erdos3.plateauFourierMode`, `OAI.Erdos3.plateauModeMixture`, `OAI.Erdos3.polynomialSublevelThreshold_inverse_le_exp`, `OAI.Erdos3.principalProgressionSliceCenter`, `OAI.Erdos3.principalProgressionSliceWidth`, `OAI.Erdos3.principalSlicePolynomial`, `OAI.Erdos3.rationalBooleanSitePhase`, `OAI.Erdos3.rationalGridPhase`, `OAI.Erdos3.realLinearCharacter`, `OAI.Erdos3.realOrderedSlots`, `OAI.Erdos3.reducedRelativeParameter`, `OAI.Erdos3.reducedRelativeParameter_controls`, `OAI.Erdos3.regularizedImageDensity`, `OAI.Erdos3.regularizedImageMap`, `OAI.Erdos3.reindexedBlockCubeDomain`, `OAI.Erdos3.relativePatchSourceTest`, `OAI.Erdos3.relativePatchSourceTest_integer`, `OAI.Erdos3.scalarInitialReferencePolynomial`, `OAI.Erdos3.scalarSupportPlateau`, `OAI.Erdos3.selectedBooleanSiteRows`, `OAI.Erdos3.selectedDerivative`, `OAI.Erdos3.selectedInverseField`, `OAI.Erdos3.slicedPolynomialScale`, `OAI.Erdos3.slicedPrincipalBoundaryRadius`, `OAI.Erdos3.slicedPrincipalC2Tolerance`, `OAI.Erdos3.slicedPrincipalComparisonBudget`, `OAI.Erdos3.translationMajor_initial_budget_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B006
import Definitions.Def_OAIErdos3B007
import Definitions.Def_OAIErdos3B008
import Definitions.Def_OAIErdos3B009

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

noncomputable def selectedDerivative (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ U x).comp J

noncomputable def selectedInverseField (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) (x : κ → ℝ) : ℝ :=
  J ((selectedDerivative U J x).inverse (Pi.single i 1)) j

end Erdos3

end

section

namespace Erdos3

noncomputable def booleanSelectedInjection {B O F α : Type*}
    [Fintype O] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (v : F) (r : O → Option α) :
    (O → ℝ) →L[ℝ] (BlockParameter B F α → ℝ) :=
  coordinateInjection (fun col => (block col, v, r col))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RiemannianLocalCoordinates
namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]

theorem coordinate_edist_le_mul_pathELength {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, ∀ v : TangentSpace I (γ t),
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f (γ t) v)‖ₑ ≤ C * ‖v‖ₑ) :
    edist (f (γ a)) (f (γ b)) ≤ C * pathELength I γ a b := by
  have hsmooth : ContDiff ℝ 1 (f ∘ γ) := (hf.comp hγ).contDiff
  calc
    _ = ‖(f ∘ γ) b - (f ∘ γ) a‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc a b, ‖deriv (f ∘ γ) t‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hsmooth.contDiffOn hab
    _ ≤ ∫⁻ t in Icc a b, C * ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hchain := mfderiv_comp_apply t (hf.mdifferentiableAt one_ne_zero)
        (hγ.mdifferentiableAt one_ne_zero) 1
      rw [mfderiv_eq_fderiv] at hchain
      change deriv (f ∘ γ) t = tangentModelVector
        (mfderiv I 𝓘(ℝ, F) f (γ t) (mfderiv 𝓘(ℝ) I γ t 1)) at hchain
      rw [hchain]
      exact hbound t ht _
    _ = C * pathELength I γ a b := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, pathELength_eq_lintegral_mfderiv_Icc]

theorem coordinate_path_stays_in_closedBall {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) ∈ Metric.closedBall (f (γ 0)) r := by
  let A := {t : ℝ | f (γ t) ∈ Metric.closedBall (f (γ 0)) r}
  have hA : IsClosed (A ∩ Icc 0 1) :=
    ((Metric.isClosed_closedBall).preimage (hf.continuous.comp hγ.continuous)).inter isClosed_Icc
  have hzero : (0 : ℝ) ∈ A := Metric.mem_closedBall_self r.coe_nonneg
  apply hA.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
  intro t ht hAt
  have hvariation := coordinate_edist_le_mul_pathELength hf hγ ht.1
    (fun u hu => hbound (γ u) (hAt hu))
  have hlength : (C : ℝ≥0∞) * pathELength I γ 0 t ≤ C * pathELength I γ 0 1 := by
    gcongr
    exact ht.2.le
  have hlt : edist (f (γ 0)) (f (γ t)) < r := hvariation.trans_lt
    (hlength.trans_lt hshort)
  have hball : f (γ t) ∈ Metric.ball (f (γ 0)) r := by
    rw [← Metric.eball_coe, Metric.mem_eball, edist_comm]
    exact hlt
  have hnhds : {u | f (γ u) ∈ Metric.ball (f (γ 0)) r} ∈ 𝓝 t :=
    (Metric.isOpen_ball.preimage (hf.continuous.comp hγ.continuous)).mem_nhds hball
  exact Filter.mem_of_superset (nhdsWithin_le_nhds hnhds)
    (fun u hu => Metric.ball_subset_closedBall hu)

theorem coordinate_edist_le_of_short_path {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 :=
  coordinate_edist_le_mul_pathELength hf hγ zero_le_one
    (fun t ht => hbound (γ t) (coordinate_path_stays_in_closedBall hf hγ hbound hshort t ht))

end Erdos3

end

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

theorem coordinate_edist_le_of_riemannianEDist_lt {f : M → F} {C r : ℝ≥0}
    (hC : 0 < C) (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (x y : M)
    (hbound : ∀ z, f z ∈ Metric.closedBall (f x) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ)
    (hnear : (C : ℝ≥0∞) * riemannianEDist I x y < r) :
    edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  apply le_of_forall_gt
  intro q hq
  have hmin : (C : ℝ≥0∞) * riemannianEDist I x y < min q r := lt_min hq hnear
  have hinput : riemannianEDist I x y < min q r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hmin
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < min q r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  have hb : ∀ z, f z ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ := by
    simpa only [hγ0] using hbound
  have hv := coordinate_edist_le_of_short_path hf hγ hb (hmul.trans_le (min_le_right q r))
  rw [hγ0, hγ1] at hv
  exact hv.trans_lt (hmul.trans_le (min_le_left q r))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieTreeSupport
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

def lieTreeSupport : FreeMagma I → Set I
  | .of i => {i}
  | .mul a b => lieTreeSupport a ∪ lieTreeSupport b

theorem lieTreeEval_eq_zero_of_leaf (v : I → L) (a : FreeMagma I) {i : I}
    (hi : i ∈ lieTreeSupport a) (hv : v i = 0) : lieTreeEval v a = 0 := by
  induction a using FreeMagma.rec with
  | of j =>
    have hij : i = j := hi
    simpa only [lieTreeEval, ← hij] using hv
  | mul a b ha hb =>
    rcases hi with hi | hi
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [ha hi, zero_lie]
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [hb hi, lie_zero]

theorem lieTreeEval_pi (v : I → J → L) (a : FreeMagma I) (j : J) :
    lieTreeEval v a j = lieTreeEval (fun i => v i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v a j, lieTreeEval v b j⁆ =
      ⁅lieTreeEval (fun i => v i j) a, lieTreeEval (fun i => v i j) b⁆
    rw [ha, hb]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def affinePairLocations {I : Type*} (v : I → Fin 2 → ℤ) : (I → ℤ) × (I → ℤ) :=
  (fun i => v i 0, fun i => v i 1)

def affinePairRowsOfLocations {I : Type*} (xy : (I → ℤ) × (I → ℤ)) : I → Fin 2 → ℤ :=
  fun i => ![xy.1 i, xy.2 i]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerVectorResidue {I : Type*} (m : ℕ) (x : I → ℤ) : I → ZMod m :=
  fun i => (x i : ZMod m)

def affinePairModulus {J : Type*} [Fintype J] (t u : J → ℤ) : ℕ :=
  (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

noncomputable def normalizedSupportPlateau (H : ℝ) (x : J → ℝ) : ℝ :=
  linearCutoff H (1 / 4) ‖x‖

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PlateauFourierMode
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J]

noncomputable def realLinearCharacter (ω x : J → ℝ) : ℂ :=
  CircleFourier.character ((∑ j, ω j * x j : ℝ) : CircleFourier.Circle)

noncomputable def plateauFourierMode (H : ℝ) (ω x : J → ℝ) : ℂ :=
  (normalizedSupportPlateau H x : ℂ) * realLinearCharacter ω x

noncomputable def rationalGridPhase (D : ℕ) [NeZero D] (a : J → ℤ) (r : J → ZMod D) : ℂ :=
  CircleFourier.character (ZMod.toAddCircle (∑ j, (a j : ZMod D) * r j))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockTorusFactor (q h b : ℕ) (A : ℝ) : ℕ :=
  integerSupportTorusFactor (blockJetScaleBound q h b A)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedPlateauMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {T J : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable [Fintype J]

noncomputable def plateauModeMixture (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) : ℂ :=
  ∫ t, rationalGridPhase D a (integerGridResidue D (shift t)) *
    plateauFourierMode H (fun j => -ω j) (x - fun j => (shift t j : ℝ) / K) ∂p.toMeasure

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (offset : B → ℤ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IndependentIntegerSiteDirections
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem integer_difference_exists_pivot {K : Type*} [Fintype K] {q : ℕ}
    (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ))) :
    ∃ selection : Fin q → K, (integerDifferencePivot difference selection).det ≠ 0 := by
  let A : Matrix K (Fin q) ℝ := fun k i => difference i k
  obtain ⟨selection, hdet⟩ := exists_nonzero_row_minor A hlin
  have he : A.submatrix selection id = (realDifferencePivot
      (fun i k => (difference i k : ℝ)) selection).transpose := rfl
  rw [he, Matrix.det_transpose, ← integerDifferencePivot_det_cast] at hdet
  exact ⟨selection, fun hz => hdet (by rw [hz, Int.cast_zero])⟩

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrthogonalBlockGram
namespace OAI

section

namespace Erdos3

open Module

theorem basis_inr_repr_zero_of_mem_inl_span
    {α β E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Basis (α ⊕ β) ℝ E) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))) (j : β) :
    b.repr x (Sum.inr j) = 0 := by
  classical
  have hle : Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i))) ≤
      LinearMap.ker (b.coord (Sum.inr j)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    simp
  exact hle hx

theorem gram_det_orthogonal_block
    {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis (α ⊕ β) ℝ E) :
    let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
    (Matrix.gram ℝ b).det = (Matrix.gram ℝ (fun i : α => b (Sum.inl i))).det *
      (Matrix.gram ℝ (fun j : β => b (Sum.inr j) - U.starProjection (b (Sum.inr j)))).det := by
  classical
  let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
  let w : β → E := fun j => b (Sum.inr j) - U.starProjection (b (Sum.inr j))
  let g : (α ⊕ β) → E := Sum.elim (fun i => b (Sum.inl i)) w
  let C : Matrix α β ℝ := fun i j => -b.repr (U.starProjection (b (Sum.inr j))) (Sum.inl i)
  have hz (i j : β) : b.repr (U.starProjection (b (Sum.inr j))) (Sum.inr i) = 0 :=
    basis_inr_repr_zero_of_mem_inl_span b (U.starProjection_apply_mem _) i
  have hM : b.toMatrix g = Matrix.fromBlocks 1 C 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inl i) = (1 : Matrix α α ℝ) i j
        simp [Finsupp.single_apply, Matrix.one_apply, eq_comm]
      | inr j =>
        change b.repr (w j) (Sum.inl i) = C i j
        simp [w, C]
    | inr i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inr i) = 0
        simp
      | inr j =>
        change b.repr (w j) (Sum.inr i) = (1 : Matrix β β ℝ) i j
        simp [w, hz, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  have hdet : b.det g = 1 := by
    rw [b.det_apply, hM, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hgram : (Matrix.gram ℝ g).det = (Matrix.gram ℝ b).det := by
    rw [gram_det_basis_change b g, hdet, one_pow, one_mul]
  have horth (i : α) (j : β) : inner ℝ (b (Sum.inl i)) (w j) = 0 := by
    have hi : b (Sum.inl i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hi
      (Submodule.sub_starProjection_mem_orthogonal (K := U) (b (Sum.inr j)))
  have hblock : Matrix.gram ℝ g = Matrix.fromBlocks
      (Matrix.gram ℝ (fun i : α => b (Sum.inl i))) 0 0 (Matrix.gram ℝ w) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact horth i j
    | inr i =>
      cases j with
      | inl j =>
        change inner ℝ (w i) (b (Sum.inl j)) = 0
        rw [real_inner_comm]
        exact horth j i
      | inr j => rfl
  rw [← hgram, hblock, Matrix.det_fromBlocks_zero₂₁]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedCubeDomain
namespace OAI

section

namespace Erdos3

open MeasureTheory

def reindexedBlockCubeDomain {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N) : Set (Fin N → ℝ) :=
  (fun x => x ∘ e) ⁻¹' blockCubeDomain B F α

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialThresholdBudget
namespace OAI

section

namespace Erdos3

theorem polynomialSublevelThreshold_inverse_le_exp (n m : ℕ) {C scale η Pc Ps Pe : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η)
    (hPc : 0 ≤ Pc) (hPs : 0 ≤ Ps) (hPe : 0 ≤ Pe)
    (hCb : C ≤ Real.exp Pc) (hsb : scale ≤ Real.exp Ps) (hηb : η⁻¹ ≤ Real.exp Pe) :
    (polynomialSublevelThreshold n m C scale η)⁻¹ ≤
      Real.exp (Ps+2+(n : ℝ)*(Pc+m+Pe+2)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm : (m : ℝ)+1 ≤ Real.exp m := Real.add_one_le_exp _
  have hb : 2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1*Real.exp Pc*Real.exp m*Real.exp Pe := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbase : 1+2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+2) := by
    have he : Pc+m+Pe+1+1 = Pc+m+Pe+2 := by ring
    simpa only [he] using one_add_le_exp_succ (by positivity : 0 ≤ Pc+m+Pe+1) hb
  rw [polynomialSublevelThreshold, inv_inv]
  calc
    _ ≤ Real.exp 1*Real.exp (Ps+1)*(Real.exp (Pc+m+Pe+2))^n := by
      gcongr
      exact one_add_le_exp_succ hPs hsb
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

def regularizedImageMap {Ω I : Type*} (δ : ℝ≥0) (U : Ω → I → ℝ)
    (p : Ω × (I → ℝ)) : I → ℝ := U p.1 + (δ : ℝ) • p.2

noncomputable def regularizedImageDensity {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (U : Ω → I → ℝ) (δ : ℝ≥0) : (I → ℝ) → ℝ :=
  densityMixture μ (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPrincipalPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F : Type*} [Fintype B] [Fintype F]

noncomputable def principalSlicePolynomial (c : B → ℝ) (lower width : B × F → ℝ) :
    MvPolynomial (B × F) ℝ :=
  ∑ b, MvPolynomial.C (c b) * ∏ i,
    (MvPolynomial.C (lower (b, i)) + MvPolynomial.C (width (b, i)) * MvPolynomial.X (b, i))

section Joint

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPolynomial (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (o : Σ _d : D, Unit) :
    MvPolynomial (Σ d, B d × F d) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1) (principalSlicePolynomial (c o.1) (lower o.1) (width o.1))

end Joint

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalComparisonBudget (N m : ℕ) (C A r κ : ℝ) : ℝ :=
  1 + 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) +
    N * ((2 * κ⁻¹) ^ 2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPrincipalBoundaryRadius (N : ℕ) (η : ℝ) : ℝ :=
  min (1 / 4) (η / (16 * ((N : ℝ) + 1)))

noncomputable def slicedPrincipalC2Tolerance (N O m : ℕ) (C a δ A η : ℝ) : ℝ :=
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r) ^ m
  polynomialPerturbationScale κ⁻¹ 1 (slicedPrincipalComparisonBudget N m C A r κ) (η / 2) O

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def slicedPolynomialScale (N O Z m d : ℕ) (C M a δ A η : ℝ) : ℝ :=
  slicedPrincipalC2Tolerance N O m C a δ A η / (1 + polynomialMassC2Budget Z d M)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealOrderedSlots
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedSlots (B : ℝ) (a : NilpotentLieBCHGroup L s hnil) :
    TriangularSlots d where
  center x j := -e.repr (a * realOrderedBasisPrefixProduct e hnil j.val
    (fun k => B * x k)).coord j / B
  lower j x y h := by
    have hp : realOrderedBasisPrefixProduct e hnil j.val (fun k => B * x k) =
        realOrderedBasisPrefixProduct e hnil j.val (fun k => B * y k) := by
      apply realOrderedBasisPrefixProduct_congr
      intro k hk
      rw [h k hk]
    rw [hp]

namespace IsRealCentralLieBasis

variable [IsScalarTower ℚ ℝ L]
  {e}

end IsRealCentralLieBasis
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChordBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def chordBoxCutoff (a : ℝ) (h : ℝ≥0) (z : ι → ℂ) : ℝ :=
  ∏ i, linearCutoff a h ‖1 - z i‖

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteMomentPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open Polynomial

noncomputable def finiteMomentPolynomial {m : ℕ} (v : Fin m → ℂ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (v j) * Polynomial.X ^ j.val

theorem finiteMomentPolynomial_coeff {m : ℕ} (v : Fin m → ℂ) (j : Fin m) :
    (finiteMomentPolynomial v).coeff j.val = v j := by
  classical
  simp only [finiteMomentPolynomial, finsetSum_coeff, coeff_C_mul_X_pow, ← Fin.ext_iff]
  simp

theorem finiteMomentPolynomial_ne_zero {m : ℕ} {v : Fin m → ℂ} (hv : v ≠ 0) :
    finiteMomentPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hj := finiteMomentPolynomial_coeff v j
  rw [h, coeff_zero] at hj
  exact hj.symm

theorem finiteMomentPolynomial_natDegree_le {m : ℕ} (v : Fin m → ℂ) :
    (finiteMomentPolynomial v).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt j.isLt)

theorem finiteMomentPolynomial_eval {m : ℕ} (v : Fin m → ℂ) (z : ℂ) :
    (finiteMomentPolynomial v).eval z = ∑ j, v j * z ^ j.val := by
  simp [finiteMomentPolynomial, eval_finsetSum]

noncomputable def momentProduct {m : ℕ} (v : Fin m → Fin m → ℂ)
    (z : Fin (m * m + 1)) : ℂ :=
  ∏ i, ∑ j, v i j * (z.val : ℂ) ^ j.val

theorem momentProduct_ne_zero_some {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) : ∃ z, momentProduct v z ≠ 0 := by
  classical
  let P : Polynomial ℂ := ∏ i, finiteMomentPolynomial (v i)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => finiteMomentPolynomial_ne_zero (hv i))
  have hdeg : P.natDegree ≤ m * m := by
    calc
      _ ≤ ∑ i : Fin m, (finiteMomentPolynomial (v i)).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin m, m := Finset.sum_le_sum (fun i _ => finiteMomentPolynomial_natDegree_le (v i))
      _ = _ := by simp
  by_contra h
  push Not at h
  apply hP
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun z : Fin (m * m + 1) => (z.val : ℂ))
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro z
    simpa only [P, eval_prod, finiteMomentPolynomial_eval, momentProduct] using h z
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdeg

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedVerticalPower
namespace OAI

section

namespace Erdos3

theorem exists_vertical_pair_precision :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∃ q r rho eta : ℝ,
      p ≤ q ∧ p ≤ r ∧ q ≤ (p + C) ^ C ∧ r ≤ (p + C) ^ C ∧
      verticalDecompositionBudget q ≤ (p + C) ^ C ∧
      verticalDecompositionBudget r ≤ (p + C) ^ C ∧
      0 < rho ∧ 0 < eta ∧ rho⁻¹ ≤ Real.exp q ∧ eta⁻¹ ≤ Real.exp r ∧
      rho + Real.exp (verticalDecompositionBudget q) * eta ≤ Real.exp (-p) / 2 ∧
      Real.exp (-((p + C) ^ C)) ≤ (Real.exp (-p) / 2) /
        (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) := by
  obtain ⟨c, _, hV⟩ := exists_verticalDecompositionBudget_bound
  let Q : Polynomial ℕ := Polynomial.X + 4
  let R : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c
  let P : Polynomial ℕ := R + (R + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  let q := p + 4
  let r := q + (q + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hf : 0 ≤ (q + c) ^ c := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hg : 0 ≤ (r + c) ^ c := by positivity
  have hb : r + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, R, Q, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hVq := hV q hq
  have hVr := hV r hr
  have hVqC : verticalDecompositionBudget q ≤ (p + C) ^ C := by
    have hfR : (q + c) ^ c ≤ r := by dsimp [r]; linarith
    exact hVq.trans (hfR.trans hrC)
  have hVrC : verticalDecompositionBudget r ≤ (p + C) ^ C := by linarith
  have hscaled : Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤ Real.exp (-q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  have he4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsplit : Real.exp (-q) * Real.exp 4 = Real.exp (-p) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hfour : Real.exp (-q) * 4 ≤ Real.exp (-p) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left he4 (Real.exp_nonneg _)
  have hsmall : Real.exp (-q) + Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤
      Real.exp (-p) / 2 := by linarith
  refine ⟨q, r, Real.exp (-q), Real.exp (-r), hpq, hpq.trans hqr, hqr.trans hrC, hrC,
    hVqC, hVrC, Real.exp_pos _, Real.exp_pos _, ?_, ?_, hsmall, ?_⟩
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · apply (le_div_iff₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
    have hloss : q + verticalDecompositionBudget q + verticalDecompositionBudget r ≤ (p + C) ^ C := by
      have hstep : q + verticalDecompositionBudget q ≤ r := by dsimp [r]; linarith
      linarith
    calc
      _ ≤ Real.exp (-(q + verticalDecompositionBudget q + verticalDecompositionBudget r)) *
          (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-q) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) / 2 := by linarith [Real.exp_pos (-q)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {S R T U : Type*} [Fintype S] [Fintype R] [Fintype T]

noncomputable def maskedSiteFactor (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  if label s u = r s then f k s u else 0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def idealSiteLogBudget (m q : ℕ) (P : ℝ) : ℝ :=
  q+(m : ℝ)*P+affineProfileLogBound m P+P+1

theorem idealSiteLogBudget_bounds (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ idealSiteLogBudget m q P ∧ P ≤ idealSiteLogBudget m q P ∧
    (m : ℝ)*P ≤ idealSiteLogBudget m q P ∧
    affineProfileLogBound m P+q ≤ idealSiteLogBudget m q P := by
  have hf := affineProfileLogBound_nonneg m hP
  have hm : 0 ≤ (m : ℝ)*P := by positivity
  unfold idealSiteLogBudget
  constructor
  · positivity
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) q]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) q]

section Ideal

variable {D G α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
  (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
  (sets : ∀ d, O d → Finset α)

end Ideal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPeriodPivot
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerPeriod_exists_pivot {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J]
    (A : Matrix O J ℤ) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A.mulVecLin.range) :
    ∃ s : O ↪ J, (A.submatrix id s).det ≠ 0 := by
  classical
  have hcol (i : O) : ∃ v : J → ℤ, A *ᵥ v = a • Pi.single i 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single i 1, rfl⟩)
  choose v hv using hcol
  let B : Matrix J O ℤ := fun j i => v i j
  have hAB : A * B = a • (1 : Matrix O O ℤ) := by
    ext i k
    change (A *ᵥ v k) i = (a • (1 : Matrix O O ℤ)) i k
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply,
      Pi.single_apply, eq_comm] using congrFun (hv k) i
  have hdet : (A * B).det ≠ 0 := by
    rw [hAB, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ ha
  rw [rectangular_det_expansion] at hdet
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hminor : (A.submatrix id s).det ≠ 0 := left_ne_zero_of_mul hs
  refine ⟨⟨s, ?_⟩, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, hij])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelDensityProjection
namespace OAI

namespace Erdos3

theorem linearIndependent_of_fixed_kernel_period {O K₀ K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K₀]
    (A₀ : Matrix O K₀ ℤ) (A : Matrix O K ℤ) (e : K₀ → K)
    (he : ∀ i k, A i (e k) = A₀ i k) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A₀.mulVecLin.range) :
    LinearIndependent ℝ (fun i k => (A i k : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := integerPeriod_exists_pivot A₀ ha hperiod
  have hdet : ((A₀.submatrix id s).map (fun z => (z : ℝ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hs
  let restrict : (K → ℝ) →ₗ[ℝ] (O → ℝ) :=
    { toFun := fun v j => v (e (s j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  change LinearIndependent ℝ (fun i j => (A₀ i (s j) : ℝ)) at hrows
  apply LinearIndependent.of_comp restrict
  simpa only [Function.comp_def, restrict, LinearMap.coe_mk, AddHom.coe_mk,
    he] using hrows

end Erdos3

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CountingDeficitDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingKernelAverage {X : Type*} [Fintype X]
    (b : ℝ) (w f g : X → ℝ) : ℝ := 𝔼 x, w x * countingKernel b (f x) (g x)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedRelativeBudget
namespace OAI

section

namespace Erdos3

def reducedRelativeParameter (s : ℕ) (p : ℝ) : ℝ :=
  2 * p + 2 * (p + (s + 2)) ^ (s + 2) + 4

theorem reducedRelativeParameter_controls (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedRelativeParameter s p ∧ p ≤ reducedRelativeParameter s p ∧
      2 * p ≤ reducedRelativeParameter s p ∧
      p + 2 * (p + (s + 2)) ^ (s + 2) + 2 ≤ reducedRelativeParameter s p + 2 := by
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  unfold reducedRelativeParameter
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem exists_reducedRelative_budget (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a ≤
        (p + C) ^ C ∧
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
  let D : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let Q : Polynomial ℕ := 2 * Polynomial.X + 2 * D + 4
  let P : Polynomial ℕ := 4 * D + 2 + (Q + Polynomial.C a) ^ a + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hq := (reducedRelativeParameter_controls s hp).1
  have ha : 0 ≤ (reducedRelativeParameter s p + a) ^ a := by positivity
  have hb : 0 ≤ (reducedRelativeParameter s p + b) ^ b := by positivity
  have hsum : 4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a +
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, D, reducedRelativeParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SynchronizedCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exp_repeated_add_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.exp p + Real.exp p + Real.exp q ≤ Real.exp (p + q + 2) := by
  have hpq : Real.exp p ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_right hq)
  have hqp : Real.exp q ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp (p + q) + Real.exp (p + q) + Real.exp (p + q) := add_le_add (add_le_add hpq hpq) hqp
    _ = 3 * Real.exp (p + q) := by ring
    _ ≤ Real.exp 2 * Real.exp (p + q) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_synchronizedCorrection_budget (a d r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a + p + (p + d) ^ d + 2 ≤ (p + C) ^ C ∧
      (p + r) ^ r ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X +
    (Polynomial.X + Polynomial.C d) ^ d + 2 + (Polynomial.X + Polynomial.C r) ^ r
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hd : 0 ≤ (p + d) ^ d := by positivity
  have hr : 0 ≤ (p + r) ^ r := by positivity
  have hsum : (p + a) ^ a + p + (p + d) ^ d + 2 + (p + r) ^ r ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonInitialBudget
namespace OAI

section

namespace Erdos3

def commonExtractionParameter (p : ℝ) : ℝ := 3 * p + 3

def commonInitialParameter (p : ℝ) : ℝ := (commonExtractionParameter p + 2) ^ 3

theorem commonExtractionParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonExtractionParameter p ∧ 2 * p ≤ commonExtractionParameter p ∧
      1 ≤ commonExtractionParameter p ∧ commonExtractionParameter p ≤ commonInitialParameter p := by
  have hq : 1 ≤ commonExtractionParameter p + 2 := by
    unfold commonExtractionParameter
    linarith
  have hpow := pow_le_pow_right₀ hq (show 1 ≤ (3 : ℕ) by decide)
  simp only [pow_one] at hpow
  unfold commonInitialParameter
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · linarith

theorem commonExtractionParameter_products {p C M : ℝ} (hp : 0 ≤ p)
    (_hC : 0 ≤ C) (hCp : C ≤ Real.exp p) (hM : 0 ≤ M) (hMp : M ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    max 2 (C * (M + M)) ≤ Real.exp (commonExtractionParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (commonExtractionParameter p) := by
  have hq := commonExtractionParameter_controls hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  constructor
  · apply max_le (htwo.trans (Real.exp_le_exp.mpr hq.2.2.1))
    calc
      _ ≤ Real.exp p * (Real.exp p + Real.exp p) :=
        mul_le_mul hCp (add_le_add hMp hMp) (add_nonneg hM hM) (Real.exp_nonneg _)
      _ = 2 * (Real.exp p * Real.exp p) := by ring
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (1 + (p + p)) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold commonExtractionParameter; linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hδ hl (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq.2.1

theorem exists_commonInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonInitialParameter p + 1 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + 2) ^ 3 ≤ (p + D) ^ D ∧
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (3 * Polynomial.X + 3 + 2) ^ 3
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 2) ^ 3 + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonInitialParameter p :=
    (hp.trans (commonExtractionParameter_controls hp).1).trans
      (commonExtractionParameter_controls hp).2.2.2
  have h2 : 0 ≤ (commonInitialParameter p + 2) ^ 3 := by positivity
  have hC : 0 ≤ (commonInitialParameter p + C) ^ C := by positivity
  have hsum : commonInitialParameter p + 1 + (commonInitialParameter p + 2) ^ 3 +
      (commonInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonInitialParameter, commonExtractionParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonTerminalBudget
namespace OAI

section

namespace Erdos3

def fullInitialParameter (s C : ℕ) (p : ℝ) : ℝ :=
  p + p * (s + 2) * (p + 1) ^ (s + 1) + (p + C) ^ C + 2

theorem fullInitialParameter_controls (s C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fullInitialParameter s C p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ fullInitialParameter s C p ∧
      (p + C) ^ C ≤ fullInitialParameter s C p := by
  have hdim : 0 ≤ p * (s + 2) * (p + 1) ^ (s + 1) := by positivity
  have hC : 0 ≤ (p + C) ^ C := by positivity
  unfold fullInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem exists_fullInitialParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

def commonTerminalParameter (s c : ℕ) (p : ℝ) : ℝ := fullInitialParameter s c p + (s + 1)

theorem commonTerminalParameter_controls (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonTerminalParameter s c p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ commonTerminalParameter s c p ∧
      (p + c) ^ c ≤ commonTerminalParameter s c p ∧
      (s + 1 : ℕ) ≤ commonTerminalParameter s c p := by
  have h := fullInitialParameter_controls s c hp
  have hle : fullInitialParameter s c p ≤ commonTerminalParameter s c p :=
    le_add_of_nonneg_right (by positivity)
  refine ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.trans hle, ?_⟩
  have hnonneg : 0 ≤ fullInitialParameter s c p := hp.trans h.1
  simpa only [commonTerminalParameter, Nat.cast_add, Nat.cast_one] using
    (le_add_of_nonneg_left hnonneg : ((s : ℝ) + 1) ≤ fullInitialParameter s c p + ((s : ℝ) + 1))

theorem exists_commonTerminalParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonTerminalParameter s c p ≤ (p + D) ^ D ∧
      (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2 + Polynomial.C (s + 1)
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonTerminalParameter s c p := hp.trans (commonTerminalParameter_controls s c hp).1
  have hpow : 0 ≤ (commonTerminalParameter s c p + C) ^ C := by positivity
  have hsum : commonTerminalParameter s c p + (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonTerminalParameter, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TerminalCompositionBudget
namespace OAI

section

namespace Erdos3

theorem exists_terminalComposition_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p ≤ (p + C) ^ C ∧ (2 * p + a) ^ a ≤ (p + C) ^ C ∧ (2 * p + b) ^ b ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := Polynomial.X +
    (2 * Polynomial.X + Polynomial.C a) ^ a + (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (2 * p + a) ^ a := by positivity
  have hb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hsum : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastTerminalBudget
namespace OAI

section

namespace Erdos3

def doublePowerParameter (a b : ℕ) (p : ℝ) : ℝ := p + (3 * p + 2) ^ a + (p + 2) ^ b + 2

theorem doublePowerParameter_controls (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ doublePowerParameter a b p ∧ (3 * p + 2) ^ a ≤ doublePowerParameter a b p ∧
      (p + 2) ^ b ≤ doublePowerParameter a b p := by
  have h₁ : 0 ≤ (3 * p + 2) ^ a := by positivity
  have h₂ : 0 ≤ (p + 2) ^ b := by positivity
  have hlast : p + (3 * p + 2) ^ a + (p + 2) ^ b ≤ doublePowerParameter a b p :=
    le_add_of_nonneg_right (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right h₁).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact (le_add_of_nonneg_left (add_nonneg hp h₁)).trans hlast

theorem exists_doublePowerParameter_budget (a b C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (doublePowerParameter a b p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + (3 * Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ b + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, doublePowerParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

def fastTerminalParameter (p : ℝ) : ℝ := doublePowerParameter 294 7 p

theorem fastTerminalParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastTerminalParameter p ∧ (3 * p + 2) ^ 294 ≤ fastTerminalParameter p ∧
      (p + 2) ^ 7 ≤ fastTerminalParameter p :=
  doublePowerParameter_controls 294 7 hp

theorem exists_fastTerminalParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fastTerminalParameter p + C) ^ C ≤ (p + D) ^ D :=
  exists_doublePowerParameter_budget 294 7 C

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastRemovalBudget
namespace OAI

section

namespace Erdos3

theorem exists_fast_removal_factor_budget (s a cA cD : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p → ∀ (K : ℝ), 0 ≤ K → K ≤ Real.exp p →
      K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) ∧
      K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
        Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + (Polynomial.X + Polynomial.C cA) ^ cA +
    (Polynomial.X + Polynomial.C cD) ^ cD + Polynomial.C (s + 1) + (Polynomial.X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp K hK hKp
  have hpoly : 2 * p + (p + cA) ^ cA + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤
      (p + C) ^ C := by simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hAexp : 2 * p + (p + cA) ^ cA ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cD) ^ cD := by positivity
    have h2 : 0 ≤ (p + 2) ^ a := by positivity
    have h3 : (0 : ℝ) ≤ (s + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hDexp : p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a ≤ (p + C) ^ C := by
    have h1 : 0 ≤ (p + cA) ^ cA := by positivity
    linarith
  have hAfactor : K * Real.exp ((p + cA) ^ cA) * K ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + cA) ^ cA) * Real.exp p := by gcongr
      _ = Real.exp (2 * p + (p + cA) ^ cA) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hAexp
  have hstep : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (s + 1 : ℝ))
  have hDfactor : K * (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) ≤
      Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp p * (Real.exp ((p + cD) ^ cD) * (Real.exp (s + 1) * Real.exp ((p + 2) ^ a))) := by
        gcongr
      _ = Real.exp (p + (p + cD) ^ cD + (s + 1 : ℕ) + (p + 2) ^ a) := by
        simp only [← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hDexp
  exact ⟨hAfactor, hDfactor⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialRemovalBudget
namespace OAI

section

namespace Erdos3

theorem exists_initial_removal_budget (cS cR : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let A := (p + cS) ^ cS
      let B := (p + cR) ^ cR
      let r := p + 1 + 2 * A
      Real.exp A * Real.exp p ≤ Real.exp r ∧
      Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r ∧
      Real.exp p * Real.exp r ≤ Real.exp ((p + C) ^ C) ∧
      Real.exp p * Real.exp B ≤ Real.exp ((p + C) ^ C) := by
  let P : Polynomial ℕ := 2 * Polynomial.X + 1 +
    2 * (Polynomial.X + Polynomial.C cS) ^ cS +
    (Polynomial.X + Polynomial.C cR) ^ cR
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp A B r
  have hA : 0 ≤ A := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hB : 0 ≤ B := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hpoly : 2 * p + 1 + 2 * A + B ≤ (p + C) ^ C := by
    simpa [P, A, B, Polynomial.eval₂_pow] using hbudget p hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hsmall : Real.exp A * (Real.exp p + Real.exp A) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp A * (Real.exp (p + A) + Real.exp (p + A)) := by
        gcongr <;> linarith
      _ = 2 * Real.exp (p + 2 * A) := by
        rw [← two_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp 1 * Real.exp (p + 2 * A) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp r := by rw [← Real.exp_add]; congr 1; dsimp [r]; ring
  refine ⟨?_, hsmall, ?_, ?_⟩
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeDependentSelectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_native_dependent_selection_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P₀ := (p + a) ^ a
      let P := (P₀ + 2) ^ 3 + 2 * P₀
      P₀ ≤ (p + C) ^ C ∧ 2 * P ≤ (p + C) ^ C ∧ (P + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + Polynomial.C a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P₀ + 2 * P + (P + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp P₀' P'
  have hP₀ : 0 ≤ P₀' := by dsimp only [P₀']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hpow : 0 ≤ (P' + c) ^ c := by positivity
  have hsum : P₀' + 2 * P' + (P' + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, P₀, P, P₀', P', Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hP, hpow, hsum],
    by linarith only [hP₀, hpow, hsum], by linarith only [hP₀, hP, hsum]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def matchedCellSpace (L S : Finset G) : Finset (G × (G × G)) := L ×ˢ (S ×ˢ S)

noncomputable def matchedFirstCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f z.1

noncomputable def matchedSecondCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f (-z.1 + z.2.1 + z.2.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedPairAverage (L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 r ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, F r (-r + s + t)

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIndependentAverage (L S C : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 u ∈ C, 𝔼 v ∈ C, matchedPairAverage L S (fun x y => F (x + u) (y + v))

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIntegral (L S : Finset G) (a f g : G → ℝ) : ℝ :=
  matchedPairAverage L S (fun x y => f x * g y * a (x + y))

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def parentMatchedAverage (A B L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedPairAverage L S (fun r q => F (x + r) (y + q))

variable [DecidableEq G]

noncomputable def parentTruncatedIntegral (A B L S : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedIntegral L S (fun z => a (x + y + z))
    (Peeling.slice L (fun r => f (x + r))) (Peeling.slice L (fun q => g (y + q)))

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def centerSlice (L : Finset G) (f : G → ℝ) (x : G) : G → ℝ :=
  Peeling.slice L (fun r => f (x + r))

noncomputable def centerPotential (L : Finset G) (f g : G → ℝ) (z : G × G) : ℝ :=
  (cellAverage L f z.1 * cellAverage L g z.2) ^ (1 / 4 : ℝ)

noncomputable def centerMatchedIntegral (L S : Finset G) (a f g : G → ℝ) (z : G × G) : ℝ :=
  matchedIntegral L S (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildIntegral (L S : Finset G) (a f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    bilinearIntegral (C.image (fun r => t.1 + r))
      (C.image (fun r => (-t.1 + t.2.1 + t.2.2) + r))
      (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildPotential (L S : Finset G) (f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    (matchedFirstCell C (centerSlice L f z.1) t *
      matchedSecondCell C (centerSlice L g z.2) t) ^ (1 / 4 : ℝ)

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

def CellBilinearBound (C : Finset G) (a : G → ℝ) (T : ℝ) : Prop :=
  ∀ origin : G, ∀ f g : G → ℝ,
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
    (∀ x, x ∉ C → f x = 0) → (∀ x, x ∉ C → g x = 0) →
    bilinearIntegral C C (fun x => a (origin + x)) f g ≤
      T * ((𝔼 x ∈ C, f x) * (𝔼 x ∈ C, g x)) ^ (1 / 4 : ℝ)

variable [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefinementPolynomialBound
namespace OAI

section

namespace Erdos3.CellRefinement

open Polynomial

noncomputable def refinementRankPolynomial (C : ℕ) : Polynomial ℕ :=
  Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 + 1

noncomputable def refinementDepthPolynomial (C : ℕ) : Polynomial ℕ := Polynomial.C C * X + 1

noncomputable def refinementFinalRankPolynomial (C : ℕ) : Polynomial ℕ :=
  1 + refinementDepthPolynomial C * refinementRankPolynomial C

noncomputable def refinementMatchPolynomial (C : ℕ) : Polynomial ℕ :=
  5 * refinementFinalRankPolynomial C + 13 * X + 2 * Polynomial.C C + 8020

noncomputable def refinementUnbalancedPolynomial (C : ℕ) : Polynomial ℕ :=
  2 * refinementFinalRankPolynomial C +
    Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 +
    2 * Polynomial.C C * X ^ 2 + 2 * X + 2 * Polynomial.C C + 3209 +
    Polynomial.C C * (3 + (3 * Polynomial.C C + 1) * X ^ 2 + refinementFinalRankPolynomial C)

noncomputable def refinementRoundPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementMatchPolynomial C + refinementFinalRankPolynomial C + 3 * X + 1602 +
    refinementUnbalancedPolynomial C

noncomputable def refinementWidthPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementDepthPolynomial C * refinementRoundPolynomial C

noncomputable def refinementCostPolynomial (C : ℕ) : Polynomial ℕ :=
  (2 * refinementFinalRankPolynomial C + 4 * X + refinementWidthPolynomial C +
    refinementMatchPolynomial C + 1612) +
  (3 * X + 2 + refinementFinalRankPolynomial C *
    (refinementWidthPolynomial C + refinementMatchPolynomial C + 10))

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def pivotCellForm {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (z : Fin l → Fin q → R) (x d : R) (beta : Fin l → Fin q) : R :=
  x + slope * d + ∑ a, (slope - v a) * z a (beta a)

noncomputable def pivotGridFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (pivotCellForm v slope z x d beta)

noncomputable def pivotRootFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (w : R) : ℝ :=
  ∏ beta : Fin l → Fin q, f (w + ∑ a, (slope - v a) * z a (beta a))

noncomputable def pivotKernelFactor {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  ∏ beta : Fin l → Fin q, countingKernel parameter
    (f (pivotCellForm v a z x d beta)) (g (pivotCellForm v b z x d beta))

noncomputable def pivotStageIntegrand {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R) : ℝ :=
  (∏ i ∈ S, pivotGridFactor v (slopes i) (mu i) z x d) *
    pivotKernelFactor v a b parameter f g z x d

noncomputable def pivotStageCount {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) : ℝ :=
  𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, pivotStageIntegrand v S slopes mu a b parameter f g z x d

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

def PivotCompatible {I R : Type*} [CommRing R] {l : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (a b : R) : Prop :=
  IsUnit (b - a) ∧
    (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) ∧
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) ∧
    (∀ j, IsUnit (a - v j) ∧ IsUnit (b - v j) ∧
      ∀ i ∈ S, IsUnit (slopes i - v j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem mem_rectangular_zero_radius_iff {I : Type*} [Fintype I]
    (H : I → ℝ) (R : ℝ) (v : I → ℤ) :
    v ∈ rectangularWeightIndices 0 H R ↔ ∀ i, |(v i : ℝ)| ≤ H i * R := by
  classical
  constructor
  · intro hv i
    have h := sampledWeightIndices_mem_bound (Fintype.mem_piFinset.mp hv i)
    simpa only [Pi.zero_apply, sub_zero] using h
  · intro hv
    apply Fintype.mem_piFinset.mpr
    intro i
    change v i ∈ sampledWeightIndices 0 (H i) R
    simp only [sampledWeightIndices, zero_sub, zero_add, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr (abs_le.mp (hv i)).1, Int.le_floor.mpr (abs_le.mp (hv i)).2⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

noncomputable def spatialWindow {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) : Finset (X → (Unit ⊕ α) → ℤ) := by
  classical
  exact (Fintype.piFinset (fun d => rectangularWeightIndices 0 (fun _ : Unit ⊕ α => H d) b)).image
    (fun w d => spatialUnstar (w d))

theorem mem_spatialWindow_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)| ≤ H d * b := by
  classical
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    intro d i
    have h := (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b (w d)).mp
      (Fintype.mem_piFinset.mp hw d) i
    simpa only [spatialStar_unstar] using h
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨fun d => spatialStar (v d), ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro d
      exact (mem_rectangular_zero_radius_iff (fun _ : Unit ⊕ α => H d) b _).mpr (hv d)
    · funext d
      exact spatialUnstar_star (v d)

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {I : A → Type*} [∀ a, Fintype (I a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {T K L S U : Type*} [Fintype T] [Fintype K] [Fintype L] [Fintype S]
variable (c : T → ℂ) (a : K → L → ℂ)
variable (g : T → S → U → ℂ) (f : K → L → S → U → ℂ) (v : S → U)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (offset : B → ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

noncomputable def selectedBooleanSiteRows (axis : A) (rows : Finset (Finset α))
    (x : Finset α → A → ℝ) : rows → ℝ :=
  fun t => booleanCoefficient (fun s => x s axis) t

noncomputable def rationalBooleanSitePhase (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (s : Finset α) (v : ZMod D) : ℂ :=
  rationalGridPhase D a (fun t => booleanCoefficient (Pi.single s v) t)

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α T : Type*} [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev PlateauSiteIndex (α A : Type*) (n : A → ℕ) :=
  Σ a, (Finset α × Unit → Fin (n a))

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A]

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def scalarSupportPlateau (H x : ℝ) : ℂ :=
  normalizedSupportPlateau H (fun _ : Unit => x)

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

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AmbientL1SamplingBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def ambientL1FourierInput {A : Type*} [Semiring A] (T : A) : A := 2 * T + 1
noncomputable def ambientL1SamplingBudget {A : Type*} [Semiring A] (T : A) : A :=
  let Q := ambientL1FourierInput T
  T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q

theorem ambientL1SamplingBudget_bounds {T : ℝ} (hT : 0 ≤ T)
    {Lf Lg Cf Cg Ljet : ℝ≥0} {η : ℝ}
    (hf : (Lf : ℝ) ≤ Real.exp T) (hg : (Lg : ℝ) ≤ Real.exp T)
    (hcf : (Cf : ℝ) ≤ Real.exp T) (hcg : (Cg : ℝ) ≤ Real.exp T)
    (hjet : (Ljet : ℝ) ≤ Real.exp T) (hη : η⁻¹ ≤ Real.exp T) :
    let Q := ambientL1FourierInput T
    let P := ambientL1SamplingBudget T
    0 ≤ Q ∧ T ≤ Q ∧ T ≤ P ∧
      (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q ∧ η⁻¹ ≤ Real.exp Q ∧
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P ∧
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P := by
  intro Q P
  have hTQ : T ≤ Q := by dsimp [Q, ambientL1FourierInput]; linarith
  have hQ : 0 ≤ Q := hT.trans hTQ
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum {a b : ℝ≥0} (ha : (a : ℝ) ≤ Real.exp T) (hb : (b : ℝ) ≤ Real.exp T) :
      ((a + b : ℝ≥0) : ℝ) ≤ Real.exp (T + 1) := by
    rw [NNReal.coe_add, Real.exp_add]
    calc
      _ ≤ 2 * Real.exp T := by linarith
      _ ≤ _ := by nlinarith [Real.exp_pos T]
  have hl : (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q := by
    rw [NNReal.coe_mul]
    apply (mul_le_mul (hsum hf hg) hjet (NNReal.coe_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp [Q, ambientL1FourierInput]
    ring
  have hc : ((Cf + Cg : ℝ≥0) : ℝ) ≤ Real.exp Q :=
    (hsum hcf hcg).trans (Real.exp_le_exp.mpr (by dsimp [Q, ambientL1FourierInput]; linarith))
  have hpow : 0 ≤ (2 * Q + 2) ^ 4 := by positivity
  have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
  have hTP : T ≤ P := by
    change T ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hfreq : (2 * Q + 2) ^ 4 ≤ P := by
    change (2 * Q + 2) ^ 4 ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hcoeff : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ P := by
    change _ ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  refine ⟨hQ, hTQ, hTP, hl, hη.trans (Real.exp_le_exp.mpr hTQ), Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp Q :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

theorem exists_ambientL1SamplingThreshold_bound (K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ T : ℝ, 0 ≤ T →
      (ambientL1SamplingBudget T + K) ^ K ≤ (T + A) ^ A := by
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget
    ((ambientL1SamplingBudget Polynomial.X + Polynomial.C K) ^ K)
  refine ⟨A, hA, ?_⟩
  intro T hT
  simpa [ambientL1SamplingBudget, ambientL1FourierInput, Polynomial.eval₂_pow] using hb T hT

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedFiniteIdealProfileLog {A : Type*} [Semiring A] (D p : A) : A :=
  3 * D + (2 * D + 2) * p + 1

def allocatedFiniteIdealCoefficientLog {A : Type*} [Semiring A]
    (m : ℕ) (D p : A) : A :=
  (2 ^ (m + 1) : ℕ) * D * (4 * allocatedFiniteIdealProfileLog D p + 8) +
    allocatedFiniteIdealProfileLog D p

def allocatedFiniteIdealLipschitzLog {A : Type*} [Semiring A] (D p c : A) : A :=
  D + 6 * allocatedFiniteIdealProfileLog D p + c + 14

theorem idealSiteLogBudget_le_finite_profile {outputs dim : ℕ} {D p : ℝ}
    (hp : 0 ≤ p) (hout : (outputs : ℝ) ≤ D) (hdim : (dim : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealProfileLog D p := by
  have hm := mul_le_mul_of_nonneg_right hout hp
  dsimp only [idealSiteLogBudget, affineProfileLogBound, allocatedFiniteIdealProfileLog]
  nlinarith only [hout, hdim, hprofile, hm]

theorem allocatedFiniteIdeal_budget_nonneg (m : ℕ) {D p c : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedFiniteIdealProfileLog D p ∧
      0 ≤ allocatedFiniteIdealCoefficientLog m D p ∧
      0 ≤ allocatedFiniteIdealLipschitzLog D p c := by
  dsimp only [allocatedFiniteIdealProfileLog, allocatedFiniteIdealCoefficientLog,
    allocatedFiniteIdealLipschitzLog]
  refine ⟨?_, ?_, ?_⟩ <;> positivity

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hR : ∀ j, 0 < R j)
variable {δ : ℝ≥0}
  {ε p M D : ℝ}

local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hR : ∀ j, 0 < R j)
variable {δ : ℝ≥0}
  {ε p M D w eP : ℝ}

local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedMarkedCoveredLowerDiagramBudget
namespace OAI

section

namespace Erdos3

theorem exists_allocatedMarkedCoveredLowerDiagramBudget (A B T : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 1 ≤ p →
      let nativeCost := (p + A) ^ A
      let inputCost := p + nativeCost
      let recoveryCost := (inputCost + B) ^ B
      let lowerInput := inputCost + recoveryCost
      let finalLower := (lowerInput + T) ^ T
      1 ≤ inputCost ∧ p ≤ inputCost ∧ nativeCost ≤ inputCost ∧
        inputCost ≤ lowerInput ∧ recoveryCost ≤ lowerInput ∧
        lowerInput ≤ (p + C) ^ C ∧ finalLower ≤ (p + C) ^ C := by
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let I : Polynomial ℕ := Polynomial.X + N
  let R : Polynomial ℕ := (I + Polynomial.C B) ^ B
  let U : Polynomial ℕ := I + R
  let F : Polynomial ℕ := (U + Polynomial.C T) ^ T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + F)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let nativeCost := (p + A) ^ A
  let inputCost := p + nativeCost
  let recoveryCost := (inputCost + B) ^ B
  let lowerInput := inputCost + recoveryCost
  let finalLower := (lowerInput + T) ^ T
  have hnative : 0 ≤ nativeCost := by dsimp [nativeCost]; positivity
  have hinput : 0 ≤ inputCost := add_nonneg hp0 hnative
  have hrecovery : 0 ≤ recoveryCost := by dsimp [recoveryCost]; positivity
  have hlower : 0 ≤ lowerInput := add_nonneg hinput hrecovery
  have hfinal : 0 ≤ finalLower := by dsimp [finalLower]; positivity
  have hsum : lowerInput + finalLower ≤ (p + C) ^ C := by
    simpa only [N, I, R, U, F, nativeCost, inputCost, recoveryCost, lowerInput, finalLower,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Nat.coe_castRingHom] using hbudget p hp0
  exact ⟨hp.trans (le_add_of_nonneg_right hnative), le_add_of_nonneg_right hnative,
    le_add_of_nonneg_left hp0, le_add_of_nonneg_right hrecovery,
    le_add_of_nonneg_left hinput, (le_add_of_nonneg_right hfinal).trans hsum,
    (le_add_of_nonneg_left hlower).trans hsum⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastSymbolCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exists_fastSymbolCorrectionBudget (a ce cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 0 ≤ p →
      let p₀ : ℝ := p + (p + 2) ^ a + (p + 2) ^ 4 + 2
      let p₁ : ℝ := p₀ + (p₀ + ce) ^ ce + (p₀ + cr) ^ cr
      let p₂ : ℝ := p₁ + ((p₁ + 2) ^ 10 + 2) ^ 36 + ((p₁ + 2) ^ 10 + 2) ^ 18 + 2
      (p₂ + ce) ^ ce + (p₂ + cr) ^ cr ≤ (p + C) ^ C := by
  let B₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ 4 + 2
  let B₁ : Polynomial ℕ := B₀ + (B₀ + Polynomial.C ce) ^ ce + (B₀ + Polynomial.C cr) ^ cr
  let B₂ : Polynomial ℕ := B₁ + ((B₁ + 2) ^ 10 + 2) ^ 36 + ((B₁ + 2) ^ 10 + 2) ^ 18 + 2
  let B : Polynomial ℕ := (B₂ + Polynomial.C ce) ^ ce + (B₂ + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, B₂, B₁, B₀, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistExtractionBudget
namespace OAI

section

namespace Erdos3

theorem exists_normalizedTwistExtractionBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + 3 * p + 16
      q + (q + b) ^ b + 3 * p + 16 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + 3 * X + 16
  let P := Q + (Q + Polynomial.C b) ^ b + 3 * X + 16
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajor_detected_potential_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a
      (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C ∧ q ≤ (p + C)^C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a)^a
  let R : Polynomial ℕ := (Q + (Q + 2)^4 + 1 + Polynomial.C c)^c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, fun p hp => ?_⟩
  let q : ℝ := (p + a)^a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hR : 0 ≤ (q + (q + 2)^4 + 1 + c)^c := by positivity
  have hsum : q + (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C := by
    simpa [Q, R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_left hq).trans hsum, (le_add_of_nonneg_right hR).trans hsum⟩

theorem translationMajor_initial_budget_bounds (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ (p + a)^a ∧ p ≤ (p + a)^a ∧ 1 ≤ (p + a)^a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (1 : ℝ) ≤ p + a := by linarith
  have hpow : p + a ≤ (p + a)^a := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ a by omega)
  exact ⟨(zero_le_one.trans hbase).trans hpow,
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow, hbase.trans hpow⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorSeparatedBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajorSeparated_budget (a c s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let p1 := (p + a) ^ a
      p1 ≤ (p + C) ^ C ∧
        (p1 + c) ^ c ≤ (p + C) ^ C ∧
        (p1 + s) ^ s ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := (P + Polynomial.C c) ^ c
  let R : Polynomial ℕ := (P + Polynomial.C s) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : (p + a) ^ a + ((p + a) ^ a + c) ^ c +
      ((p + a) ^ a + s) ^ s ≤ (p + C) ^ C := by
    simpa only [P, Q, R, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom]
      using hbudget p hp
  have hP : 0 ≤ (p + a) ^ a := by positivity
  have hQ : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
  have hR : 0 ≤ ((p + a) ^ a + s) ^ s := by positivity
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchSourceTestFinBounds
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativePatchSourceTest {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (y : X → ℝ) : ℝ :=
  (relativeBoxInput N f (fun i => ⌊y i⌋) - a) * A.value y

@[simp] theorem relativePatchSourceTest_integer {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (x : X → ℤ) :
    relativePatchSourceTest N f a A (fun i => (x i : ℝ)) =
      (relativeBoxInput N f x - a) * A.value (fun i => (x i : ℝ)) := by
  simp only [relativePatchSourceTest, Int.floor_intCast]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] integerBox

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastInactiveCharacterSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J K H : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

noncomputable def forecastInactiveCharacterCoefficient
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (r : K → H → ZMod (orderOf χ)) : ℂ :=
  finiteImageCharacteristic p
    (fun t j => (integerLongPolynomialOutput poly
      (fun k => ((r k.1 k.2).val : ℤ)) N t j : ZMod N)) χ

section Principal

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}
  {L : PrincipalTupleIndex B h → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Principal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J D α : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]
  [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "Output" => (Σ _a : Active, Unit)

local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {V Out : Type*} [Fintype V] [DecidableEq V] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPolynomialTorusPeriod
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem integerPolynomial_eval_zmod_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((eval x P : ℤ) : ZMod q) = ((eval y P : ℤ) : ZMod q) := by
  change (Int.castRingHom (ZMod q)) (eval x P) = (Int.castRingHom (ZMod q)) (eval y P)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  exact congrArg (fun z => eval z (MvPolynomial.map (Int.castRingHom (ZMod q)) P)) (funext hxy)

theorem integerPolynomial_eval_sub_dvd {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    (q : ℤ) ∣ eval x P - eval y P := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  rw [Int.cast_sub, integerPolynomial_eval_zmod_eq P q x y hxy, sub_self]

theorem addCircle_int_div_eq_of_dvd_sub (q : ℕ) (a b : ℤ)
    (h : (q : ℤ) ∣ a - b) :
    (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      (((b : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) := by
  by_cases hq : q = 0
  · simp [hq]
  · let : NeZero q := ⟨hq⟩
    have hab : (a : ZMod q) = (b : ZMod q) := by
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
    simpa only [ZMod.toAddCircle_intCast] using congrArg ZMod.toAddCircle hab

theorem integerPolynomial_eval_addCircle_div_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((((eval x P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      ((((eval y P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) :=
  addCircle_int_div_eq_of_dvd_sub q _ _ (integerPolynomial_eval_sub_dvd P q x y hxy)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeOutside
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def outsideAssignment (K : Finset ι) (base : ∀ i, Value i)
    (x : ∀ i : {i // i ∉ K}, Value i.val) : ∀ i, Value i :=
  fun i => if h : i ∈ K then base i else x ⟨i, h⟩

def liftOutside (K : Finset ι) :
    CoordinateDecisionTree {i // i ∉ K} (fun i => Value i.val) → CoordinateDecisionTree ι Value
  | .leaf => .leaf
  | .split i children => .split i.val (fun v => liftOutside K (children v))

end Erdos3.CoordinateDecisionTree

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeRelabel
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v} {Other : ι → Type w}

def relabelAssignment (e : ∀ i, Value i ≃ Other i) (x : ∀ i, Value i) : ∀ i, Other i :=
  fun i => e i (x i)

def relabel (e : ∀ i, Value i ≃ Other i) :
    CoordinateDecisionTree ι Value → CoordinateDecisionTree ι Other
  | .leaf => .leaf
  | .split i children => .split i (fun v => relabel e (children ((e i).symm v)))

end Erdos3.CoordinateDecisionTree

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationCoordinateBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationCoordinate_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t q : ℕ) (p M B : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp p → 0 ≤ B → B ≤ Real.exp p →
      (q : ℝ) ≤ Real.exp p →
      ((d : ℝ) + 1) * ((t : ℝ) * M * B) *
          (1 + (n : ℝ) * d * ((t : ℝ) * M * B)) ^ d ≤
        Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  let Q : Polynomial ℕ :=
    Polynomial.C (5 * d + 4) * Polynomial.X +
      Polynomial.C (d ^ 2 + 2 * d + 1 + d.factorial)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t q p M B hp hn ht hM hMp hB hBp hq
  have htotal : (5 * (d : ℝ) + 4) * p +
      ((d : ℝ) ^ 2 + 2 * d + 1 + d.factorial) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hbudget p hp
  have hmasscost : (4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1 ≤
      (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ d + 1 by positivity)) hp
    have hf : (0 : ℝ) ≤ d.factorial := Nat.cast_nonneg _
    nlinarith
  have hdenomcost : (d.factorial : ℝ) + ((d : ℝ) + 1) * p ≤ (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ 4 * d + 3 by positivity)) hp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [sq_nonneg (d : ℝ)]
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have ha : (t : ℝ) * M * B ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod : (n : ℝ) * d * ((t : ℝ) * M * B) ≤ Real.exp (4 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp d * Real.exp (3 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hplus : 1 + (n : ℝ) * d * ((t : ℝ) * M * B) ≤
      Real.exp (4 * p + d + 1) := one_add_le_exp_succ (by positivity) hprod
  have hfactor : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  constructor
  · calc
      _ ≤ Real.exp ((d : ℝ) + 1) * Real.exp (3 * p) *
          Real.exp (4 * p + d + 1) ^ d := by gcongr
      _ = Real.exp ((4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hmasscost
  · have hf : (d.factorial : ℝ) ≤ Real.exp d.factorial := by
      linarith [Real.add_one_le_exp (d.factorial : ℝ)]
    push_cast
    calc
      (d.factorial : ℝ) * (q : ℝ) ^ (d + 1) ≤
          Real.exp d.factorial * (Real.exp p) ^ (d + 1) := by gcongr
      _ = Real.exp ((d.factorial : ℝ) + ((d : ℝ) + 1) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr hdenomcost

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedGridLength_bounds (N : ℕ) (H ρ : ℝ)
    (hlarge : 4 ≤ ρ * H) (hwhole : ρ * H ≤ 2 * (N : ℝ)) :
    0 < ⌊ρ * H / 2⌋₊ ∧ ⌊ρ * H / 2⌋₊ ≤ N ∧
      ρ * H / 4 ≤ (⌊ρ * H / 2⌋₊ : ℝ) ∧ (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := by
  have hpos : 0 < ⌊ρ * H / 2⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hN : ⌊ρ * H / 2⌋₊ ≤ N := Nat.floor_le_of_le (by linarith)
  have hup : (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := Nat.floor_le (by linarith)
  have hnext := Nat.lt_floor_add_one (ρ * H / 2)
  exact ⟨hpos, hN, by linarith, hup⟩

noncomputable def normalizedBoxPartitions {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ)) :
    ∀ i, FiniteProgressionPartition (N i) :=
  comparableBoxPartitions N (fun i => ⌊ρ * H i / 2⌋₊)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).2.1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPoint (lo hi : I → ℤ) (z : ∀ i, Finset.Ico (lo i) (hi i)) :
    translatedIntegerBox lo (fun i => (hi i - lo i).toNat) := by
  refine ⟨fun i => (z i : ℤ), (mem_translatedIntegerBox _ _ _).mpr ?_⟩
  intro i
  have h := Finset.mem_Ico.mp (z i).property
  constructor
  · exact h.1
  · omega

noncomputable def integerBoxMesh (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (z : ∀ i, Finset.Ico (lo i) (hi i)) : ∀ i, (P i).Label :=
  physicalBoxCell lo (fun i => (hi i - lo i).toNat) P (integerBoxMeshPoint lo hi z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPointEquiv (lo hi : I → ℤ) :
    (∀ i, Finset.Ico (lo i) (hi i)) ≃ translatedIntegerBox lo (fun i => (hi i - lo i).toNat) where
  toFun := integerBoxMeshPoint lo hi
  invFun x i := ⟨x.val i, by
    have h := (mem_translatedIntegerBox _ _ _).mp x.property i
    exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def integerBoxMeshCellEquiv (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      {x : translatedIntegerBox lo (fun i => (hi i - lo i).toNat) //
        physicalBoxCell lo (fun i => (hi i - lo i).toNat) P x = c} :=
    (integerBoxMeshPointEquiv lo hi).subtypeEquiv (fun _ => Iff.rfl)
  exact e.trans (physicalBoxCellEquiv lo (fun i => (hi i - lo i).toNat) P hstep hpos c)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarInitialPolynomialBudget
namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialReferencePolynomial (d A : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let P := Polynomial.C A * (X + 1)
  let M := Polynomial.C (d + 1) * X
  let D := Polynomial.C d
  let input := M * (P + 3) + X * P + 2 * (X + 1) + P + 1
  let Z := 4 * (6 * input + P + 3 * D + 10) + 2 * P + 10
  let row := (16 + 4 * D) * Z + 16 * D + 48
  let error := Z + row + X * (row + 6 * Z + 12)
  let G := 2 * (30 + 2 * X * Z + 2 * X + error + X * (5 * Z + 11) + 10 * Z + 4 * (2 + D)) + 2
  G + Z + P + M + X + D + 2 * (3 * X + 10) + X + 20

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SingleParameterPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators fwdDiff

noncomputable def integerNewtonPolynomial (s : ℕ) (c : ℕ → ℤ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    Polynomial.C ((c k : ℝ) / (k.factorial : ℝ)) * descPochhammer ℝ k

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [Unique σ] [CommRing R]

end Erdos3

end

end OAI

end


