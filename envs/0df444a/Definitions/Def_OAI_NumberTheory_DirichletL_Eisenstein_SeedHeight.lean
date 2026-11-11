-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:06:30.754278+00:00
-- url     : https://prove2.me/theorems/0c477959-06f0-49dd-81b5-ae2dac6d61d8
-- title:
--   Seed Height
-- statement:
--   Definitions and structural lemmas for Seed Height, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SeedHeight.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_CubicReopening
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_MeromorphicResolvent
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_eq
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_pos
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_smooth
import Theorems.Thm_OAI_CubicEisenstein_actual_smoothCuspSeed_contDiffAt
import Theorems.Thm_OAI_CubicEisenstein_cuspTransition_contDiff
import Theorems.Thm_OAI_CubicEisenstein_embeddedRow_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_heightDenominator_eq_quadratic
import Theorems.Thm_OAI_CubicEisenstein_heightDenominator_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEisenstein_upperPoint
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_target_positive
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelExhaustionCutoff_hasCompactSupport
import Theorems.Thm_OAI_CubicEisenstein_kernelExhaustionCutoff_smooth
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_contMDiff
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientEisenstein_mk
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
import Theorems.Thm_OAI_CubicEisenstein_norm_le_sqrt_rowEnergy
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_rowEnergy_nonneg
import Theorems.Thm_OAI_CubicEisenstein_rowEnergy_pos
import Theorems.Thm_OAI_CubicEisenstein_smoothEisenstein_eq_actual
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_summable_norm_summand
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
lemma kernel_compact_seed_height_bound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    ∃B : ℝ,a≤B ∧ 3≤B ∧ ∀q∈S,kernelQuotientBarrier 2 3 q≤B := by
  obtain ⟨B,hB⟩ := (hS.image (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num)).continuous).bddAbove
  refine ⟨max a (max 3 B),le_max_left _ _,(le_max_left 3 B).trans (le_max_right _ _),?_⟩
  intro q hq
  exact (hB (Set.mem_image_of_mem _ hq)).trans ((le_max_right 3 B).trans (le_max_right _ _))
def kernelSeedHeightBound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) : ℝ :=
  Classical.choose (kernel_compact_seed_height_bound a S hS)
lemma kernelSeedHeightBound_spec (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    a≤kernelSeedHeightBound a S hS ∧ 3≤kernelSeedHeightBound a S hS ∧
      ∀q∈S,kernelQuotientBarrier 2 3 q≤kernelSeedHeightBound a S hS :=
  Classical.choose_spec (kernel_compact_seed_height_bound a S hS)
def compactSeedTransition (a b B : ℝ) : C(Set.Icc a B,ℂ) :=
  ⟨fun v => (cuspTransition a b (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    ((cuspTransition_contDiff a b).continuous.comp continuous_subtype_val)⟩
def compactSeedProfile (a b B : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a B,ℂ) :=
  compactSeedTransition a b B * NormedSpace.exp (s • compactLogProfile a B ha)
def kernelLocalSeedL2 (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (s : ℂ) : KernelQuotientL2 :=
  kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1
      (compactSeedProfile a b (kernelSeedHeightBound a S hS) ha s))
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
def kernelCorrectedSeed (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotient→ℂ :=
  fun q => kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q
def kernelLocalCorrectedSeed (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  kernelLocalSeedL2 S hS a b ha s +
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)
end
section
open Filter
open scoped BigOperators Classical Topology ContDiff
section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)
lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _
end PartialDerivatives
section
variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  apply contDiff_tsum (v := fun k i => ‖b i‖*C k) hprod
  · intro k hk
    exact hb.mul_right (C k)
  · intro k i x hk
    have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
        b i • iteratedFDeriv ℝ k (F (a i)) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := b i) (i := k) (x := x)
          ((hf i).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)))
    rw [he,norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)
end
lemma rowEnergy_real_smul (r : ℝ) (u : Fin 2→ℂ) :
    rowEnergy (r • u)=r^2*rowEnergy u := by
  simp only [rowEnergy,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
def normalizedComplexRow (u : Fin 2→ℂ) : Fin 2→ℂ := (Real.sqrt (rowEnergy u))⁻¹ • u
lemma normalizedComplexRow_energy (u : Fin 2→ℂ) (hu : u≠0) :
    rowEnergy (normalizedComplexRow u)=1 := by
  rw [normalizedComplexRow,rowEnergy_real_smul,inv_pow,
    Real.sq_sqrt (rowEnergy_nonneg u),inv_mul_cancel₀ (rowEnergy_pos u hu).ne']
lemma rowEnergy_continuous : Continuous rowEnergy := by
  unfold rowEnergy
  fun_prop
lemma rowEnergy_unit_isCompact : IsCompact {u : Fin 2→ℂ | rowEnergy u=1} := by
  apply (isCompact_closedBall (0 : Fin 2→ℂ) 1).of_isClosed_subset
    (isClosed_eq rowEnergy_continuous continuous_const)
  intro u hu
  change rowEnergy u=1 at hu
  rw [Metric.mem_closedBall,dist_zero_right]
  simpa only [hu,Real.sqrt_one] using norm_le_sqrt_rowEnergy u
lemma rowEnergy_unit_ne_zero (u : Fin 2→ℂ) (hu : rowEnergy u=1) : u≠0 := by
  intro h
  simp [h,rowEnergy] at hu
def regularSpatialHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : ℝ :=
  deltaLoss*ConcreteCompactWeight.positiveExtension (p 2/deltaLoss)
lemma regularSpatialHeight_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) :
    0<regularSpatialHeight deltaLoss p :=
  mul_pos hδ (ConcreteCompactWeight.positiveExtension_pos _)
lemma regularSpatialHeight_contDiff (deltaLoss : ℝ) : ContDiff ℝ ∞ (regularSpatialHeight deltaLoss) := by
  unfold regularSpatialHeight
  exact contDiff_const.mul (ConcreteCompactWeight.positiveExtension_smooth.comp
    ((contDiff_apply ℝ ℝ 2).div_const deltaLoss))
lemma regularSpatialHeight_eq (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularSpatialHeight deltaLoss p=p 2 := by
  rw [regularSpatialHeight,ConcreteCompactWeight.positiveExtension_eq _ ((le_div_iff₀ hδ).mpr (by simpa using hp))]
  field_simp
def regularRowKernel (s : ℂ) (deltaLoss : ℝ) (u : Fin 2→ℂ) (p : SpatialCoordinates) : ℂ :=
  logRatioPower s (regularSpatialHeight deltaLoss p)
    (heightDenominator (spatialHorizontal p) (regularSpatialHeight deltaLoss p) u)
lemma regularRowDenominator_contDiff (deltaLoss : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates =>
      heightDenominator (spatialHorizontal p.2) (regularSpatialHeight deltaLoss p.2) p.1) := by
  have hc (j : Fin 2) : ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates => p.1 j) :=
    (contDiff_apply ℝ ℂ j).comp contDiff_fst
  have hz := spatialHorizontal_contDiff.comp (contDiff_snd (E := Fin 2→ℂ))
  have hv := (regularSpatialHeight_contDiff deltaLoss).comp (contDiff_snd (E := Fin 2→ℂ))
  have hw := ((hc 0).mul hz).add (hc 1)
  simp only [heightDenominator,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  exact (((Complex.reCLM.contDiff.comp hw).mul (Complex.reCLM.contDiff.comp hw)).add
    ((Complex.imCLM.contDiff.comp hw).mul (Complex.imCLM.contDiff.comp hw))).add
    ((((Complex.reCLM.contDiff.comp (hc 0)).mul (Complex.reCLM.contDiff.comp (hc 0))).add
      ((Complex.imCLM.contDiff.comp (hc 0)).mul (Complex.imCLM.contDiff.comp (hc 0)))).mul (hv.pow 2))
lemma regularRowKernel_contDiffAt (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) :
    ContDiffAt ℝ ∞ (Function.uncurry (regularRowKernel s deltaLoss)) (u,p) := by
  have hv : ContDiff ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => regularSpatialHeight deltaLoss q.2) :=
    (regularSpatialHeight_contDiff deltaLoss).comp contDiff_snd
  have hD := (regularRowDenominator_contDiff deltaLoss).contDiffAt (x := (u,p))
  have hv0 := regularSpatialHeight_pos deltaLoss hδ p
  have hD0 := heightDenominator_pos (spatialHorizontal p) (regularSpatialHeight deltaLoss p) hv0 u hu
  have hl := (hv.contDiffAt.log hv0.ne').sub (hD.log hD0.ne')
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (u,p) hl)).cexp
lemma heightDenominator_real_smul (z : ℂ) (v r : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (r•u)=r^2*heightDenominator z v u := by
  unfold heightDenominator
  have he : (r•u) 0*z+(r•u) 1=r•(u 0*z+u 1) := by
    simp only [Pi.smul_apply,smul_add,smul_mul_assoc]
  rw [he]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
lemma heightDenominator_normalized (z : ℂ) (v : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (normalizedComplexRow u)=heightDenominator z v u/rowEnergy u := by
  rw [normalizedComplexRow,heightDenominator_real_smul,inv_pow,Real.sq_sqrt (rowEnergy_nonneg u)]
  ring
lemma normalized_row_summand (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    summand 1 s r*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p=
      smoothSummand s r p := by
  have hu := embeddedRow_ne_zero r
  have hE := rowEnergy_pos _ hu
  have hv : 0<p 2 := hδ.trans_le hp
  have hD := heightDenominator_pos (spatialHorizontal p) (p 2) hv (embeddedRow r) hu
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp,heightDenominator_normalized]
  rw [summand,rowOperator_one,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hE.ne'),
    ←Complex.ofReal_log hE.le]
  unfold smoothSummand rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  unfold logRatioPower
  rw [Real.log_div hD.ne' hE.ne',mul_assoc,←Complex.exp_add]
  congr 2
  unfold spatialHorizontal
  push_cast
  ring
theorem regular_eisenstein_compact_smooth (s : ℂ) (hs : 2<s.re)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ψ : SpatialCoordinates→ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p => ∑'r : CuspCosets,
      summand 1 s r*(ψ p*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p)) := by
  apply compact_smooth_family_tsum (fun u p => ψ p*regularRowKernel s deltaLoss u p)
    {u : Fin 2→ℂ | rowEnergy u=1} (tsupport ψ) rowEnergy_unit_isCompact hcψ
  · intro u hu p
    have hψp : ContDiffAt ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => ψ q.2) (u,p) :=
      hψ.contDiffAt.comp (u,p) contDiffAt_snd
    exact hψp.mul (regularRowKernel_contDiffAt s deltaLoss hδ u (rowEnergy_unit_ne_zero u hu) p)
  · intro u hu
    exact tsupport_mul_subset_left
  · intro r
    exact normalizedComplexRow_energy _ (embeddedRow_ne_zero r)
  · exact summable_norm_summand 1 s hs
theorem smoothEisenstein_contDiffAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (smoothEisenstein s) p := by
  let deltaLoss : ℝ:=p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates→ℂ:=fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  have hsum := regular_eisenstein_compact_smooth s hs deltaLoss hδ ψ hψ hcψ
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq
  unfold smoothEisenstein
  apply tsum_congr
  intro r
  have hψq : ψ q=1 := by simp [ψ,hχ]
  rw [hψq,one_mul]
  exact (normalized_row_summand s deltaLoss hδ r q hq.le).symm
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
lemma kernel_contMDiff_of_spatial (f : KernelQuotient→ℂ) (F : SpatialCoordinates→ℂ)
    (hF : ∀p,0<p 2→ContDiffAt ℝ ∞ F p)
    (hcoord : ∀q : KernelQuotient,∀p∈hyperbolicSpatialChart.target,
      f ((kernelQuotientChart q).symm p)=F p) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hc : ContinuousAt (kernelQuotientChart q) q :=
    (kernelQuotientChart q).continuousOn.continuousAt ((kernelQuotientChart q).open_source.mem_nhds hq)
  have heq : f=ᶠ[𝓝 q] (fun t => F (kernelQuotientChart q t)) := by
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with t ht
    rw [←hcoord q _ ((kernelQuotientChart q).map_source ht).1,
      (kernelQuotientChart q).left_inv ht]
  rw [contMDiffAt_iff]
  refine ⟨((hF _ (hyperbolicSpatialChart_target_positive hp)).continuousAt.comp hc).congr heq.symm,?_⟩
  have he : (fun p => f ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)] F := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact hcoord q p hp
  have hh := (hF _ (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'
lemma kernelQuotientEisenstein_coordinate (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientEisenstein s hs ((kernelQuotientChart q).symm p)=smoothEisenstein s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp,
    kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint,
    smoothEisenstein_eq_actual s p (hyperbolicSpatialChart_target_positive hp)]
  rfl
lemma kernelQuotientEisenstein_contMDiff (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientEisenstein s hs) :=
  kernel_contMDiff_of_spatial _ _ (smoothEisenstein_contDiffAt s hs)
    (kernelQuotientEisenstein_coordinate s hs)
lemma kernelQuotientSeed_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientSeed a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeed a b s _=smoothCuspSeedField a b s p
  rw [smoothCuspSeedField,dif_pos (hyperbolicSpatialChart_target_positive hp)]
  rfl
lemma kernelQuotientSeed_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientSeed a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeed_contDiffAt a b s ha hab)
    (kernelQuotientSeed_coordinate a b s)
def kernelCutoffRemainderTest (n : ℕ) (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) : kernelSmoothTests := by
  let f : KernelQuotient→ℂ:=fun q => (kernelExhaustionCutoff n q:ℂ)*
    (kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q)
  refine ⟨f,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space
        ((kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)))
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := by
      by_contra hne
      exact hn (subset_closure hne)
    exact hq (by simp [f,hz])
end CubicEisenstein
open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)
def HasInitialCanonicalDensityAtRadius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∀ A : ℝ,0≤A → ∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2
end InitialMeanSquare
end
end OAI


