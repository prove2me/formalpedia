-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
-- name    : OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:18:14.467994+00:00
-- url     : https://prove2.me/theorems/dcffdeb9-66ee-4bd0-988e-63f8f9bcc4f4
-- title:
--   Reflected Branches
-- statement:
--   Definitions and structural lemmas for Reflected Branches, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/ReflectedBranches.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_complexDiagonal_action
import Theorems.Thm_OAI_CubicEisenstein_complexTranslation_action
import Theorems.Thm_OAI_CubicEisenstein_complexWeyl_action
import Theorems.Thm_OAI_CubicEisenstein_complex_bruhat_nonzero
import Theorems.Thm_OAI_CubicEisenstein_complex_bruhat_zero
import Theorems.Thm_OAI_CubicEisenstein_euclideanComplexDilation_apply
import Theorems.Thm_OAI_CubicEisenstein_euclideanInversion_hasFDerivAt
import Theorems.Thm_OAI_CubicEisenstein_euclideanToHyperbolic_positive
import Theorems.Thm_OAI_CubicEisenstein_euclideanUpperHalf_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_euclideanWeylAction_apply
import Theorems.Thm_OAI_CubicEisenstein_euclideanWeylReflection_apply
import Theorems.Thm_OAI_CubicEisenstein_euclidean_complex_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_upperPoint
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialCoordinates_reconstruct
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_integralOrbitProjection_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_contMDiff
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_upperPoint_congr
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
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
open scoped BigOperators Classical
namespace CompletedGauss
section
open ActualEisensteinCubic LocalReflectionBrackets
def reflectedLocalPiece (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) : ℂ :=
  if j=4 then exceptionalPiece P e n b
  else if e=0 then bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3)) else 0
def reflectedLocalSize (P : Ideal O) [P.IsMaximal] (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P))
  else if j=0 then (rootCard (O ⧸ P))⁻¹ else 1
def reflectedBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i,reflectedLocalPiece (P i) (hg i) (j i) (e i) n b
end
open scoped BigOperators Classical SchwartzMap ContDiff Topology
open MeasureTheory Filter
theorem Vstar_contDiff (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Vstar W) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have hz : (Vstar W)=ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℂ)) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      change y<a at hy
      have hw : W y=0 := by
        by_contra hn
        have hh := (hsupp hn).1
        linarith
      simp only [Vstar,hw,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_sqrt hx)).mul hW.contDiffAt
theorem Vstar_support (W : ℝ→ℂ) (a b : ℝ)
    (hsupp : Function.support W⊆Set.Icc a b) : Function.support (Vstar W)⊆Set.Icc a b := by
  intro x hx
  apply hsupp
  intro hz
  exact hx (by simp [Vstar,hz])
def vstarSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Vstar_support W a b hsupp)).toSchwartzMap
    (Vstar_contDiff W a b ha hsupp hW)
@[simp] theorem vstarSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (x : ℝ) :
    vstarSchwartz W a b ha hsupp hW x=Vstar W x := rfl
end CompletedGauss
namespace InitialMeanSquare
open SecondPassArithmetic
end InitialMeanSquare
namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups Matrix InnerProductSpace
def hyperbolicEuclideanCoordinates (w : HyperbolicSpace) : EuclideanSpatial :=
  WithLp.toLp 2 (hyperbolicSpatialCoordinates w)
lemma hyperbolicEuclideanCoordinates_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicEuclideanCoordinates (upperPoint z v hv)=WithLp.toLp 2 ![z.re,z.im,v] := by
  simp only [hyperbolicEuclideanCoordinates,hyperbolicSpatialCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
lemma euclideanToHyperbolic_coordinates (w : HyperbolicSpace) :
    euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)=w := by
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  rw [euclideanToHyperbolic_positive _ hp]
  change upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+Complex.I*(hyperbolicSpatialCoordinates w 1:ℂ))
    (hyperbolicSpatialCoordinates w 2) hp=w
  simpa only [mul_comm] using hyperbolicSpatialCoordinates_reconstruct w
lemma hyperbolicEuclideanCoordinates_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicEuclideanCoordinates (euclideanToHyperbolic p)=p := by
  rw [euclideanToHyperbolic_positive _ hp,hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp
def euclideanAction (g : SL(2,ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  hyperbolicEuclideanCoordinates (g•euclideanToHyperbolic p)
lemma euclideanAction_positive (g : SL(2,ℂ)) (p : EuclideanSpatial) :
    0<euclideanAction g p 2 := by
  change 0<hyperbolicHeight (g•euclideanToHyperbolic p)
  exact hyperbolicHeight_pos _
lemma euclideanAction_mul (g h : SL(2,ℂ)) :
    euclideanAction (g*h)=euclideanAction g ∘ euclideanAction h := by
  funext p
  simp only [euclideanAction,Function.comp_apply,euclideanToHyperbolic_coordinates,mul_smul]
lemma euclideanAction_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexTranslation b) p=p+euclideanHorizontalTranslation b := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexTranslation_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp [euclideanHorizontalTranslation]
lemma euclideanAction_diagonal (b : ℂ) (hb : b≠0) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexDiagonal b hb) p=euclideanComplexDilation b p := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexDiagonal_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j
  · simpa [Complex.mul_re] using h0.symm
  · simpa [Complex.mul_im,add_comm] using h1.symm
  · exact h2.symm
lemma euclideanAction_weyl (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction complexWeyl p=euclideanWeylAction p := by
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  have hq : 0<euclideanWeylAction p 2 := by
    rw [(euclideanWeylAction_apply p).2.2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  have h := congrArg hyperbolicEuclideanCoordinates
    (show euclideanToHyperbolic (euclideanWeylAction p)=
      complexWeyl•euclideanToHyperbolic p from by
      rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
      obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
      apply upperPoint_congr
      · rw [h0,h1,euclidean_complex_norm_sq]
        simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
          Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
        field_simp
        ; ring
      · rw [h2,euclidean_complex_norm_sq]
        field_simp)
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ hq,euclideanAction] using h.symm
lemma euclideanWeylReflection_norm (u : EuclideanSpatial) : ‖euclideanWeylReflection u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanWeylReflection_apply u
  simp only [Fin.sum_univ_three,h0,h1,h2,neg_sq]
lemma euclideanComplexDilation_norm (b : ℂ) (u : EuclideanSpatial) :
    ‖euclideanComplexDilation b u‖=Complex.normSq b*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (norm_nonneg _))).mp
  have h : (b^2).re^2+(b^2).im^2=(Complex.normSq b)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq b 2
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b u
  simp only [Fin.sum_univ_three,h0,h1,h2]
  calc
    _ = ((b^2).re^2+(b^2).im^2)*((u 0)^2+(u 1)^2)+(Complex.normSq b)^2*(u 2)^2 := by ring
    _ = _ := by rw [h]; ring
lemma euclideanInversionDeriv_norm (p u : EuclideanSpatial) :
    ‖euclideanInversionDeriv p u‖=(1/‖p‖)^2*‖u‖ := by
  unfold euclideanInversionDeriv
  rw [_root_.smul_apply,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  simp only [LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map]
def HyperbolicDifferentialIsometry (g : SL(2,ℂ)) : Prop :=
  ∀p : EuclideanSpatial,0<p 2 → ∃A : EuclideanSpatial→L[ℝ]EuclideanSpatial,
    HasFDerivAt (euclideanAction g) A p ∧
    ∀u,‖A u‖*p 2=‖u‖*euclideanAction g p 2
lemma hyperbolicDifferentialIsometry_mul (g h : SL(2,ℂ))
    (hg : HyperbolicDifferentialIsometry g) (hh : HyperbolicDifferentialIsometry h) :
    HyperbolicDifferentialIsometry (g*h) := by
  intro p hp
  obtain ⟨B,hB,hBn⟩ := hh p hp
  obtain ⟨A,hA,hAn⟩ := hg (euclideanAction h p) (euclideanAction_positive h p)
  refine ⟨A.comp B,?_,?_⟩
  · rw [euclideanAction_mul]
    exact hA.comp p hB
  · intro u
    rw [euclideanAction_mul]
    change ‖A (B u)‖*p 2=‖u‖*euclideanAction g (euclideanAction h p) 2
    apply (mul_right_inj' (euclideanAction_positive h p).ne').mp
    calc
      _ = (‖A (B u)‖*euclideanAction h p 2)*p 2 := by ring
      _ = (‖B u‖*euclideanAction g (euclideanAction h p) 2)*p 2 := by rw [hAn]
      _ = (‖B u‖*p 2)*euclideanAction g (euclideanAction h p) 2 := by ring
      _ = _ := by rw [hBn]; ring
lemma hyperbolicDifferentialIsometry_translation (b : ℂ) :
    HyperbolicDifferentialIsometry (complexTranslation b) := by
  intro p hp
  refine ⟨ContinuousLinearMap.id ℝ _,?_,?_⟩
  · apply ((hasFDerivAt_id p).add_const (euclideanHorizontalTranslation b)).congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_translation b q hq
  · intro u
    rw [euclideanAction_translation b p hp]
    simp [euclideanHorizontalTranslation]
lemma hyperbolicDifferentialIsometry_diagonal (b : ℂ) (hb : b≠0) :
    HyperbolicDifferentialIsometry (complexDiagonal b hb) := by
  intro p hp
  refine ⟨euclideanComplexDilation b,?_,?_⟩
  · apply (euclideanComplexDilation b).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_diagonal b hb q hq
  · intro u
    rw [euclideanComplexDilation_norm,euclideanAction_diagonal b hb p hp,
      (euclideanComplexDilation_apply b p).2.2]
    ring
lemma hyperbolicDifferentialIsometry_weyl : HyperbolicDifferentialIsometry complexWeyl := by
  intro p hp
  refine ⟨euclideanWeylReflection.comp (euclideanInversionDeriv p),?_,?_⟩
  · have h := euclideanWeylReflection.hasFDerivAt.comp p
      (euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp))
    apply h.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_weyl q hq
  · intro u
    change ‖euclideanWeylReflection (euclideanInversionDeriv p u)‖*p 2=_
    rw [euclideanWeylReflection_norm,euclideanInversionDeriv_norm,euclideanAction_weyl p hp,
      (euclideanWeylAction_apply p).2.2]
    ring
theorem hyperbolicDifferentialIsometry (g : SL(2,ℂ)) : HyperbolicDifferentialIsometry g := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_diagonal _ ha)
      (hyperbolicDifferentialIsometry_translation _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicDifferentialIsometry_mul _ _
      (hyperbolicDifferentialIsometry_mul _ _
        (hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_translation _)
          (hyperbolicDifferentialIsometry_diagonal _ (inv_ne_zero hc)))
        hyperbolicDifferentialIsometry_weyl)
      (hyperbolicDifferentialIsometry_translation _)
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
namespace CubicEisenstein
lemma norm_comp_scaled_isometry (A : EuclideanSpatial→L[ℝ]EuclideanSpatial) (r : ℝ)
    (hr : 0<r) (hA : ∀u,‖A u‖=r*‖u‖) (φ : EuclideanSpatial→L[ℝ]ℝ) :
    ‖φ.comp A‖=r*‖φ‖ := by
  let iso : EuclideanSpatial→ₗᵢ[ℝ]EuclideanSpatial :=
    { toLinearMap := (r⁻¹ • A).toLinearMap
      norm_map' := fun u => by
        change ‖r⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hA]
        field_simp }
  let equiv : EuclideanSpatial≃ₗᵢ[ℝ]EuclideanSpatial :=
    LinearIsometryEquiv.ofSurjective iso ((LinearMap.injective_iff_surjective).mp iso.injective)
  have he : A=r • (equiv : EuclideanSpatial→L[ℝ]EuclideanSpatial) := by
    apply ContinuousLinearMap.ext
    intro u
    change A u=r • (r⁻¹ • A u)
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [he,ContinuousLinearMap.comp_smul,norm_smul,Real.norm_of_nonneg hr.le,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
lemma hyperbolic_cotangent_energy_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    (p 2)^2*‖fderiv ℝ (F ∘ euclideanAction g) p‖^2=
      (euclideanAction g p 2)^2*‖fderiv ℝ F (euclideanAction g p)‖^2 := by
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g p hp
  rw [(hF.hasFDerivAt.comp p hA).fderiv]
  have hn : ∀u,‖A u‖=(euclideanAction g p 2/p 2)*‖u‖ := by
    intro u
    calc
      ‖A u‖=(‖u‖*euclideanAction g p 2)/p 2 := (eq_div_iff hp.ne').2 (hAn u)
      _ = _ := by ring
  rw [norm_comp_scaled_isometry A _ (div_pos (euclideanAction_positive g p) hp) hn]
  field_simp
def euclideanScalarDirichletDensity (F : EuclideanSpatial→ℝ) (p : EuclideanSpatial) : ℝ :=
  (p 2)^2*‖fderiv ℝ F p‖^2
lemma euclideanScalarDirichletDensity_invariant (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hinv : F ∘ euclideanAction g=F) :
    euclideanScalarDirichletDensity F (euclideanAction g p)=euclideanScalarDirichletDensity F p := by
  have h := hyperbolic_cotangent_energy_comp g F p hp hF
  rw [hinv] at h
  exact h.symm
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
namespace CubicEisenstein
lemma hyperbolicSpatialChart_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicSpatialChart (euclideanToHyperbolic p)=p.ofLp :=
  congrArg WithLp.ofLp (hyperbolicEuclideanCoordinates_toHyperbolic p hp)
lemma euclideanToHyperbolic_contMDiffAt (p : EuclideanSpatial) (hp : 0<p 2) :
    ContMDiffAt 𝓘(ℝ,EuclideanSpatial) 𝓘(ℝ,SpatialCoordinates) ∞ euclideanToHyperbolic p := by
  have ht : p.ofLp∈hyperbolicSpatialChart.target := by
    rw [←hyperbolicSpatialChart_toHyperbolic p hp]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,SpatialCoordinates)) (n := ∞) (x := euclideanToHyperbolic p))
  have hd := (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds ht)).comp p
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.contDiffAt.contMDiffAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
    with q hq
  change euclideanToHyperbolic q=hyperbolicSpatialChart.symm q.ofLp
  rw [←hyperbolicSpatialChart_toHyperbolic q hq,hyperbolicSpatialChart.left_inv (Set.mem_univ _)]
def kernelTestField (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  f.1 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))
lemma kernelTestField_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f) p :=
  (((f.2.1.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
lemma kernelTestField_re_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).re) p :=
  Complex.reCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)
lemma kernelTestField_im_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).im) p :=
  Complex.imCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)
lemma kernelTestField_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (p : EuclideanSpatial) :
    kernelTestField f (euclideanAction (integralComplexMatrix M) p)=kernelTestField f p := by
  simp only [kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,integralOrbitProjection_eq]
def kernelTestEnergyDensity (f : kernelSmoothTests) (w : HyperbolicSpace) : ℝ :=
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)+
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)
lemma kernelTestEnergyDensity_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f (integralComplexMatrix M•w)=kernelTestEnergyDensity f w := by
  have he : hyperbolicEuclideanCoordinates (integralComplexMatrix M•w)=
      euclideanAction (integralComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    simp only [euclideanAction,euclideanToHyperbolic_coordinates]
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  unfold kernelTestEnergyDensity
  rw [he]
  congr 1
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.re (kernelTestField_invariant f M p)
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.im (kernelTestField_invariant f M p)
def kernelQuotientEnergyDensity (f : kernelSmoothTests) : KernelQuotient→ℝ :=
  Quotient.lift (kernelTestEnergyDensity f) (by
    intro u v huv
    obtain ⟨M,hM⟩ := huv
    rw [←hM]
    exact (kernelTestEnergyDensity_invariant f M u).symm)
def kernelDirichletEnergy (f : kernelSmoothTests) : ℝ :=
  ∫q,kernelQuotientEnergyDensity f q ∂integralQuotientVolume globalKubotaKernel
end CubicEisenstein
end
end OAI


