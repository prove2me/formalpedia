-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:23:38.674199+00:00
-- url     : https://prove2.me/theorems/29e11809-2e5a-42e5-bb70-9675f2572df5
-- title:
--   Cusp Height
-- statement:
--   Definitions and structural lemmas for Cusp Height, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CuspHeight.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_cosetHeight_cosetOf
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_levelThree
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
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
namespace CubicEisenstein
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
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
def fullMatrixHeight (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) : ℝ :=
  hyperbolicHeight (integralComplexMatrix M • w)
def fullCuspHeightRelation : Setoid (SL(2,ActualEisensteinCubic.O)) := Setoid.ker fullMatrixHeight
abbrev FullCuspClasses := Quotient fullCuspHeightRelation
def fullCuspOf (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses := Quotient.mk _ M
def fullCuspHeight : FullCuspClasses→HyperbolicSpace→ℝ :=
  Quotient.lift fullMatrixHeight (fun _ _ h => h)
def fullCuspTranslate (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses→FullCuspClasses :=
  Quotient.map (fun N => N*M) (by
    intro N P h
    change fullMatrixHeight (N*M)=fullMatrixHeight (P*M)
    funext w
    have hh := congrFun h (integralComplexMatrix M • w)
    simpa only [fullMatrixHeight,map_mul,mul_smul] using hh)
lemma fullCuspTranslate_mul (M N : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses) :
    fullCuspTranslate N (fullCuspTranslate M x)=fullCuspTranslate (M*N) x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf ((P*M)*N)=fullCuspOf (P*(M*N)); rw [mul_assoc]
lemma fullCuspTranslate_one (x : FullCuspClasses) : fullCuspTranslate 1 x=x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf (P*1)=fullCuspOf P; rw [mul_one]
def fullCuspRightEquiv (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses≃FullCuspClasses where
  toFun := fullCuspTranslate M
  invFun := fullCuspTranslate M⁻¹
  left_inv x := by rw [fullCuspTranslate_mul,mul_inv_cancel,fullCuspTranslate_one]
  right_inv x := by rw [fullCuspTranslate_mul,inv_mul_cancel,fullCuspTranslate_one]
lemma fullCuspHeight_translate (M : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspRightEquiv M x) w=fullCuspHeight x (integralComplexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N => change fullMatrixHeight (N*M) w=fullMatrixHeight N (integralComplexMatrix M • w)
           simp only [fullMatrixHeight,map_mul,mul_smul]
def fullCuspProfileSum (F : ℝ→ℝ) (w : HyperbolicSpace) : ℝ :=
  ∑'x : FullCuspClasses,F (fullCuspHeight x w)
lemma fullCuspProfileSum_invariant (F : ℝ→ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    fullCuspProfileSum F (integralComplexMatrix M • w)=fullCuspProfileSum F w := by
  unfold fullCuspProfileSum
  simp only [←fullCuspHeight_translate M]
  exact (fullCuspRightEquiv M).tsum_eq (fun x : FullCuspClasses => F (fullCuspHeight x w))
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
def cuspBarrierProfile (a b v : ℝ) : ℝ := cuspTransition a b v*(v-1)
def cuspBarrier (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  1+fullCuspProfileSum (cuspBarrierProfile a b) w
lemma cuspBarrier_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    cuspBarrier a b (integralComplexMatrix M • w)=cuspBarrier a b w := by
  rw [cuspBarrier,cuspBarrier,fullCuspProfileSum_invariant]
def kernelQuotientBarrier (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrier a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrier_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff
def fullCuspFromPrincipal (r : SL(2,ActualEisensteinCubic.O)) : CuspCosets→FullCuspClasses :=
  Quotient.lift (fun N : CubicKubota.levelThree => fullCuspOf ((N:SL(2,ActualEisensteinCubic.O))*r⁻¹)) (by
    intro N P h
    apply Quotient.sound
    funext w
    have he : cosetOf N=cosetOf P := Quotient.sound h
    have hh := congrArg (fun x => cosetHeight x (integralComplexMatrix r⁻¹ • w)) he
    simpa only [cosetHeight_cosetOf,fullMatrixHeight,map_mul,mul_smul,integralComplexMatrix_levelThree] using hh)
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
def positiveHeightLaplacian (F : ℝ→ℝ) (v : ℝ) : ℝ :=
  v*deriv F v-v^2*deriv (deriv F) v
def cuspBarrierDefectProfile (a b v : ℝ) : ℝ :=
  positiveHeightLaplacian (cuspBarrierProfile a b) v-cuspBarrierProfile a b v
def cuspBarrierDefect (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  -1+fullCuspProfileSum (cuspBarrierDefectProfile a b) w
lemma cuspBarrierDefect_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O))
    (w : HyperbolicSpace) :
    cuspBarrierDefect a b (integralComplexMatrix M • w)=cuspBarrierDefect a b w := by
  rw [cuspBarrierDefect,cuspBarrierDefect,fullCuspProfileSum_invariant]
def kernelQuotientBarrierDefect (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrierDefect a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrierDefect_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
def fullCuspRow (x : FullCuspClasses) : Fin 2→ℂ :=
  complexBottomRow (integralComplexMatrix x.out)
def fullCuspProfileField (F : ℝ→ℝ) (p : SpatialCoordinates) : ℝ :=
  ∑'x : FullCuspClasses,F (rowHeight (fullCuspRow x) p)
end CubicEisenstein
end
end OAI


