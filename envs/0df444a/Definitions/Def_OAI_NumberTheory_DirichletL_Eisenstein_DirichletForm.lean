-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:48:52.27563+00:00
-- url     : https://prove2.me/theorems/e7761e76-db5a-4fd8-a79b-b798b4de1cc9
-- title:
--   Dirichlet Form
-- statement:
--   Definitions and structural lemmas for Dirichlet Form, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
namespace CubicEisenstein
def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)
lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl
lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace
def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]
def kernelDirichletPairDensity (f g : kernelSmoothTests) (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4
def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel
end CubicEisenstein
namespace CompletedGauss
section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open CanonicalQuadraticSieve ActualEisensteinCubic
end
section
open ActualEisensteinCubic CanonicalQuadraticSieve
def completedRowFiber (S : Finset (Ideal O)) (Q A T : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)
end
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve
end CompletedGauss
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
def initialLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  ((CubicReflectionKernel.logProfile_compact W a b ha hs).mul_left
    (f := fun t : ℝ => (Real.exp (t/2) : ℂ))).toSchwartzMap (by
      change ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (t/2) : ℂ)*W (Real.exp t))
      have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) :=
        Real.contDiff_exp.comp (contDiff_id.div_const 2)
      exact (Complex.ofRealCLM.contDiff.comp he).mul
        (hW.comp Real.contDiff_exp))
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
end InitialMeanSquare
end
end OAI


