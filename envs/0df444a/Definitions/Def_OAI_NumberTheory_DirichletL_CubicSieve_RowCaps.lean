-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T09:52:08.077691+00:00
-- url     : https://prove2.me/theorems/fd589af1-60f2-4315-aa8a-ffce3d7a27e7
-- title:
--   Row Caps
-- statement:
--   Definitions and structural lemmas for Row Caps, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/RowCaps.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotient_localHomeomorph
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
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
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
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
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
def globalFirstRowCap (K ell B F : ℝ) : ℝ :=
  (Real.exp 1)^2*ell^2*B^6*F^2/K
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
noncomputable abbrev actualSextic := ActualEisensteinCubic.canonicalSextic
def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)
def exceptionalBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i, exceptionalPiece (P i) (e i) n b
def exceptionalDivisor {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    (e : ι→Fin 3) (v : Fin 3) : Ideal O := ∏i, if e i=v then P i else 1
def exceptionalSize {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) : ℝ :=
  ∏i, if e i=0 then (rootCard (O ⧸ P i))⁻¹ else rootCard (O ⧸ P i)
end CompletedGauss
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss
end CanonicalQuadraticSieve
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff
namespace CubicEisenstein
def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I
def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2
def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)
def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]
lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)
abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}
def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩
lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop
def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous
def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph
lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold
namespace CubicEisenstein
abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel
def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates
def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w
def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))
def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart
end CubicEisenstein
end
end OAI


