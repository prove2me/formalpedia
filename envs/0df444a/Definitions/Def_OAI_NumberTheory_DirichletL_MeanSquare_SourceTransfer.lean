-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T09:29:31.88836+00:00
-- url     : https://prove2.me/theorems/94459935-e244-4763-97a0-e96ac0fa6bea
-- title:
--   Source Transfer
-- statement:
--   Definitions and structural lemmas for Source Transfer, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceTransfer.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
def residualScale (Z : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*
    elementNorm (secondExpansionQuotient p x))
def sourceWeight (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (Z H : ℝ) (x : SecondExpansionData ι) : ℂ :=
  secondNormalizedExpansionWeight p hp hcop hg Ψ m 1 1 ray Z H x *
    (residualScale p Z x : ℂ)⁻¹
end
end
open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
def sourceElementData (x : SecondExpansionData ι) : ElementDatum where
  divisor := ∏i∈x.divisor,Ideal.span {p i}
  shared := ∏i∈x.overlap,p i
  frequency := x.frequency
def sourceObservation (x : SecondExpansionData ι) : O×O :=
  (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*x.frequency,
   primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*∏i∈x.overlap,p i)
end
end InitialMeanSquare
namespace CubicEisenstein
section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv
abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
example : InnerProductSpace ℂ EuclideanGradientL2 := inferInstance
example : CompleteSpace EuclideanGradientL2 := inferInstance
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ
def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2
def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))
def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker
def euclideanWeakGradient : EuclideanL2 →ₗ.[ℂ] EuclideanGradientL2 :=
  euclideanWeakGradientGraph.toLinearPMap
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv
abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)
def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap
lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous
abbrev EuclideanH1 := euclideanH1Submodule
instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe
example : InnerProductSpace ℂ EuclideanH1 := inferInstance
def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)
def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)
end CubicEisenstein
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge
def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp
def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
def sourceChildEnergy (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑u∈T,‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative)
    u.2 (if rowNegative then -u.1 else u.1)‖^2
def sourceEnergyMagnitude (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑u∈T,(rowMagnitude p hp hcop hg F Ψ m u.2 (if rowNegative then -u.1 else u.1)
    V X testNegative)^2
def sourceGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2)*
    Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)
def sourceFixedMode (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℂ :=
  ∑x∈s,w q x*
    star (fixedChildRow p hp hcop hg F Ψ₁ m (fixedSecondTest p V₁ X₁ q.1 q.2.2 true)
      (sourceObservation p x).2 (sourceObservation p x).1)*
    fixedChildRow p hp hcop hg F Ψ₂ m (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      (sourceObservation p x).2 (-(sourceObservation p x).1)
def integratedSourceMode (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)*
    sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ (t₁,t₂,t₃)
end
end InitialMeanSquare
end
end OAI


