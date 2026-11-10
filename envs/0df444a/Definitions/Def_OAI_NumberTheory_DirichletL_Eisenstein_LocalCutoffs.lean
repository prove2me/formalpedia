-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:19:49.076691+00:00
-- url     : https://prove2.me/theorems/7f352762-190e-46d1-91be-ef9e4be00819
-- title:
--   Local Cutoffs
-- statement:
--   Definitions and structural lemmas for Local Cutoffs, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_schwartz_mem_euclideanWeakGradientGraph
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
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv ContDiff
structure PositiveChartCutoff where
  func : EuclideanSpatial → ℝ
  smooth : ContDiff ℝ ∞ func
  compact : HasCompactSupport func
  positive : tsupport func ⊆ {p | 0 < p 2}
def kernelLocalizedField (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℂ := χ.func p • kernelTestField f p
lemma kernelLocalizedField_compact (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    HasCompactSupport (kernelLocalizedField χ f) := χ.compact.smul_right
lemma kernelLocalizedField_smooth (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ContDiff ℝ ∞ (kernelLocalizedField χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p 2
  · exact χ.smooth.contDiffAt.smul (kernelTestField_contDiffAt f p hp)
  · have hn : p ∉ tsupport χ.func := fun h => hp (χ.positive h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]
def kernelLocalizedSchwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) :=
  (kernelLocalizedField_compact χ f).toSchwartzMap (kernelLocalizedField_smooth χ f)
def kernelLocalizedH1 (χ : PositiveChartCutoff) (f : kernelSmoothTests) : EuclideanH1 := by
  let g := kernelLocalizedSchwartz χ f
  let v := WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} g).toLp 2 volume)
  refine ⟨WithLp.toLp 2 (g.toLp 2 volume,v),?_⟩
  change (g.toLp 2 volume,v)∈euclideanWeakGradientGraph
  exact schwartz_mem_euclideanWeakGradientGraph g
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal
def kernelEuclideanProjection : EuclideanSpatial → KernelQuotient :=
  integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
end
open ActualEisensteinCubic CanonicalQuadraticSieve
structure ReflectedBranchData (levelBound K : ℝ) (I F Q : Ideal O) where
  levelScale : ℝ
  levelScale_pos : 0<levelScale
  levelScale_le : levelScale≤levelBound
  primes : Finset (Ideal O)
  maximal : ∀p : primes,p.val.IsMaximal
  good : ∀p : primes,lambda∉p.val
  coprime : Pairwise (fun p r : primes => IsCoprime p.val r.val)
  divides : ∀p : primes,p.val∣I*Q
  nonresidual : ∀p : primes,¬p.val∣rowResidualPart I Q
  label : primes→Fin 3
  nColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  bColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  nBounds : ∀i,∀J∈nColumns i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2
  bBounds : ∀i,∀J∈bColumns i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1
  amplitude : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ
  amplitude_bound : ∀i,∀n∈nColumns i,∀b∈bColumns i,‖amplitude i n b‖≤1
  rowPhase : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ
  rowPhase_bound : ∀i k,‖rowPhase i k‖≤1
namespace ReflectedBranchData
def value {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k
end ReflectedBranchData
structure ReflectedFiberData (rays : ℕ) (levelBound K : ℝ) (I F Q : Ideal O) where
  pool : Finset (Ideal O)
  maximal : ∀p : pool,p.val.IsMaximal
  divides : ∀p : pool,p.val∣I*Q
  branch : (Fin rays×(pool→Fin 6))→ReflectedBranchData levelBound K I F Q
  weight : (Fin rays×(pool→Fin 6))→ℂ
  weight_bound : ∀b,‖weight b‖≤1
namespace ReflectedFiberData
def value {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*(d.branch b).value W X ρ q k
end ReflectedFiberData
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace ReflectedFiberData
def idealValue {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then d.value W X ρ q ⟨J,h⟩ else 0
end ReflectedFiberData
def HasExactCompletedModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
    (completedRowFiber rows Q A T).Nonempty →
    ∃I∈completedRowFiber rows Q A T,∃d : ReflectedFiberData rays levelBound K I F Q,
      ∀J∈completedRowFiber rows Q A T,
        completedT (Ψ J) W X=lengthScale*d.idealValue W X ρ q (rowResidualPart J Q)
end CompletedGauss
end
end OAI


