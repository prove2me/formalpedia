-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T07:48:38.803861+00:00
-- url     : https://prove2.me/theorems/fc29e6d5-9355-4695-8a0e-ec79ab6a403f
-- title:
--   Transformed Columns
-- statement:
--   Definitions and structural lemmas for Transformed Columns, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_continuous_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_isFundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicHeight_pos
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicVolume_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_integralOrbitProjection_eq
import Theorems.Thm_OAI_CubicEisenstein_measurable_integralOrbitProjection
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
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.InitialMeanSquare.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S
def transformedColumn (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S*Ψ (∏i∈S,p i)*
    rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)*
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h*H S
def initialPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) : ℂ :=
  ∑S∈F.powerset,∑T∈F.powerset,if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S*inputColumn p Ψ₁ b d H₁ S)*
      (supportMobius (fun i => Ideal.span {p i}) T*inputColumn p Ψ₂ b d H₂ T)*
      activeGaussRowFactor p hp hinj hg T S d h else 0
def childSum (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) : ℂ :=
  ∑N∈F.powerset,secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
    (fun U => H (V∪U)) N
end InitialMeanSquare
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩
instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)
instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]
lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w
end CubicEisenstein
namespace SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
end CanonicalQuadraticSieve
end
end OAI


