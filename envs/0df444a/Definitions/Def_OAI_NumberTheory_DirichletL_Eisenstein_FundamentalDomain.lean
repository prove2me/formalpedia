-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T05:27:51.701578+00:00
-- url     : https://prove2.me/theorems/bafb0c72-ca3c-4801-909d-55d6db315848
-- title:
--   Fundamental Domain
-- statement:
--   Definitions and structural lemmas for Fundamental Domain, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/FundamentalDomain.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_globalKubotaKernel_mem
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEisenstein_automorphy
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicFrobenius_continuous
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicVolume_invariant
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeedDefect_automorphy
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeed_automorphy
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
namespace CubicEisenstein
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
def integralRowPair (M : SL(2,O)) : (Fin 2 → O)×(Fin 2 → O) :=
  (fun j => M 0 j,fun j => M 1 j)
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
end
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
def hyperbolicKeyCoordinates (w : HyperbolicSpace) : Fin 9 → ℝ :=
  ![hyperbolicFrobenius w,(hyperbolicGram w 0 0).re,(hyperbolicGram w 0 0).im,
    (hyperbolicGram w 0 1).re,(hyperbolicGram w 0 1).im,
    (hyperbolicGram w 1 0).re,(hyperbolicGram w 1 0).im,
    (hyperbolicGram w 1 1).re,(hyperbolicGram w 1 1).im]
def hyperbolicOrderKey (w : HyperbolicSpace) : Lex (Fin 9 → ℝ) := toLex (hyperbolicKeyCoordinates w)
attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous
instance integralSLCountable : Countable (SL(2,O)) := by
  let : Countable O := latticeCoordEquiv.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) O) := inferInstanceAs (Countable (Fin 2 → Fin 2 → O))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) O // A.det=1})
instance integralSubgroupHyperbolicAction (H : Subgroup (SL(2,O))) : MulAction H HyperbolicSpace :=
  MulAction.compHom HyperbolicSpace (integralComplexMatrix.comp H.subtype)
lemma integralSubgroup_smul (H : Subgroup (SL(2,O))) (M : H) (w : HyperbolicSpace) :
    M • w=integralComplexMatrix (M:SL(2,O)) • w := rfl
def hyperbolicFundamentalSet (H : Subgroup (SL(2,O))) : Set HyperbolicSpace :=
  {w | ∀M : H,hyperbolicOrderKey w≤hyperbolicOrderKey (M • w)}
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
instance integralSubgroupMeasurableAction (H : Subgroup (SL(2,O))) :
    MeasurableConstSMul H HyperbolicSpace :=
  ⟨fun M => (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable⟩
instance integralSubgroupVolumeInvariant (H : Subgroup (SL(2,O))) :
    SMulInvariantMeasure H HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul M s hs := by
    have hm := (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s)
      (hyperbolicVolume_invariant (integralComplexMatrix (M:SL(2,O))))
    simpa only [Measure.map_apply hm hs,integralSubgroup_smul] using he
def integralQuotientVolume (H : Subgroup (SL(2,O))) : Measure (IntegralOrbitQuotient H) :=
  Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))
abbrev KernelQuotientL2 := Lp ℂ 2 (integralQuotientVolume globalKubotaKernel)
example : InnerProductSpace ℂ KernelQuotientL2 := inferInstance
example : CompleteSpace KernelQuotientL2 := inferInstance
lemma kernel_eisenstein_invariant (M : globalKubotaKernel) (s : ℂ) (hs : 2<s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (M • w)=hyperbolicEisenstein s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := hyperbolicEisenstein_automorphy (⟨(M:SL(2,O)),hM⟩ : levelThree) s hs w
  rw [hchar,one_mul] at he
  exact he
def kernelQuotientEisenstein (s : ℂ) (hs : 2<s.re) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (hyperbolicEisenstein s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_eisenstein_invariant M s hs w).symm)
lemma kernel_seed_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (M • w)=smoothCuspSeed a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeed_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he
lemma kernel_defect_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (M • w)=smoothCuspSeedDefect a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeedDefect_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he
def kernelQuotientSeed (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeed a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_seed_invariant a b s M w).symm)
def kernelQuotientDefect (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeedDefect a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_defect_invariant a b s M w).symm)
end CubicEisenstein
open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
def largeCubeCoefficient (H₀ : ℝ) (B : Ideal O) : ℂ :=
  if B=⊥ then 0 else ∑ H∈idealDivisors B,
    if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0
end CompletedGauss
end
end OAI


