-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:10:37.623828+00:00
-- url     : https://prove2.me/theorems/1f8c85fe-2a75-4e69-a6c3-41e76408f443
-- title:
--   Ramified Six Branches
-- statement:
--   Definitions and structural lemmas for Ramified Six Branches, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/RamifiedSixBranches.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_cubicUnitGaussSum_one
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
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
import Theorems.Thm_OAI_SixthPowerAverage_outsideWeight_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedCoeff_zero
import Theorems.Thm_OAI_SixthPowerAverage_weightedMoebius_zero
import Theorems.Thm_OAI_SmoothMobiusCorrection_mem_primeSet
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_succ
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_zero
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.cubicUnitGaussSum_one
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
attribute [local simp] OAI.SixthPowerAverage.outsideWeight_zero
attribute [local simp] OAI.SixthPowerAverage.weightedCoeff_zero
attribute [local simp] OAI.SixthPowerAverage.weightedMoebius_zero
attribute [local simp] OAI.SmoothMobiusCorrection.mem_primeSet
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply


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
open scoped BigOperators Classical Topology MatrixGroups
section
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
def arbitraryIntervalWhittaker (a b:ℝ) (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ:=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v)
end
section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
abbrev RamifiedSixBranch := Unit ⊕ (Unit ⊕ (Unit ⊕ Fin 3))
def unitCuspUnramifiedIndex (u t:Eisˣ) (h:Eis) :Eis:=
  3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h)
def ramifiedSixIndex (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :RamifiedSixBranch→Eis
  | .inl _=>unitCuspUnramifiedIndex 1 (ramifiedCuspRoot side) h
  | .inr (.inl _)=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) (-(ramifiedCuspRoot side)) h
  | .inr (.inr (.inl _))=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) 1 h
  | .inr (.inr (.inr l))=>3*((↑(-(ramifiedCuspRoot side))⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val))^2*
        onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l
def ramifiedSixWeight (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :ℂ:=
  let t:=ramifiedCuspRoot side
  let phase:=ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑t⁻¹:Eis))
  match i with
  | .inl _=>(4:ℂ)⁻¹*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))
  | .inr (.inl _)=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((-t:Eisˣ):Eis))
  | .inr (.inr (.inl _))=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((1:Eisˣ):Eis))
  | .inr (.inr (.inr l))=>(4:ℂ)⁻¹*phase*
      (if (3:Eis)∣onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l+
          ramifiedAffineParameter (onceCuspRayIndex (-t) (ramifiedCuspScaleUnit side) l).val 1 then
        (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE
          (ninthCuspFrequency h/eisEmbedding (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val)) else 0)
def ramifiedArithmeticResidue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :ℂ:=
  ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
    unramifiedGaussResidue (ramifiedSixIndex side h hf i)
end
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
section
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
def kernelCorrespondenceMatrix (q : IntegralCoverCosets H globalKubotaKernel) : SL(2,ℂ) :=
  g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))
end
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
def kernelCorrespondenceTestLinear : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelCorrespondenceTest hHK hJK e g he
  map_add' f h := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (f+h).1
        (integralOrbitProjection globalKubotaKernel w)=
          kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)+
          kernelCorrespondenceFunction hJK e g he h.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (c•f).1
        (integralOrbitProjection globalKubotaKernel w)=
          c • kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_smul,Pi.smul_apply,Finset.smul_sum]
def kernelCorrespondenceEnergy : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelCorrespondenceTestLinear hHK hJK e g he)).extendOfNorm
    kernelEnergyGraphCore
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedCuspShiftNumerator (b : Bool) : Eis :=
  if b then -2-omega else omega-1
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
def ramifiedScaledMode (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (3*z) v hv)*
    ShortDraftTrace.breveE (-cuspFrequency h*z)
end CubicEisenstein
end
end OAI


