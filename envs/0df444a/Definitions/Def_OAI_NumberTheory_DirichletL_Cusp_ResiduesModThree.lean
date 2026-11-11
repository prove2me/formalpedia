-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
-- name    : OAI_NumberTheory_DirichletL_Cusp_ResiduesModThree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:10:06.689433+00:00
-- url     : https://prove2.me/theorems/ce25423a-038a-41e0-b231-17fdf4d8ac09
-- title:
--   Residues Mod Three
-- statement:
--   Definitions and structural lemmas for Residues Mod Three, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/ResiduesModThree.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConjugateCuspProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_unique_coordinates
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
import Theorems.Thm_OAI_CubicEisenstein_primary_coprime_three
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicRamified_omega_isUnit
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
open scoped Classical MatrixGroups
namespace EisensteinCuspModThree
section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCoordinates (eval coords eval_coords unique_coordinates eval_mul)
abbrev Pair := ZMod 3 × ZMod 3
def add (x y : Pair) : Pair := (x.1+y.1,x.2+y.2)
def neg (x : Pair) : Pair := (-x.1,-x.2)
def sub (x y : Pair) : Pair := add x (neg y)
def mul (x y : Pair) : Pair := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def scalar (a : ZMod 3) (x : Pair) : Pair := (a*x.1,a*x.2)
def residue (x : ActualEisensteinCubic.O) : Pair := ((coords x).1,(coords x).2)
def primitive (a c : Pair) : Prop := ¬(a.1+a.2=0 ∧ c.1+c.2=0)
instance primitive_decidable (a c : Pair) : Decidable (primitive a c) := inferInstanceAs
  (Decidable (¬(a.1+a.2=0 ∧ c.1+c.2=0)))
def omegaPower (k : Fin 3) : Pair := if k=0 then (1,0) else if k=1 then (0,1) else (-1,-1)
def unitPair (u : Fin 2 × Fin 3) : Pair := scalar ((-1:ZMod 3)^u.1.val) (omegaPower u.2)
def cuspPair (j : Fin 3) : Pair := if j=0 then (0,0) else if j=1 then (0,1) else (-1,-1)
def columnTop (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 0 0,0) (scalar (g 0 1) (cuspPair j))) (unitPair u)
def columnBottom (g : SL(2,ZMod 3)) (j : Fin 3) (u : Fin 2 × Fin 3) : Pair :=
  mul (add (g 1 0,0) (scalar (g 1 1) (cuspPair j))) (unitPair u)
end
open scoped Classical MatrixGroups Matrix
local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein
def unitRepresentative (u : Fin 2 × Fin 3) : ActualEisensteinCubic.Oˣ :=
  (-1:ActualEisensteinCubic.Oˣ)^u.1.val*CubicRamified.omega_isUnit.unit^u.2.val
def cuspParameter (j : Fin 3) : ActualEisensteinCubic.O := if j=0 then 0 else if j=1 then ζ else ζ^2
def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)
def unitDiagonal (u : ActualEisensteinCubic.Oˣ) : SL(2,ActualEisensteinCubic.O) :=
  ⟨!![(u:ActualEisensteinCubic.O),0;0,(↑u⁻¹:ActualEisensteinCubic.O)],by simp [Matrix.det_fin_two]⟩
def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)
end EisensteinCuspModThree
namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}
def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2
lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm
def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)
def unitLowerIntegral (u : Eisˣ) (v : ℝ) (s freq : ℂ) (a d : Eis) : ℂ :=
  ∫z in periodDomain,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z)
end CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
def unitCuspIndexEquiv (u : Eisˣ) : Eis≃Eis where
  toFun n := (u:Eis)*n
  invFun n := (↑u⁻¹:Eis)*n
  left_inv n := by simp [←mul_assoc]
  right_inv n := by simp [←mul_assoc]
end
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
end CubicEisenstein
open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
def integerUpper (b : ℤ) : SL(2,ℤ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two_of]⟩
def integerLower (c : ℤ) : SL(2,ℤ) := ⟨!![1,0;c,1],by simp [Matrix.det_fin_two_of]⟩
end CubicKubota
end
end OAI


