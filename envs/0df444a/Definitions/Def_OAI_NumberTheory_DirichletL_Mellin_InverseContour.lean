-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
-- name    : OAI_NumberTheory_DirichletL_Mellin_InverseContour
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:04:27.484986+00:00
-- url     : https://prove2.me/theorems/acf68799-6c9b-4ac3-81e9-78680e34c387
-- title:
--   Inverse Contour
-- statement:
--   Definitions and structural lemmas for Inverse Contour, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/InverseContour.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply


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
namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
def inverseMellinIntegrand (V : ℝ → ℂ) (j : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (-s) * mellinEulerData V j s
def paperEulerKernel (V : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  mellinInv 0 (mellinEulerData V j) (paperScale * x)
end CubicReflectionKernel
namespace DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge
abbrev O := ActualEisensteinCubic.O
end DescentFiberCost
namespace EisensteinSchwartzPoisson
open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
end EisensteinSchwartzPoisson
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel
def logRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 1
theorem logRadius_pos (a b : ℝ) : 0 < logRadius a b := by unfold logRadius; positivity
def logCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b
  rOut := logRadius a b + 1
  rIn_pos := logRadius_pos a b
  rIn_lt_rOut := by linarith
def logOuterCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b + 1
  rOut := logRadius a b + 2
  rIn_pos := by have := logRadius_pos a b; linarith
  rIn_lt_rOut := by linarith
def expCorrection (a b u : ℝ) : ℝ := logOuterCutoff a b u * (Real.exp u - u)
def patchedExp (a b u : ℝ) : ℝ := u + expCorrection a b u
theorem expCorrection_compact (a b : ℝ) : HasCompactSupport (expCorrection a b) :=
  (logOuterCutoff a b).hasCompactSupport.mul_right
theorem expCorrection_smooth (a b : ℝ) : ContDiff ℝ ∞ (expCorrection a b) :=
  (logOuterCutoff a b).contDiff.mul (Real.contDiff_exp.sub contDiff_id)
theorem patchedExp_temperate (a b : ℝ) : Function.HasTemperateGrowth (patchedExp a b) :=
  Function.HasTemperateGrowth.id'.add ((expCorrection_compact a b).hasTemperateGrowth
    (expCorrection_smooth a b))
theorem patchedExp_proper (a b : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : ℝ, ‖u‖ ≤ C * (1 + ‖patchedExp a b u‖) ^ k := by
  obtain ⟨u₀, hu₀⟩ := (expCorrection_smooth a b).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (expCorrection_compact a b).norm
  refine ⟨1, ‖expCorrection a b u₀‖ + 1, ?_⟩
  intro u
  have htriangle : ‖u‖ ≤ ‖patchedExp a b u‖ + ‖expCorrection a b u‖ := by
    simpa only [patchedExp, add_sub_cancel_right] using
      norm_sub_le (patchedExp a b u) (expCorrection a b u)
  have hbound := hu₀ u
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedExp a b u), norm_nonneg (expCorrection a b u₀)]
def logPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (logCutoff a b)).comp
    (SchwartzMap.compCLM ℝ (patchedExp_temperate a b) (patchedExp_proper a b))
end CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel
end CubicReflectionKernel
end
end OAI


