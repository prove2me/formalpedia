-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
-- name    : OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:43:00.110041+00:00
-- url     : https://prove2.me/theorems/3f804dc2-c6e3-444c-b3b8-26781580b721
-- title:
--   Reflected Kernel
-- statement:
--   Definitions and structural lemmas for Reflected Kernel, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ReflectedKernel.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
section
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
def momentScale : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ u : ℝ, (1 + ‖u‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
end
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics
def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27
def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)
theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)
end CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics
end CubicReflectionKernel
open scoped BigOperators Classical
namespace DescentWeightedCauchy
abbrev O := ActualEisensteinCubic.O
def firstRowMap (E : Ideal O) (x : Ideal O × Ideal O) : Ideal O :=
  x.2 * x.1 ^ 2 * E
def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e
end DescentWeightedCauchy
end
end OAI


