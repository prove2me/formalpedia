-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
-- name    : OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:24:00.359621+00:00
-- url     : https://prove2.me/theorems/bf5d08a4-fdd1-46e9-b7f9-5108282c0003
-- title:
--   Ramified Symbol
-- statement:
--   Definitions and structural lemmas for Ramified Symbol, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedSymbol.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat_eq_one_iff
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
import Theorems.Thm_OAI_ShortDraftLatticeCount_coordinate_squares
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg
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
open scoped BigOperators Classical
namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
def cubicExp (n : ℤ) : O := omega ^ (n % 3).toNat
@[simp] lemma cubicExp_zero : cubicExp 0 = 1 := by simp [cubicExp]
def linearRay (u v : ℤ) (x : O) : O :=
  cubicExp (u * (((ActualEisensteinCoordinates.coords x).1 - 1) / 3) +
    v * ((ActualEisensteinCoordinates.coords x).2 / 3))
end CubicRamified
namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified
end CubicJacobiGlobal
namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount
def unitCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}
theorem q_eq_one_iff_unitCoordinates (z : ℤ × ℤ) : q z = 1 ↔ z ∈ unitCoordinates := by
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    have hs := coordinate_squares a b 1 (by norm_num) (le_of_eq h)
    have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    interval_cases a <;> interval_cases b <;> norm_num [q, unitCoordinates] at *
  · intro h
    simp only [unitCoordinates, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num [q]
theorem unit_coordinate_mem (u : Oˣ) : coords u.val ∈ unitCoordinates := by
  apply (q_eq_one_iff_unitCoordinates _).mp
  have hn := (rational_qNat_eq_one_iff u.val).mpr u.isUnit
  have hz := qO_nonneg u.val
  change (q (coords u.val)).toNat = 1 at hn
  have hi : ((q (coords u.val)).toNat : ℤ) = 1 := by exact_mod_cast hn
  simpa only [Int.toNat_of_nonneg hz] using hi
def unitCoordinateMap (u : Oˣ) : {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  ⟨coords u.val, unit_coordinate_mem u⟩
theorem unitCoordinateMap_bijective : Function.Bijective unitCoordinateMap := by
  constructor
  · intro u v huv
    apply Units.ext
    have hc := congrArg Subtype.val huv
    have he := congrArg (fun z : ℤ × ℤ => eval z.1 z.2) hc
    simpa only [unitCoordinateMap, eval_coords] using he
  · intro z
    have hq := (q_eq_one_iff_unitCoordinates z.val).mpr z.property
    have hu : IsUnit (eval z.val.1 z.val.2) := by
      apply (rational_qNat_eq_one_iff _).mp
      simp only [qNat, coords_eval, hq]
      norm_num
    refine ⟨hu.unit, Subtype.ext ?_⟩
    change coords hu.unit.val = z.val
    rw [hu.unit_spec, coords_eval]
def unitCoordinateEquiv : Oˣ ≃ {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  Equiv.ofBijective unitCoordinateMap unitCoordinateMap_bijective
end PrimaryIdealUnitReindex
open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss
end QuadraticUnitInvariance
namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
end GaussGeneratorTransport
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson
end QuadraticUnitInvariance
open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
end EisensteinSchwartzPoisson
end
end OAI


