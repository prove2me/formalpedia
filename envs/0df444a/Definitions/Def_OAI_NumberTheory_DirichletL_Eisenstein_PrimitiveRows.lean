-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:18:20.297866+00:00
-- url     : https://prove2.me/theorems/0721badc-c1d8-47df-8ae6-46940d148cf8
-- title:
--   Primitive Rows
-- statement:
--   Definitions and structural lemmas for Primitive Rows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/PrimitiveRows.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_Rows
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_cosetRow_injective
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
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
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
namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
lemma levelThree_of_entries (M : SL(2,O))
    (h : ∀ i j : Fin 2, (3 : O) ∣ M i j - (if i=j then 1 else 0)) :
    M ∈ levelThree := by
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  have hh : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
      Ideal.Quotient.mk (Ideal.span {(3 : O)}) (if i=j then 1 else 0) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using hh
lemma row_coprime (M : levelThree) : IsCoprime (row M 0) (row M 1) := by
  have h : (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 0 0, ?_⟩
  change -(M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 +
    (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 = 1
  linear_combination h
lemma exists_matrix_of_primitive_row (c d : O) (hcop : IsCoprime c d)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    ∃ M : levelThree, row M = ![c,d] := by
  obtain ⟨r,s,hrs⟩ := hcop
  let M : SL(2,O) := ⟨!![s+r*c,r*(d-1); c,d], by
    rw [Matrix.det_fin_two]
    change (s+r*c)*d-(r*(d-1))*c=1
    linear_combination hrs⟩
  have hA : s+r*c-1 = -s*(d-1) := by linear_combination hrs
  have hM : M ∈ levelThree := by
    apply levelThree_of_entries
    intro i j
    fin_cases i <;> fin_cases j
    · change (3 : O) ∣ s+r*c-1
      rw [hA]
      exact hd.mul_left (-s)
    · change (3 : O) ∣ r*(d-1)-0
      simpa only [sub_zero] using hd.mul_left r
    · change (3 : O) ∣ c-(if (1 : Fin 2)=0 then 1 else 0)
      simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_zero] using hc
    · change (3 : O) ∣ d-1
      exact hd
  exact ⟨⟨M,hM⟩, rfl⟩
def PrimitiveRow := {v : Fin 2 → O //
  IsCoprime (v 0) (v 1) ∧ (3 : O) ∣ v 0 ∧ (3 : O) ∣ v 1-1}
def cosetPrimitiveRow (x : CuspCosets) : PrimitiveRow :=
  ⟨cosetRow x, by
    induction x using Quotient.inductionOn with | _ M =>
      change IsCoprime (row M 0) (row M 1) ∧ (3 : O) ∣ row M 0 ∧ (3 : O) ∣ row M 1-1
      exact ⟨row_coprime M, levelThree_lower M, by simpa [row] using levelThree_entry M 1 1⟩⟩
lemma cosetPrimitiveRow_bijective : Function.Bijective cosetPrimitiveRow := by
  constructor
  · intro x y hxy
    exact cosetRow_injective (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨M,hM⟩ := exists_matrix_of_primitive_row (v.1 0) (v.1 1)
      v.2.1 v.2.2.1 v.2.2.2
    refine ⟨cosetOf M, ?_⟩
    apply Subtype.ext
    change row M = v.1
    rw [hM]
    funext i
    fin_cases i <;> rfl
def primitiveRowEquiv : CuspCosets ≃ PrimitiveRow := Equiv.ofBijective _ cosetPrimitiveRow_bijective
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
def primitiveRowPhase (v : PrimitiveRow) : ℂ :=
  eisEmbedding (symbol (v.1 0) (v.1 1))
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
def radialSource (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)
def radialDual (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)
def subsetNorm {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℝ :=
  Ideal.absNorm (∏ i ∈ E, P i)
def subsetMobius {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℂ :=
  UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i)
def smallDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => subsetNorm P E ≤ Z)
def largeDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => Z < subsetNorm P E)
end
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
def middleDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Y Z : ℝ) :=
  (smallDivisors P S Z).filter (fun E => Y < subsetNorm P E)
def dualNear (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0
def dualFar (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if lengthScale < ‖eisEmbedding h‖ ^ 2 then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0
end TruncatedPrincipalPoisson
namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT
end EisensteinSchwartzPoisson
open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
end TruncatedPrincipalPoisson
end
end OAI


