-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_Rows
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_Rows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:50:21.531506+00:00
-- url     : https://prove2.me/theorems/09f922f3-9a12-4009-aa7d-987b84182a7e
-- title:
--   Rows
-- statement:
--   Definitions and structural lemmas for Rows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/Rows.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicKubota_value_zero_lower_left
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
section
open scoped BigOperators Classical MatrixGroups
section
abbrev K := ActualEisensteinCubic.K
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1
lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by
  funext j
  simp only [row, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]
lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change eisEmbedding (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]
def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h
def cuspRelation : Setoid levelThree := Setoid.ker row
abbrev CuspCosets := Quotient cuspRelation
def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M
def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)
@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl
def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)
@[simp] lemma cosetCharacter_cosetOf (M : levelThree) :
    cosetCharacter (cosetOf M) = complexCharacter M := rfl
def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])
@[simp] lemma rightTranslate_cosetOf (M N : levelThree) :
    rightTranslate M (cosetOf N) = cosetOf (N*M) := rfl
lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]
@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]
def rightEquiv (M : levelThree) : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp
def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) eisEmbedding).comp levelThree.subtype
def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := eisEmbedding ∘ cosetRow x
end
section
open ActualEisensteinCubic ConcreteTraceCRT
def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))
instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance
instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance
def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨n i, by simp⟩⟩
def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (ActualEisensteinCoordinates.coords (v i.1)).1
    else (ActualEisensteinCoordinates.coords (v i.1)).2
end
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
def rowEnergy (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2
def rowOperator (g : SL(2,ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap
@[simp] lemma rowOperator_apply (g : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl
@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
def rowBound (g : SL(2,ℂ)) : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)
def summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)
def eisenstein (g : SL(2,ℂ)) (s : ℂ) : ℂ := ∑' x : CuspCosets, summand g s x
end
open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
def upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩
def heightDenominator (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2
def transformedHeight (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u
def upperEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (upperSection z v hv) s
end CubicEisenstein
end
end OAI


