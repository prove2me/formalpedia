-- Prove2me | Definitions.Def_QEC_Coding_ChainComplex_FinitePath
-- name    : QEC_Coding_ChainComplex_FinitePath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:08:00.321836+00:00
-- url     : https://prove2.me/theorems/02773884-e4d0-4d1f-ba4d-f3ffca08059c
-- title:
--   Finite Path
-- statement:
--   Definitions and structural lemmas for Finite Path, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/FinitePath.lean

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
def left {n : Nat} (j : Fin n) : Fin (n + 1) := ⟨j.1, by omega⟩
def right {n : Nat} (j : Fin n) : Fin (n + 1) := ⟨j.1 + 1, by omega⟩
def previous {n : Nat} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : 0 < i.1 then some ⟨i.1 - 1, by omega⟩ else none
def next {n : Nat} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.1 < n then some ⟨i.1, by omega⟩ else none
def optionalSingle {Index : Type*} [DecidableEq Index]
    (o : Option Index) : Word F Index :=
  match o with
  | none => 0
  | some i => Pi.single i 1
def vertexCoboundary {n : Nat} (i : Fin (n + 1)) : Word F (Fin n) :=
  optionalSingle (F := F) (previous i) + optionalSingle (F := F) (next i)
def edgeBoundary {n : Nat} (j : Fin n) : Word F (Fin (n + 1)) :=
  Pi.single (left j) 1 + Pi.single (right j) 1
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem optionalSingle_previous_apply {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    optionalSingle (F := F) (previous i) j = if right j = i then 1 else 0 := by
  classical
  by_cases hi : 0 < i.1
  · by_cases hRight : right j = i
    · subst i
      simp [previous, optionalSingle, right]
    · have hne : (⟨i.1 - 1, by omega⟩ : Fin n) ≠ j := by
        intro h
        apply hRight
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simp [right]
        omega
      simp [previous, hi, optionalSingle, hRight, hne]
  · have hRight : right j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [right] at hv
      omega
    simp [previous, hi, optionalSingle, hRight]
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem optionalSingle_next_apply {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    optionalSingle (F := F) (next i) j = if left j = i then 1 else 0 := by
  classical
  by_cases hi : i.1 < n
  · by_cases hLeft : left j = i
    · subst i
      simp [next, optionalSingle, left]
    · have hne : (⟨i.1, hi⟩ : Fin n) ≠ j := by
        intro h
        apply hLeft
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simpa [left] using hv.symm
      simp [next, hi, optionalSingle, hLeft, hne]
  · have hLeft : left j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [left] at hv
      omega
    simp [next, hi, optionalSingle, hLeft]
def boundary {n : Nat} : Word F (Fin (n + 1)) →ₗ[F] Word F (Fin n) where
  toFun x j := ∑ i : Fin (n + 1), x i * vertexCoboundary (F := F) i j
  map_add' x y := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' coefficient x := by
    ext j
    simp [Finset.mul_sum, mul_assoc]
end QEC.Coding.FinitePath


