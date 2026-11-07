-- Prove2me | Definitions.Def_QEC_Coding_ReedMuller_Base
-- name    : QEC_Coding_ReedMuller_Base
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:16:31.627431+00:00
-- url     : https://prove2.me/theorems/0d226d8c-c980-4797-af6c-1f6d4ae0d7f4
-- title:
--   Base
-- statement:
--   Definitions and structural lemmas for Base, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Base.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace ReedMuller
open scoped BigOperators
abbrev BooleanPoint (m : Nat) :=
  Word (ZMod 2) (Fin m)
def pointWeight {m : Nat} (point : BooleanPoint m) : Nat :=
  HammingWeight point
abbrev SquarefreeMonomial (m r : Nat) :=
  {support : Finset (Fin m) // support.card ≤ r}
abbrev ANFPolynomial (m r : Nat) :=
  Word (ZMod 2) (SquarefreeMonomial m r)
def monomialValue {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) : ZMod 2 :=
  ∏ coordinate ∈ monomial.1, point coordinate
def evaluationLinearMap (m r : Nat) :
    ANFPolynomial m r →ₗ[ZMod 2] Word (ZMod 2) (BooleanPoint m) where
  toFun polynomial point :=
    ∑ monomial, polynomial monomial * monomialValue monomial point
  map_add' := by
    intro left right
    funext point
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar polynomial
    funext point
    simp [Finset.mul_sum, mul_assoc]
@[simp]
theorem evaluationLinearMap_apply {m r : Nat}
    (polynomial : ANFPolynomial m r) (point : BooleanPoint m) :
    evaluationLinearMap m r polynomial point =
      ∑ monomial, polynomial monomial * monomialValue monomial point :=
  rfl
noncomputable def basisPolynomial {m r : Nat}
    (monomial : SquarefreeMonomial m r) : ANFPolynomial m r :=
  canonicalBasisWord monomial
@[simp]
theorem evaluation_basisPolynomial {m r : Nat}
    (monomial : SquarefreeMonomial m r) (point : BooleanPoint m) :
    evaluationLinearMap m r (basisPolynomial monomial) point =
      monomialValue monomial point := by
  classical
  simp only [evaluationLinearMap_apply, basisPolynomial, canonicalBasisWord]
  rw [Fintype.sum_eq_single monomial]
  · simp
  · intro other hne
    simp [hne]
def reedMullerCode (r m : Nat) : LinearCode (ZMod 2) (BooleanPoint m) where
  carrier := LinearMap.range (evaluationLinearMap m r)
@[simp]
theorem mem_reedMullerCode {r m : Nat}
    (word : Word (ZMod 2) (BooleanPoint m)) :
    word ∈ (reedMullerCode r m).carrier ↔
      ∃ polynomial : ANFPolynomial m r,
        evaluationLinearMap m r polynomial = word := by
  simp [reedMullerCode]
def supportPoint {m : Nat} (support : Finset (Fin m)) : BooleanPoint m :=
  fun coordinate => if coordinate ∈ support then 1 else 0
def binomialUpTo (m r : Nat) : Nat :=
  ∑ i ∈ Finset.Icc 0 r, Nat.choose m i
def supportValue {m : Nat} (support : Finset (Fin m))
    (point : BooleanPoint m) : ZMod 2 :=
  ∏ coordinate ∈ support, point coordinate
def restrictedEvaluation {m r : Nat} (support : Finset (Fin m))
    (monomials : List (SquarefreeMonomial m r)) :
    Word (ZMod 2) (BooleanPoint m) :=
  fun point => supportValue support point *
    (monomials.map fun monomial => monomialValue monomial point).sum
def binaryOverlap {m : Nat}
    (left right : Word (ZMod 2) (BooleanPoint m)) : Nat :=
  HammingWeight fun point => left point * right point
theorem binary_eq_one_of_ne_zero (value : ZMod 2)
    (hvalue : value ≠ 0) : value = 1 := by
  have hvalNe : value.val ≠ 0 :=
    (ZMod.val_eq_zero value).not.mpr hvalue
  have hvalLt : value.val < 2 := ZMod.val_lt value
  apply (ZMod.val_eq_one (by omega) value).mp
  omega
def constrainedPointEquiv {m : Nat} (support : Finset (Fin m)) :
    {point : BooleanPoint m // support ⊆ hammingSupport point} ≃
      Word (ZMod 2) {coordinate : Fin m // coordinate ∉ support} where
  toFun point coordinate := point.1 coordinate.1
  invFun complement :=
    ⟨fun coordinate => if h : coordinate ∈ support then 1 else complement ⟨coordinate, h⟩,
      by
        intro coordinate hcoordinate
        simp [hammingSupport, hcoordinate]⟩
  left_inv point := by
    apply Subtype.ext
    funext coordinate
    by_cases hcoordinate : coordinate ∈ support
    · simp only [hcoordinate, dite_true]
      have hnonzero : point.1 coordinate ≠ 0 := by
        simpa [hammingSupport] using point.2 hcoordinate
      exact (binary_eq_one_of_ne_zero _ hnonzero).symm
    · simp [hcoordinate]
  right_inv complement := by
    funext coordinate
    simp [coordinate.2]
noncomputable def activeMonomials {m r : Nat}
    (polynomial : ANFPolynomial m r) : List (SquarefreeMonomial m r) :=
  (Finset.univ.filter fun monomial => polynomial monomial ≠ 0).toList
noncomputable def highSquarefreeComplementEquiv {m r : Nat}
    (hrm : r < m) :
    {support : Finset (Fin m) // ¬ support.card ≤ r} ≃
      SquarefreeMonomial m (m - r - 1) where
  toFun support := ⟨support.1ᶜ, by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega⟩
  invFun support := ⟨support.1ᶜ, by
    intro hcard
    rw [Finset.card_compl] at hcard
    simp only [Fintype.card_fin] at hcard
    omega⟩
  left_inv support := by
    apply Subtype.ext
    simp
  right_inv support := by
    apply Subtype.ext
    simp
end ReedMuller
end Coding
end QEC


