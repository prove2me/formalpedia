-- Prove2me | Definitions.Def_QEC_Coding_ReedSolomon_FullLength
-- name    : QEC_Coding_ReedSolomon_FullLength
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:09:36.937064+00:00
-- url     : https://prove2.me/theorems/c7669abd-50bd-4408-ac8b-9cf954a45907
-- title:
--   Full Length
-- statement:
--   Definitions and structural lemmas for Full Length, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/FullLength.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
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
namespace KT19ReedSolomon
open scoped BigOperators
def Admissible (p l k : Nat) : Prop :=
  Nat.Prime p ∧ 1 ≤ k ∧ k ≤ l ∧ l ≤ p ∧ 3 * l ≤ p + 1
def evaluationMap (p : Nat) (polynomial : Polynomial (ZMod p)) :
    Word (ZMod p) (ZMod p) :=
  fun point => polynomial.eval point
def evaluationLinearMap (p l : Nat) :
    Polynomial.degreeLT (ZMod p) l →ₗ[ZMod p] Word (ZMod p) (ZMod p) where
  toFun polynomial := evaluationMap p polynomial.1
  map_add' left right := by
    funext point
    simp [evaluationMap]
  map_smul' scalar polynomial := by
    funext point
    simp [evaluationMap, Algebra.smul_def]
@[simp]
theorem evaluationLinearMap_apply (p l : Nat)
    (polynomial : Polynomial.degreeLT (ZMod p) l) (point : ZMod p) :
    evaluationLinearMap p l polynomial point = polynomial.1.eval point :=
  rfl
def coordinatewiseProduct {p : Nat}
    (left right : Word (ZMod p) (ZMod p)) : Word (ZMod p) (ZMod p) :=
  fun point => left point * right point
theorem mul_mem_degreeLT (p l m : Nat) [Fact p.Prime]
    (left : Polynomial.degreeLT (ZMod p) l)
    (right : Polynomial.degreeLT (ZMod p) m) :
    left.1 * right.1 ∈ Polynomial.degreeLT (ZMod p) (l + m - 1) := by
  by_cases hleft : left.1 = 0
  · simp [hleft]
  by_cases hright : right.1 = 0
  · simp [hright]
  have hleftDegree : left.1.natDegree < l := by
    have hdegree := Polynomial.mem_degreeLT.mp left.2
    rw [Polynomial.degree_eq_natDegree hleft] at hdegree
    exact_mod_cast hdegree
  have hrightDegree : right.1.natDegree < m := by
    have hdegree := Polynomial.mem_degreeLT.mp right.2
    rw [Polynomial.degree_eq_natDegree hright] at hdegree
    exact_mod_cast hdegree
  rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree (mul_ne_zero hleft hright),
    Polynomial.natDegree_mul hleft hright]
  exact_mod_cast (show left.1.natDegree + right.1.natDegree < l + m - 1 by omega)
theorem evaluationLinearMap_injective (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) : Function.Injective (evaluationLinearMap p l) := by
  intro left right hevaluation
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (Finset.univ : Finset (ZMod p))
  · have hdegree := Polynomial.mem_degreeLT.mp left.2
    exact hdegree.trans_le (by simpa [ZMod.card] using hlp)
  · have hdegree := Polynomial.mem_degreeLT.mp right.2
    exact hdegree.trans_le (by simpa [ZMod.card] using hlp)
  · intro point _
    exact congrFun hevaluation point
noncomputable def fullEvaluationLinearEquiv (p : Nat) [Fact p.Prime] :
    Polynomial.degreeLT (ZMod p) p ≃ₗ[ZMod p] Word (ZMod p) (ZMod p) := by
  apply LinearEquiv.ofBijective (evaluationLinearMap p p)
  refine ⟨evaluationLinearMap_injective p p le_rfl, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
  · exact evaluationLinearMap_injective p p le_rfl
  · rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis (ZMod p) p),
      Fintype.card_fin, Module.finrank_fintype_fun_eq_card, ZMod.card]
def reedSolomonCode (p l : Nat) [Fact p.Prime] : LinearCode (ZMod p) (ZMod p) where
  carrier := LinearMap.range (evaluationLinearMap p l)
def coordinatewiseProductCode {p : Nat} [Fact p.Prime]
    (left right : LinearCode (ZMod p) (ZMod p)) : LinearCode (ZMod p) (ZMod p) where
  carrier := Submodule.span (ZMod p)
    {word | ∃ x ∈ left.carrier, ∃ y ∈ right.carrier,
      coordinatewiseProduct x y = word}
end KT19ReedSolomon
end Coding
end QEC


