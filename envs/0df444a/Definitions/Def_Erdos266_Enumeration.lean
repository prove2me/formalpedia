-- Prove2me | Definitions.Def_Erdos266_Enumeration
-- name    : Erdos266_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:32:33.230611+00:00
-- url     : https://prove2.me/theorems/177996cc-f0ff-49a6-9684-ba098699bd94
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
def qEnum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm
lemma exists_fresh (i : ℕ) (l : List ℚ) :
    ∃ m : ℕ, qEnum m ∉ l ∧ |qEnum m| ≤ (i : ℚ) + 1 := by
  have hIcc : (Set.Icc (0 : ℚ) 1).Infinite :=
    Set.infinite_coe_iff.mp (Set.Icc.infinite (by norm_num))
  have hsub : Set.Icc (0 : ℚ) 1 ⊆ {q : ℚ | |q| ≤ (i : ℚ) + 1} := by
    intro q hq
    have h0 : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
    rw [Set.mem_ofPred_eq, abs_le]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hdiff : ({q : ℚ | |q| ≤ (i : ℚ) + 1} \ {q | q ∈ l}).Infinite :=
    (hIcc.mono hsub).sdiff l.finite_toSet
  obtain ⟨q, hq⟩ := hdiff.nonempty
  refine ⟨qEnum.symm q, ?_, ?_⟩
  · rw [Equiv.apply_symm_apply]
    exact hq.2
  · rw [Equiv.apply_symm_apply]
    exact hq.1
def picks : ℕ → List ℚ
  | 0 => []
  | i + 1 => picks i ++ [qEnum (Nat.find (exists_fresh i (picks i)))]
def pickIdx (i : ℕ) : ℕ := Nat.find (exists_fresh i (picks i))
def tSeq (i : ℕ) : ℚ := qEnum (pickIdx i)
end Erdos266


