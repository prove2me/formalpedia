-- Prove2me | Definitions.Def_Bdd_Size
-- name    : Bdd_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:07:44.741765+00:00
-- url     : https://prove2.me/theorems/d85de9fb-0b17-44fb-802e-b5e50c5f9f11
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Size.lean

import Definitions.Def_Bdd_Collect
import Theorems.Thm_Collect_collect_spec
import Theorems.Thm_Collect_collect_terminal
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_not_isTerminal_of_root_eq_node
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
namespace Size
def size : OBdd n m → Nat := List.length ∘ Collect.collect
lemma isTerminal_iff_size_eq_zero {n m} {O : OBdd n m} : size O = 0 ↔ O.isTerminal := by
  constructor
  · intro h
    simp only [size, Function.comp_apply, List.length_eq_zero_iff] at h
    cases O_root_def : O.1.root with
    | terminal b => use b
    | node j =>
      have := Collect.collect_spec (j := j) (by rw [O_root_def]; exact Relation.ReflTransGen.refl)
      rw [h] at this
      contradiction
  · rintro ⟨b, hb⟩
    simp [size, Collect.collect_terminal hb]
def bool_of_size_eq_zero {n m} (O : OBdd n m) (h : size O = 0) : Bool :=
  match O_root_def : O.1.root with
  | .terminal b => b
  | .node _ => False.elim (not_isTerminal_of_root_eq_node O_root_def (isTerminal_iff_size_eq_zero.mp h))
end Size


