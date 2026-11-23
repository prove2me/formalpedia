-- Prove2me | Definitions.Def_Bdd_Nary
-- name    : Bdd_Nary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:37:35.036744+00:00
-- url     : https://prove2.me/theorems/eb5b7f86-86f5-4823-8f0a-a86a17435e37
-- title:
--   Nary
-- statement:
--   Definitions and structural lemmas for Nary, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean

import Mathlib.Data.Vector.Basic
set_option autoImplicit true
namespace Nary
abbrev Func n α β := Vector α n → β
@[simp]
def IndependentOf (f : Func n α β) (i : Fin n) := ∀ a v, f v = f (Vector.set v i a)
@[simp]
def DependsOn (f : Func n α β) (i : Fin n) := ¬ IndependentOf f i
def Dependency (f : Func n α β) := { i // DependsOn f i }
@[simp]
def restrict (f : Func n α β) : α → Fin n → Func n α β := fun a i I ↦ f (I.set i a)
end Nary


