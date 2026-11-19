-- Prove2me | Definitions.Def_DeletionCode_ComponentFibers
-- name    : DeletionCode_ComponentFibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:11:22.972884+00:00
-- url     : https://prove2.me/theorems/6b11c3d9-8029-4f27-8ee1-17440be13e4e
-- title:
--   Component Fibers
-- statement:
--   Definitions and structural lemmas for Component Fibers, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentFibers.lean

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.ComponentFibers
open scoped BigOperators
def SingletonFiber {A C : Type*} (f : A → C) (c : C) : Prop :=
  ∃ a, f a = c ∧ ∀ b, f b = c → b = a
noncomputable instance singletonFibersFintype {A C : Type*} [Fintype C]
    (f : A → C) : Fintype {c : C // SingletonFiber f c} := by
  classical
  exact Fintype.ofFinite _
noncomputable def fiber {A C : Type*} [Fintype A] (f : A → C) (c : C) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => f a = c)
end DeletionCode.ComponentFibers


