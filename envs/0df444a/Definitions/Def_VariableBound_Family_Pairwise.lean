-- Prove2me | Definitions.Def_VariableBound_Family_Pairwise
-- name    : VariableBound_Family_Pairwise
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:30.635732+00:00
-- url     : https://prove2.me/theorems/1890a2af-6e62-406d-9d10-e30b050de49a
-- title:
--   Pairwise
-- statement:
--   Definitions and structural lemmas for Pairwise, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
section
section
namespace VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
def H (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (p : F × F) (E : Fin m) : Prop :=
  ∀ i : Fin s, i.val < a - 1 → bits (p.1 * ϑ E + p.2) i = 0
instance (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (p : F × F) (E : Fin m) : Decidable (H bits ϑ a p E) := by
  unfold H; infer_instance
def Z (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (a : ℕ) : Finset F := univ.filter fun x => ∀ i : Fin s, i.val < a - 1 → bits x i = 0
def Y (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (V : Finset (Fin m)) (p : F × F) : ℕ := #{E ∈ V | H bits ϑ a p E}
end VariableBound.Pairwise


