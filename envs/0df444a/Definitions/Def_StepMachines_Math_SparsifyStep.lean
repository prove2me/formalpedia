-- Prove2me | Definitions.Def_StepMachines_Math_SparsifyStep
-- name    : StepMachines_Math_SparsifyStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:31:59.122204+00:00
-- url     : https://prove2.me/theorems/f49fbf9e-0de9-40f3-a624-56095cfaf731
-- title:
--   Sparsify Step
-- statement:
--   Definitions and structural lemmas for Sparsify Step, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyStep.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_SparsifyTree
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
namespace Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
@[expose] public def redL (s : List (Finset α)) : List (Finset α) :=
  s.filter fun C => ∀ D ∈ s, D ⊆ C → D = C
@[expose] public def NodeL (τ : ℕ) (φ s : List (Finset α)) (p q : ℕ) : Prop :=
  s.Nodup ∧ Node τ φ.toFinset s.toFinset p q
section Main
variable {τ n : ℕ} {lits : List α} {φ s : List (Finset α)} {p q : ℕ}
variable {U : Finset α}
end Main
end Groundwork.Sparsify


