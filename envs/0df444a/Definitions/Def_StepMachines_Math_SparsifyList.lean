-- Prove2me | Definitions.Def_StepMachines_Math_SparsifyList
-- name    : StepMachines_Math_SparsifyList
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:32:34.586796+00:00
-- url     : https://prove2.me/theorems/638c0915-62b3-49be-99ed-0e1d1d7fcb90
-- title:
--   Sparsify List
-- statement:
--   Definitions and structural lemmas for Sparsify List, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyList.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyStep
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
section
namespace Groundwork.Sparsify
open Finset
section Sim
variable {σ σ' : Type*} {step' : σ' → Option (σ' × σ')} {step : σ → Option (σ × σ)} {f : σ' → σ} {I : σ' → Prop}
end Sim
variable {α : Type*} [DecidableEq α]
@[expose] public def redLL (s : List (List α)) : List (List α) :=
  s.filter fun C => ∀ D ∈ s, (∀ a ∈ D, a ∈ C) → ∀ a ∈ C, a ∈ D
section Main
variable [Fintype α] {τ n : ℕ} {lits : List α} {φ : List (List α)}
end Main
end Groundwork.Sparsify


