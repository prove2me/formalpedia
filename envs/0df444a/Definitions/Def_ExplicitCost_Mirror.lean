-- Prove2me | Definitions.Def_ExplicitCost_Mirror
-- name    : ExplicitCost_Mirror
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:12:42.548207+00:00
-- url     : https://prove2.me/theorems/76955adc-1b92-4a37-b5ec-f9a12bf40aa0
-- title:
--   Mirror
-- statement:
--   Definitions and structural lemmas for Mirror, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
set_option autoImplicit false
section
section
namespace ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
structure Follows (M : QueryMachine Q A α β) (M' : QueryMachine Q A α' β) (w : α → α') (d : ℕ) (φ : M.σ → M'.σ) : Prop where
  init : ∀ a, M'.init (w a) = φ (M.init a)
  out : ∀ s, M'.out (φ s) = M.out s
  ask : ∀ s, M'.ask (φ s) = M.ask s
  step : ∀ s, M'.step (φ s) = φ (M.step s)
  resume : ∀ s v, M'.resume (φ s) v = φ (M.resume s v)
  size : ∀ s, size (φ s) ≤ size s + d
def Mirrors (M : QueryMachine Q A α β) (M' : QueryMachine Q A α' β) (w : α → α') (d : ℕ) : Prop := ∃ φ : M.σ → M'.σ, Follows M M' w d φ
end ExplicitCost


