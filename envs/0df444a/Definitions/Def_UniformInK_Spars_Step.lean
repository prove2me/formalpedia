-- Prove2me | Definitions.Def_UniformInK_Spars_Step
-- name    : UniformInK_Spars_Step
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:36:20.410699+00:00
-- url     : https://prove2.me/theorems/44d3e548-7afd-44bb-bd9a-b54875ed6df0
-- title:
--   Step
-- statement:
--   Definitions and structural lemmas for Step, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK
namespace Step
variable {α : Type*} [DecidableEq α]
section StepLemma
variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}
end StepLemma
variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}
variable {τ p t : ℕ} {φ : Finset (Finset α)}
end Step
end UniformInK


