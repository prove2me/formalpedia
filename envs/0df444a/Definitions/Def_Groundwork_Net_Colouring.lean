-- Prove2me | Definitions.Def_Groundwork_Net_Colouring
-- name    : Groundwork_Net_Colouring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:19.373353+00:00
-- url     : https://prove2.me/theorems/ee7bb08b-1c3b-4617-a2ad-1031c4777842
-- title:
--   Colouring
-- statement:
--   Definitions and structural lemmas for Colouring, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Colouring.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
set_option autoImplicit false
section
open Finset
namespace Groundwork.Colouring
section core
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => (Fintype.card κ ^ Fintype.card ι)
def Zs (γ : κ) (χ : ι → κ) : ℕ := ∑ a : ι, if χ a = γ then 1 else 0
variable (c : ι → ι → ℕ)
def Ys (γ γ' : κ) (χ : ι → κ) : ℕ :=
  ∑ p : ι × ι, if χ p.1 = γ ∧ χ p.2 = γ' then c p.1 p.2 else 0
def Us : ℕ := ∑ p : ι × ι, c p.1 p.2
def meet (p q : ι × ι) : ℕ :=
  (if q.1 = p.1 then 1 else 0) + (if q.1 = p.2 then 1 else 0) +
  (if q.2 = p.1 then 1 else 0) + (if q.2 = p.2 then 1 else 0)
end core
@[expose] public def beta (K g U P : ℕ) : ℕ := max 1 ((K * U + g * P) / K ^ 3)
end Groundwork.Colouring


