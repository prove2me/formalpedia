-- Prove2me | Definitions.Def_StepMachines_Prog_Range
-- name    : StepMachines_Prog_Range
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:40.972499+00:00
-- url     : https://prove2.me/theorems/70b489d9-43ff-465c-b929-de7589c71d36
-- title:
--   Range
-- statement:
--   Definitions and structural lemmas for Range, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
set_option autoImplicit false
section
namespace Groundwork.Stepped
open Finset
variable {α β γ : Type}
@[expose] public def rangeStart (N : α → ℕ) (a : α) : Option (α × ℕ) := if 0 < N a then some (a, 0) else none
@[expose] public def rangeNext (N : α → ℕ) (x : α × ℕ) : Option (α × ℕ) :=
  if x.2 + 1 < N x.1 then some (x.1, x.2 + 1) else none
@[expose] public def rangeG (g : γ → ℕ → β → γ) (c : γ) (x : α × ℕ) (b : β) : γ := g c x.2 b
@[expose] public def foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : Stepped (α × ℕ) β) (g : γ → ℕ → β → γ)
    (c₀ : α → γ) : Stepped α γ :=
  foldWhile (rangeStart N) (rangeNext N) M (rangeG g) c₀
@[expose] public def addG (c : ℤ) (_ : ℕ) (b : ℤ) : ℤ := c + b
@[expose] public def zeroC (_ : α) : ℤ := 0
@[expose] public def sumRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) ℤ) : Stepped α ℤ :=
  foldRange N M addG zeroC
@[expose] public def mulG (c : ℤ) (_ : ℕ) (b : ℤ) : ℤ := c * b
@[expose] public def oneC (_ : α) : ℤ := 1
@[expose] public def prodRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) ℤ) : Stepped α ℤ :=
  foldRange N M mulG oneC
@[expose] public def firstG (p : β → Bool) (c : Option ℕ) (y : ℕ) (b : β) : Option ℕ :=
  match c with | some i => some i | none => if p b then some y else none
@[expose] public def noneC (_ : α) : Option ℕ := none
@[expose] public def firstRange [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) :
    Stepped α (Option ℕ) :=
  foldRange N M (firstG p) noneC
end Groundwork.Stepped


