-- Prove2me | Definitions.Def_ToTuring_Enc
-- name    : ToTuring_Enc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:22:51.530192+00:00
-- url     : https://prove2.me/theorems/16268199-2d02-437c-9c71-e464bef046d9
-- title:
--   Enc
-- statement:
--   Definitions and structural lemmas for Enc, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Enc.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Tree
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
set_option autoImplicit false
section
section
namespace Groundwork
open TM
class Enc (α : Type) where
  /-- the tree of a value -/
  toV : α → V
open Enc
instance : Enc Unit := ⟨fun _ => .nil⟩
instance : Enc Bool := ⟨.bit⟩
instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun p => .cons (toV p.1) (toV p.2)⟩
instance {α : Type} [Enc α] : Enc (List α) := ⟨fun l => l.foldr (fun x v => .cons (toV x) v) .nil⟩
instance {α : Type} [Enc α] : Enc (Option α) := ⟨fun o => o.elim .nil fun x => .cons (toV x) .nil⟩
instance {α β : Type} [Enc α] [Enc β] : Enc (α ⊕ β) :=
  ⟨fun s => s.elim (fun x => .cons (.bit false) (toV x)) fun y => .cons (.bit true) (toV y)⟩
instance : Enc ℕ := ⟨fun n => toV (Nat.bits n)⟩
instance : Enc ℤ := ⟨fun z => toV (decide (z < 0), z.natAbs)⟩
def wd {α : Type} [Enc α] (x : α) : List Sym := code (toV x)
def len {α : Type} [Enc α] (x : α) : ℕ := (wd x).length
class Carried (α : Type) [Enc α] [HasSize α] : Prop where
  le : ∀ x : α, len x + 2 ≤ 7 * size x
end Groundwork


