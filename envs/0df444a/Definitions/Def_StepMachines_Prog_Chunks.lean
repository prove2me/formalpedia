-- Prove2me | Definitions.Def_StepMachines_Prog_Chunks
-- name    : StepMachines_Prog_Chunks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:36.165713+00:00
-- url     : https://prove2.me/theorems/c5aa5356-43bd-4e24-9cbc-858dfac73810
-- title:
--   Chunks
-- statement:
--   Definitions and structural lemmas for Chunks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
namespace Groundwork
open Finset
@[expose] public def toWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, y => decide (y % 2 = 1) :: toWord ℓ (y / 2)
@[expose] public def ofWord : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * ofWord w
@[expose] public def words (ℓ : ℕ) : Finset (List Bool) := (range (2 ^ ℓ)).image (toWord ℓ)
@[expose] public def chunks : List ℕ → List Bool → List (List Bool)
  | [], _ => []
  | c :: cs, w => w.take c :: chunks cs (w.drop c)
section cut
variable {ι : Type*} [DecidableEq ι]
@[expose] public def cut (c : ι → ℕ) (d : List Bool) : List ι → List Bool → ι → List Bool
  | [], _ => fun _ => d
  | i :: e, w => Function.update (cut c d e (w.drop (c i))) i (w.take (c i))
@[expose] public def glue (e : List ι) (t : ι → List Bool) : List Bool := (e.map t).flatten
@[expose] public def block (ℓ j : ℕ) (w : List Bool) : List Bool := (w.drop (j * ℓ)).take ℓ
end cut
@[expose] public def tri (a b : ℕ) : ℕ := b * (b - 1) / 2 + a
end Groundwork


