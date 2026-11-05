-- Prove2me | Definitions.Def_StepMachines_Prog_Decode
-- name    : StepMachines_Prog_Decode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:03.203653+00:00
-- url     : https://prove2.me/theorems/d4ecf7fd-9479-4c1d-94dc-db18c6955028
-- title:
--   Decode
-- statement:
--   Definitions and structural lemmas for Decode, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Decode.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Data.Nat.Size
import Definitions.Def_StepMachines_Math_Formula
set_option autoImplicit false
section
namespace Groundwork.Decode
open Sat3
public abbrev NCNF : Type := List (List (ℕ × Bool))
@[expose] public def width (n : ℕ) : ℕ := if n = 0 then 1 else Nat.size (2 * n)
@[expose] public def slotDec (v : ℕ) : Option (ℕ × Bool) :=
  if v = 0 then none else some ((v - 1) / 2, decide ((v - 1) % 2 = 1))
@[expose] public def clauseDec (w : ℕ) (b : List Bool) : List (ℕ × Bool) :=
  [0, 1, 2].filterMap fun j => slotDec (ofWord (block w j b))
@[expose] public def dec (x : List Bool) : ℕ × NCNF :=
  let n := (x.takeWhile id).length
  let body := (x.dropWhile id).tail
  let w := width n
  (n, ((List.range body.length).take (body.length / (3 * w))).map fun c => clauseDec w (block (3 * w) c body))
@[expose] public def toN {n : ℕ} (φ : CNF n) : NCNF := φ.map fun C => C.map fun l => (l.1.val, l.2)
@[expose] public def SatN (ψ : NCNF) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2
def blk (n : ℕ) (C : List (Lit n)) : List Bool :=
  (List.range 3).flatMap fun j => (List.range ((Nat.log2 (2 * n) + 1))).map (slot C[j]?).testBit
end Groundwork.Decode


