-- Prove2me | Definitions.Def_WidthK_Decode
-- name    : WidthK_Decode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:05.830254+00:00
-- url     : https://prove2.me/theorems/12fdaeb8-9d6e-4969-bd3d-df78a84dc8b6
-- title:
--   Decode
-- statement:
--   Definitions and structural lemmas for Decode, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Decode.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
set_option autoImplicit false
section
namespace Groundwork.DecodeK
open Sat3 (Lit CNF Satisfiable slot)
open SatK
open Groundwork.Decode
@[expose] public def clauseDec (k w : ℕ) (b : List Bool) : List (ℕ × Bool) :=
  (List.range k).filterMap fun j => slotDec (ofWord (block w j b))
@[expose] public def decK (k : ℕ) (x : List Bool) : ℕ × NCNF :=
  let n := (x.takeWhile id).length
  let body := (x.dropWhile id).tail
  let w := width n
  (n, ((List.range body.length).take (body.length / (k * w))).map fun c => clauseDec k w (block (k * w) c body))
def blk (k n : ℕ) (C : List (Lit n)) : List Bool :=
  (List.range k).flatMap fun j => (List.range ((Nat.log2 (2 * n) + 1))).map (slot C[j]?).testBit
end Groundwork.DecodeK


