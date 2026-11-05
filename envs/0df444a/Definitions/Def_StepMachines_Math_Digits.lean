-- Prove2me | Definitions.Def_StepMachines_Math_Digits
-- name    : StepMachines_Math_Digits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:07.916453+00:00
-- url     : https://prove2.me/theorems/e604502e-9463-4393-93b3-7e65800d1935
-- title:
--   Digits
-- statement:
--   Definitions and structural lemmas for Digits, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
def c2 (g : ℕ) : ℕ := g * (g - 1) / 2
def rectIx (g : ℕ) (tr : Bool) (p κ : ℕ) : ℕ := if tr = true then κ * c2 g + p else p * c2 g + κ
def ixOf (g : ℕ) (ω : Rect (Fin g) (Fin g)) : ℕ := tri ω.1.1 ω.1.2 * c2 g + tri ω.2.1 ω.2.2
def patOf (g n y : ℕ) : Rect (Fin g) (Fin g) → ℕ :=
  fun ω => if ω ∈ Ω (Fin g) (Fin g) then digit n y (ixOf g ω) else 0
end Groundwork.Grid


