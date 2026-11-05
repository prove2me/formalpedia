-- Prove2me | Definitions.Def_Paper_SecLevel_Grid
-- name    : Paper_SecLevel_Grid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:07:18.221077+00:00
-- url     : https://prove2.me/theorems/03828aeb-597b-4f13-8ad8-138ca693e50e
-- title:
--   Sec Level Grid
-- statement:
--   Definitions and structural lemmas for Sec Level Grid, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Grid.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_DefFactor
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Prog_GridDefs
set_option autoImplicit false
section
section
namespace Paper
open Finset Groundwork
variable {g lam : ℕ}
abbrev Rectangle (g : ℕ) : Type := Grid.Rect (Fin g) (Fin g)
def rectangles (g : ℕ) : Finset (Rectangle g) := Grid.Ω (Fin g) (Fin g)
abbrev Settings (g lam : ℕ) : Type := Grid.Half (Fin g) (Fin g) (Bits lam)
abbrev RowSetting (g lam : ℕ) : Type := Grid.RowSt (Fin g) (Fin g) (Bits lam)
section OnPath
open Groundwork.Grid Groundwork.Prog
end OnPath
end Paper


