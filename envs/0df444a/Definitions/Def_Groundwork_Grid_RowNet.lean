-- Prove2me | Definitions.Def_Groundwork_Grid_RowNet
-- name    : Groundwork_Grid_RowNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:25:18.968702+00:00
-- url     : https://prove2.me/theorems/0cdcce5c-cca0-465d-bdef-9d40d34152d4
-- title:
--   Row Net
-- statement:
--   Definitions and structural lemmas for Row Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
end Groundwork.Grid


