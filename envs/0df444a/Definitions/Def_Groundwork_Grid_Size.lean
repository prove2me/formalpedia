-- Prove2me | Definitions.Def_Groundwork_Grid_Size
-- name    : Groundwork_Grid_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:03.592049+00:00
-- url     : https://prove2.me/theorems/6ad7a587-3a52-4a98-8deb-00956bf6a310
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
end Groundwork.Grid


