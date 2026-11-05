-- Prove2me | Definitions.Def_ClauseBound_Grid_Size
-- name    : ClauseBound_Grid_Size
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:50.200137+00:00
-- url     : https://prove2.me/theorems/d6ca2d94-9c71-4e99-a156-214d36e25ed9
-- title:
--   Size
-- statement:
--   Definitions and structural lemmas for Size, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
end ClauseBound.Grid


