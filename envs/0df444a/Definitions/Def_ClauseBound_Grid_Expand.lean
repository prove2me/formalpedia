-- Prove2me | Definitions.Def_ClauseBound_Grid_Expand
-- name    : ClauseBound_Grid_Expand
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:58.455579+00:00
-- url     : https://prove2.me/theorems/2e7757b3-3943-4c45-b8d3-3fee008d8f5b
-- title:
--   Expand
-- statement:
--   Definitions and structural lemmas for Expand, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
end ClauseBound.Grid


