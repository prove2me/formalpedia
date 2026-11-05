-- Prove2me | Definitions.Def_ClauseBound_Alg_Grid
-- name    : ClauseBound_Alg_Grid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:43:26.587978+00:00
-- url     : https://prove2.me/theorems/9161d6db-c497-4874-923b-233c0eb5c291
-- title:
--   Grid
-- statement:
--   Definitions and structural lemmas for Grid, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Grid.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_ClauseBound_Alg_GridPresents
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.Grid
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
end ClauseBound.Alg.Grid


