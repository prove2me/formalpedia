-- Prove2me | Definitions.Def_SparsificationLemma_Geo_S
-- name    : SparsificationLemma_Geo_S
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:28:41.336593+00:00
-- url     : https://prove2.me/theorems/afcaa511-91dc-48cf-b506-8773fe2b8c4a
-- title:
--   S
-- statement:
--   Definitions and structural lemmas for S, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/S.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK PaddedDescent
end SparsificationLemma.Geo


