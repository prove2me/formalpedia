-- Prove2me | Definitions.Def_SparsificationLemma_Geo_Thr
-- name    : SparsificationLemma_Geo_Thr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:15.230193+00:00
-- url     : https://prove2.me/theorems/4220802b-55a9-4525-92e3-dcb24af61318
-- title:
--   Thr
-- statement:
--   Definitions and structural lemmas for Thr, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Thr.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Bound
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Geo
open Finset UniformInK
end SparsificationLemma.Geo


