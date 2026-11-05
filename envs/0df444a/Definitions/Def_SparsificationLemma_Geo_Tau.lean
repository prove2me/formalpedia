-- Prove2me | Definitions.Def_SparsificationLemma_Geo_Tau
-- name    : SparsificationLemma_Geo_Tau
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:25:37.259854+00:00
-- url     : https://prove2.me/theorems/b48218df-15f2-41c0-b8b2-6eef4d829f86
-- title:
--   Tau
-- statement:
--   Definitions and structural lemmas for Tau, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Tau.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK
end SparsificationLemma.Geo


