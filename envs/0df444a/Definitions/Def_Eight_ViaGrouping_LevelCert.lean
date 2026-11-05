-- Prove2me | Definitions.Def_Eight_ViaGrouping_LevelCert
-- name    : Eight_ViaGrouping_LevelCert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:12:36.19257+00:00
-- url     : https://prove2.me/theorems/57a24635-2c2b-4678-bdf8-23f7128785cd
-- title:
--   Level Cert
-- statement:
--   Definitions and structural lemmas for Level Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelCert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_Level_Cert
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped Eight.SecNetworks Eight.Level
end Eight.ViaGrouping


