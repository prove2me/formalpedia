-- Prove2me | Definitions.Def_FromPrinted_Verifier
-- name    : FromPrinted_Verifier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:17:51.429169+00:00
-- url     : https://prove2.me/theorems/b6a25565-157f-4e67-a32e-fb61a84baaac
-- title:
--   Verifier
-- statement:
--   Definitions and structural lemmas for Verifier, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Verifier.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
set_option autoImplicit false
section
section
@[expose] section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
namespace FromPrinted.Consequences
end FromPrinted.Consequences
end


