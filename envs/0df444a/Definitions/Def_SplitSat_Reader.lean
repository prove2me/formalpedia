-- Prove2me | Definitions.Def_SplitSat_Reader
-- name    : SplitSat_Reader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:48:05.579465+00:00
-- url     : https://prove2.me/theorems/84530567-7c44-45b2-abb5-c2496cae12cc
-- title:
--   Reader
-- statement:
--   Definitions and structural lemmas for Reader, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Reader.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Walk
import Definitions.Def_CountKSat_InOut
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
end SplitSat


