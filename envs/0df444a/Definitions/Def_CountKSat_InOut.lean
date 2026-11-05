-- Prove2me | Definitions.Def_CountKSat_InOut
-- name    : CountKSat_InOut
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:44:33.314667+00:00
-- url     : https://prove2.me/theorems/58799590-baa3-4bf5-99c2-7f8962a333f8
-- title:
--   In Out
-- statement:
--   Definitions and structural lemmas for In Out, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/InOut.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_WidthK_Poly_Decode
set_option autoImplicit false
section
namespace CountKSat
open Groundwork Groundwork.Prog Groundwork.Decode Groundwork.DecodeK
open SatK (enc numSat)
end CountKSat


