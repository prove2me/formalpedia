-- Prove2me | Definitions.Def_OccurM_Wrapper
-- name    : OccurM_Wrapper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:57:52.070005+00:00
-- url     : https://prove2.me/theorems/953dd665-fe10-4d3d-bc08-53b68d949b32
-- title:
--   Wrapper
-- statement:
--   Definitions and structural lemmas for Wrapper, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
set_option autoImplicit false
section
section
@[expose] section
namespace OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)
end OccurM


