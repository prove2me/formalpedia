-- Prove2me | Definitions.Def_FromPrinted_SplitSat
-- name    : FromPrinted_SplitSat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:09:28.885271+00:00
-- url     : https://prove2.me/theorems/578eea52-aa2a-4c01-a19c-5c0240041184
-- title:
--   Split Sat
-- statement:
--   Definitions and structural lemmas for Split Sat, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_Printed_End
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
namespace FromPrinted.SplitSat
end FromPrinted.SplitSat
end


