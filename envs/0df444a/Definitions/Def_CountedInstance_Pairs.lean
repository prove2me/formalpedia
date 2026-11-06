-- Prove2me | Definitions.Def_CountedInstance_Pairs
-- name    : CountedInstance_Pairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:12:06.251187+00:00
-- url     : https://prove2.me/theorems/979212bd-f8be-4a18-8b04-1f3c05206266
-- title:
--   Pairs
-- statement:
--   Definitions and structural lemmas for Pairs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/CountedInstance/Pairs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedInstanceStatement
import Definitions.Def_CountedToPadded_GenLevels
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Num_Between
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace CountedInstance
open Groundwork
end CountedInstance


