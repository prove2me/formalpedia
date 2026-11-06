-- Prove2me | Definitions.Def_MainRoute_EveryMachine
-- name    : MainRoute_EveryMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:02:59.891409+00:00
-- url     : https://prove2.me/theorems/81ce63be-9eeb-41ab-9b39-de140d33f602
-- title:
--   Every Machine
-- statement:
--   Definitions and structural lemmas for Every Machine, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/EveryMachine.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_Defs
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_VariableBound_Paper_Arith
set_option autoImplicit false
section
section
@[expose] section
namespace MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
end MainRoute


