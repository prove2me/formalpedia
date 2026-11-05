-- Prove2me | Definitions.Def_MainRoute_General
-- name    : MainRoute_General
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:33:19.448431+00:00
-- url     : https://prove2.me/theorems/fef8054d-7943-416d-a213-b5e04bda322e
-- title:
--   General
-- statement:
--   Definitions and structural lemmas for General, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/General.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_GeneralDefs
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Main
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_GeneralPieces_ThmRunningTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace MainRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)
end MainRoute


