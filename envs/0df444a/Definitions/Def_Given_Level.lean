-- Prove2me | Definitions.Def_Given_Level
-- name    : Given_Level
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:28:37.852188+00:00
-- url     : https://prove2.me/theorems/b137f5e4-80d9-4e66-bea7-ce9fc96efc64
-- title:
--   Level
-- statement:
--   Definitions and structural lemmas for Level, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
end Given


