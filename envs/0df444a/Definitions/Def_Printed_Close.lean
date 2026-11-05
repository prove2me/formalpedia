-- Prove2me | Definitions.Def_Printed_Close
-- name    : Printed_Close
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:38:32.321623+00:00
-- url     : https://prove2.me/theorems/d0060a8b-8077-425b-b3f4-9cf2c3462e21
-- title:
--   Close
-- statement:
--   Definitions and structural lemmas for Close, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Comb
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
variable {Q A C : Type}
end Printed


