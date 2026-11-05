-- Prove2me | Definitions.Def_Printed_LevelPoly
-- name    : Printed_LevelPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:42:52.313332+00:00
-- url     : https://prove2.me/theorems/7e3638ad-453b-4dd8-9b35-ea456ce7392b
-- title:
--   Level Poly
-- statement:
--   Definitions and structural lemmas for Level Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
end Printed


