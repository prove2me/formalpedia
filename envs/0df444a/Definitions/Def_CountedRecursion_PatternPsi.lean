-- Prove2me | Definitions.Def_CountedRecursion_PatternPsi
-- name    : CountedRecursion_PatternPsi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:12:00.07987+00:00
-- url     : https://prove2.me/theorems/92d42822-6bc2-4791-a9f2-cc75e6698d01
-- title:
--   Pattern Psi
-- statement:
--   Definitions and structural lemmas for Pattern Psi, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


