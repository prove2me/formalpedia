-- Prove2me | Definitions.Def_CountedRecursion_Expansion
-- name    : CountedRecursion_Expansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:19:01.284191+00:00
-- url     : https://prove2.me/theorems/012fa5aa-0ba6-4937-b649-e398b4df7a2e
-- title:
--   Expansion
-- statement:
--   Definitions and structural lemmas for Expansion, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Expansion.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


