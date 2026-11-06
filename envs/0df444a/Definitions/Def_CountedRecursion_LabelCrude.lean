-- Prove2me | Definitions.Def_CountedRecursion_LabelCrude
-- name    : CountedRecursion_LabelCrude
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:26:19.469425+00:00
-- url     : https://prove2.me/theorems/9a60688c-1d5d-4af0-a946-52da656cb513
-- title:
--   Label Crude
-- statement:
--   Definitions and structural lemmas for Label Crude, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LabelCrude.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


