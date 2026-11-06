-- Prove2me | Definitions.Def_CountedRecursion_CaseTwo
-- name    : CountedRecursion_CaseTwo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:18:55.984743+00:00
-- url     : https://prove2.me/theorems/3374d221-c621-49e9-81d7-8de1bdcffc0c
-- title:
--   Case Two
-- statement:
--   Definitions and structural lemmas for Case Two, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


