-- Prove2me | Definitions.Def_CountedRecursion_PolyProcedure
-- name    : CountedRecursion_PolyProcedure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:40:47.588795+00:00
-- url     : https://prove2.me/theorems/cac1c793-6eb6-4ac0-bfe0-c95ad4b27c8d
-- title:
--   Poly Procedure
-- statement:
--   Definitions and structural lemmas for Poly Procedure, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyProcedure.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_ExplicitCost_Poly
import Definitions.Def_Printed_HandOver
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
end ExplicitCost


