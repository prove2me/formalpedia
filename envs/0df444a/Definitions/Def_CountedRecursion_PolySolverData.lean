-- Prove2me | Definitions.Def_CountedRecursion_PolySolverData
-- name    : CountedRecursion_PolySolverData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:04:49.695757+00:00
-- url     : https://prove2.me/theorems/ed5d37a7-f63e-48cf-99fb-46dcde29a511
-- title:
--   Poly Solver Data
-- statement:
--   Definitions and structural lemmas for Poly Solver Data, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_ClauseBound_Alg_CertLevel
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]
section Ready
variable {s : α → Ready} (hs : PolyT s)
include hs
end Ready
end ExplicitCost


