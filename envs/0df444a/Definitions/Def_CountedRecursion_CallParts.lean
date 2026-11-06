-- Prove2me | Definitions.Def_CountedRecursion_CallParts
-- name    : CountedRecursion_CallParts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:13:22.36327+00:00
-- url     : https://prove2.me/theorems/2efe0198-bf5a-4fd3-8e70-82ee28f73bdc
-- title:
--   Call Parts
-- statement:
--   Definitions and structural lemmas for Call Parts, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
section Ready
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}
end Ready
end ExplicitCost


