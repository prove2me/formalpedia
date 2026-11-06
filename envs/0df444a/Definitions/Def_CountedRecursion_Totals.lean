-- Prove2me | Definitions.Def_CountedRecursion_Totals
-- name    : CountedRecursion_Totals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:18:27.593786+00:00
-- url     : https://prove2.me/theorems/5d625ccb-5d7e-4bad-a3b9-e19c5bf0c7b9
-- title:
--   Totals
-- statement:
--   Definitions and structural lemmas for Totals, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}
end ExplicitCost


