-- Prove2me | Definitions.Def_CountedRecursion_RowWeightRun
-- name    : CountedRecursion_RowWeightRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:40:56.756181+00:00
-- url     : https://prove2.me/theorems/2401ba09-67a2-4829-89d9-1ac2b94082a1
-- title:
--   Row Weight Run
-- statement:
--   Definitions and structural lemmas for Row Weight Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
abbrev upOracle (D : PiecesCounted.Data) (g lam Lam : ℕ) (W : ℕ → List Bool → ℤ) : UpQuery → Option Ans := Sum.elim (answersOf (g * g) lam W) (piecesUpTo D Lam)
end ExplicitCost


