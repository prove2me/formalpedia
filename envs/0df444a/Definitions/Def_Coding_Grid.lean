-- Prove2me | Definitions.Def_Coding_Grid
-- name    : Coding_Grid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:02:06.233464+00:00
-- url     : https://prove2.me/theorems/f145ba62-3ec7-4729-9925-8c1edc2d99e6
-- title:
--   Grid
-- statement:
--   Definitions and structural lemmas for Grid, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_GridDefs
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_Eight_SecLevel_GridWords
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}
@[expose] def pieceRow (g : ℕ) (tr : Bool) (lam a : ℕ) (z : List Bool) (x u : ℕ) : List Bool :=
  if u = nodeG g tr a x then List.replicate lam false else block lam (if u < nodeG g tr a x then u else u - 1) (block ((g * g - 1) * lam) x z)
end Coding


