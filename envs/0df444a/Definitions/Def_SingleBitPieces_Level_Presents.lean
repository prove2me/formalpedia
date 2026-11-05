-- Prove2me | Definitions.Def_SingleBitPieces_Level_Presents
-- name    : SingleBitPieces_Level_Presents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:48:48.611138+00:00
-- url     : https://prove2.me/theorems/f7347261-9211-4883-bfbc-75c92cd4f0fb
-- title:
--   Presents
-- statement:
--   Definitions and structural lemmas for Presents, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_ClauseBound_Alg_Grid
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
namespace Presents
end Presents
open Presents
end SingleBitPieces.Level


