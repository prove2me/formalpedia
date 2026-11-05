-- Prove2me | Definitions.Def_GeneralPieces_Rec_Seq
-- name    : GeneralPieces_Rec_Seq
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:44:53.82464+00:00
-- url     : https://prove2.me/theorems/a2d0b7b1-4064-4fb9-9450-d2d3c51ffeeb
-- title:
--   Seq
-- statement:
--   Definitions and structural lemmas for Seq, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen
end GeneralPieces


