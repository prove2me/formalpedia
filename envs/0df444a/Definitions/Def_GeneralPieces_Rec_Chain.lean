-- Prove2me | Definitions.Def_GeneralPieces_Rec_Chain
-- name    : GeneralPieces_Rec_Chain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:40:31.042149+00:00
-- url     : https://prove2.me/theorems/f832406b-7d2d-463e-933b-5228a6e47b12
-- title:
--   Chain
-- statement:
--   Definitions and structural lemmas for Chain, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}
end GeneralPieces.Chain


