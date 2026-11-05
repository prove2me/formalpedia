-- Prove2me | Definitions.Def_GeneralPieces_Num_TopDisplay
-- name    : GeneralPieces_Num_TopDisplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:25:57.207067+00:00
-- url     : https://prove2.me/theorems/78e39927-e366-41dd-a5d3-ce05f01aeac0
-- title:
--   Top Display
-- statement:
--   Definitions and structural lemmas for Top Display, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
set_option autoImplicit false
section
section
namespace GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
section
variable {K k m : ℕ}
end
def Atop (C₀ d : ℕ) : ℕ := 2 + (3 + 20 * d) * (2 * C₀ + 15) * (d ^ C₀ * (C₀.factorial * 2 ^ C₀))
end GeneralPieces.TopDisplay


