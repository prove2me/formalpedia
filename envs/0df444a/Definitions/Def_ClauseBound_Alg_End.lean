-- Prove2me | Definitions.Def_ClauseBound_Alg_End
-- name    : ClauseBound_Alg_End
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:16:17.469196+00:00
-- url     : https://prove2.me/theorems/4c2300e8-9716-4110-93e8-0750ee4d195b
-- title:
--   End
-- statement:
--   Definitions and structural lemmas for End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
end ClauseBound.Alg.End


