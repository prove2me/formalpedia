-- Prove2me | Definitions.Def_WidthThree_Rates
-- name    : WidthThree_Rates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:28:52.000867+00:00
-- url     : https://prove2.me/theorems/c2b35dae-56e8-44f5-befa-48e8f7b27994
-- title:
--   Rates
-- statement:
--   Definitions and structural lemmas for Rates, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ToTuring_EndLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace WidthThree
open Turing
open scoped NNReal
end WidthThree


