-- Prove2me | Definitions.Def_ClauseBound_TopN_Arith
-- name    : ClauseBound_TopN_Arith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:13.930139+00:00
-- url     : https://prove2.me/theorems/74f139c5-076c-4675-82d5-42970ee06159
-- title:
--   Arith
-- statement:
--   Definitions and structural lemmas for Arith, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
set_option autoImplicit false
section
namespace ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
section nat
variable {k K n s : ℕ}
end nat
section lower
variable {k K n s C₀ : ℕ}
def Wof (k K s : ℕ) : ℕ := (betaN k s + 3) ^ 2 * 2 ^ betaN k s * K.size
end lower
end ClauseBound.TopN.Arith


