-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_ArithOL
-- name    : ClauseBound_ParityChecks_ArithOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:07:50.752806+00:00
-- url     : https://prove2.me/theorems/f34cc53b-b66d-460e-a0f4-3c5ee13a6923
-- title:
--   Arith OL
-- statement:
--   Definitions and structural lemmas for Arith OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
section nat
variable {k K n s C₀ : ℕ}
def GO (C₀ : ℕ) : ℕ := 2660 * (1 + 17 * C₀)
end nat
def ccO (k C₀ : ℕ) : ℕ := 3 + 3 * GO C₀ + (55 + 354 * k + GO C₀) + GO C₀ + 54 + 1 + C₀ * (85 * C₀ + 16) + 27 * (4 + 17 * C₀) + (17 + 51 * C₀)
def cO (k C C₀ : ℕ) : ℕ := Nat.size (a0 k C) + 4 * cK k * C * C₀
end ClauseBound.ParityChecks.ArithOL


