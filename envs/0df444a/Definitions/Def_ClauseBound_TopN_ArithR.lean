-- Prove2me | Definitions.Def_ClauseBound_TopN_ArithR
-- name    : ClauseBound_TopN_ArithR
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:37:06.318324+00:00
-- url     : https://prove2.me/theorems/f13aac2f-797f-44e5-a94c-330c457dc914
-- title:
--   Arith R
-- statement:
--   Definitions and structural lemmas for Arith R, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/ArithR.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
def cK (k : ℕ) : ℕ := 2 ^ (k + 1) + 1
def qE (k C C₀ : ℕ) : ℕ := 12 * cK k * C * C₀ + C₀ + 1
def a0 (k C : ℕ) : ℕ := 2 ^ (17 * cK k + k + 3) * 2 ^ (4 * cK k * C)
def A1 (k C C₀ : ℕ) : ℕ := 2 * a0 k C ^ 3 * ((qE k C C₀).factorial * 2 ^ qE k C C₀)
def ckN (k : ℕ) : ℕ := 17 * (2 ^ (k + 1) + 1) + k + 6
end ClauseBound.TopN.Arith


