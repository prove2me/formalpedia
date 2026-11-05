-- Prove2me | Definitions.Def_PaddedDescent_F_ArithInv
-- name    : PaddedDescent_F_ArithInv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:44:52.979568+00:00
-- url     : https://prove2.me/theorems/b4a7a5be-7b70-45e2-8ac5-2a66c1ed58f0
-- title:
--   Arith Inv
-- statement:
--   Definitions and structural lemmas for Arith Inv, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
namespace PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
structure Inv (t X Z Qm Wm L j lam B cnt : ℕ) : Prop where
  geo : 8963 ^ j * (Kseq j ^ 2 * lam) ≤ 10000 ^ j * X + 8963 ^ j * Z
  crude : Kseq j ^ 2 * lam ≤ Qm
  bits : B * Kseq j ^ 3 + 16 * Qm * Kseq j ^ 3 ≤ Wm
  count : cnt * 2 ^ (L * (2 * Kseq j ^ 2)) ≤ 2 ^ (L * (2 * Kseq t ^ 2))
variable {t X Z Qm Wm L j lam B cnt : ℕ}
end PaddedDescent.F.Arith


