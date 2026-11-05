-- Prove2me | Definitions.Def_RecursionToBound_Cert_Numbers
-- name    : RecursionToBound_Cert_Numbers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:46:03.760705+00:00
-- url     : https://prove2.me/theorems/d7a1fb7b-f08e-48a0-974c-b3b62c0a6817
-- title:
--   Numbers
-- statement:
--   Definitions and structural lemmas for Numbers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Numbers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
set_option autoImplicit false
section
section
@[expose] section
namespace RecursionToBound
open Finset SparsificationLemma
@[expose] def sqPred (k : ℕ) : ℕ := (k - 1) * (k - 1) + (1 - k)
@[expose] def ceilDiv (m p : ℕ) : ℕ := (m + p - 1) / p
@[expose] def logN (k : ℕ) (r : ℕ × ℕ) : ℕ := Nat.clog 2 (ceilDiv (32 * sqPred k * r.2) (min r.1 r.2))
@[expose] def alphaN (k : ℕ) (r : ℕ × ℕ) : ℕ := ceilDiv (2 * sqPred k * r.2 * logN k r) (min r.1 r.2)
end RecursionToBound


