-- Prove2me | Definitions.Def_PaddedDescent_F_ArithLevel
-- name    : PaddedDescent_F_ArithLevel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:06:40.117498+00:00
-- url     : https://prove2.me/theorems/1862e2d4-dcf3-40bf-9c4b-02bd7ccda11d
-- title:
--   Arith Level
-- statement:
--   Definitions and structural lemmas for Arith Level, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
namespace PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
end PaddedDescent.F.Arith


