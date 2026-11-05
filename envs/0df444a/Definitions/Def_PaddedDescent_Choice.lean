-- Prove2me | Definitions.Def_PaddedDescent_Choice
-- name    : PaddedDescent_Choice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:34:54.26452+00:00
-- url     : https://prove2.me/theorems/772564fa-1b17-4d2d-a727-12ab5b145a38
-- title:
--   Choice
-- statement:
--   Definitions and structural lemmas for Choice, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
section
section
@[expose] section
set_option exponentiation.threshold 1024
namespace PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
end PaddedDescent


