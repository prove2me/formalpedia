-- Prove2me | Definitions.Def_PaddedDescent_Col_Colouring
-- name    : PaddedDescent_Col_Colouring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:22:51.438675+00:00
-- url     : https://prove2.me/theorems/24139d5f-9295-4e6b-bff0-f92e2c08ffd8
-- title:
--   Colouring
-- statement:
--   Definitions and structural lemmas for Colouring, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
set_option autoImplicit false
section
section
@[expose] section
open Finset
namespace PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
noncomputable def Wt (x : ι → ℝ) (γ : κ) (χ : ι → κ) : ℝ := ∑ b, if χ b = γ then x b else 0
end PaddedDescent.Col


