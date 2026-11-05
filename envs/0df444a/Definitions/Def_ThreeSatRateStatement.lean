-- Prove2me | Definitions.Def_ThreeSatRateStatement
-- name    : ThreeSatRateStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:49.545455+00:00
-- url     : https://prove2.me/theorems/29493f6f-5a0e-48dc-9415-245d549b653f
-- title:
--   Three Sat Rate Statement
-- statement:
--   Definitions and structural lemmas for Three Sat Rate Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/ThreeSatRateStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit false
section
section
namespace Sat3
open Turing
open scoped NNReal
noncomputable def rateBound (C : ℕ) (c : ℝ) (n : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n / (Real.logb 2 ((n : ℝ) + 2)) ^ c)⌋₊
def InRateTM (c : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧ DecidesTM M (rateBound C c)
def SubexpTM : Prop :=
  ∃ M : TM2ComputableAux Bool Bool, (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ δ : ℝ≥0, 0 < δ → ∃ A : ℕ, DecidesTM M fun n => ⌊(A : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
end Sat3


