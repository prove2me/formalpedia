-- Prove2me | Definitions.Def_Sendov_Common_Sinh
-- name    : Sendov_Common_Sinh
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:52:49.710699+00:00
-- url     : https://prove2.me/theorems/9347c796-f538-5607-83a5-0326fd08185f
-- title:
--   Sinh
-- statement:
--   Definitions and structural lemmas for Sinh, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Sinh.lean

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
set_option autoImplicit false
namespace Sendov
open Real Set Filter
noncomputable def Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) : ℝ :=
  exp (2 * y) * (u₃ * y ^ 3 + u₂ * y ^ 2 + u₁ * y + u₀)
    - exp y * (v₄ * y ^ 4 + v₃ * y ^ 3 + v₂ * y ^ 2 + v₁ * y + v₀)
    - (w₃ * y ^ 3 + w₂ * y ^ 2 + w₁ * y + w₀)
end Sendov


