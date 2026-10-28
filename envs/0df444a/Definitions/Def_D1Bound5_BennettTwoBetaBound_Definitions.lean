-- Prove2me | Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
-- name    : D1Bound5_BennettTwoBetaBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:40:28.290126+00:00
-- url     : https://prove2.me/theorems/918e57c7-9ef2-497d-800b-bee95ac2896d
-- title:
--   Bennett Two Beta Bound
-- statement:
--   The exact normalized beta factor in the two-anchor residual estimate. The named objects in this bundle include `bennettTwoBetaFactor`.
-- source:
--   D1Bound5/BennettTwoBetaBound.lean, lines 11-15, SHA-256 6be0ec4b4373f2704cbfdc6beb52a3796d8063f1c67fa2c91242af5752323182. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The exact normalized beta factor in the two-anchor residual estimate. -/
noncomputable def bennettTwoBetaFactor (k : ℕ) : ℝ :=
  (27 / 4 : ℝ) ^ k * Real.Gamma ((k : ℝ) + 3 / 2) *
    Real.Gamma (2 * (k : ℝ) - 1 / 2) /
      (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))



















end D1Bound5
end


