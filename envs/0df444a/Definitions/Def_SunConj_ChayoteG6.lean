-- Prove2me | Definitions.Def_SunConj_ChayoteG6
-- name    : SunConj_ChayoteG6
-- status  : Definition
-- author  : @williambc
-- created : 2026-10-03T22:51:16.11913+00:00
-- url     : https://prove2.me/theorems/7ecc1e50-28bc-4ec0-b365-4110dd69e7ae
-- title:
--   SunConj_ChayoteG6: shared definitions
-- statement:
--   Shared Lean definitions `SunConj_ChayoteG6` used by the statements of this project.
--
--   - `chayoteB6`: Gamma part of Sun's `g` of Conjecture 5.6, as a function of a complex variable;
--   `4096 ^ z` is written `exp (z * log 4096)`.
--   - `chayoteP6`: The polynomial factor of Sun's `g` of Conjecture 5.6.
--   - `chayoteG6`: Complex extension of `g6`.
--   - `chayoteS6`: The shifted series `S(z) = ∑_{k ≥ 0} g(k + z)`.
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/162c03a7baa1a4605a86d0ac78a1ec3d39db64d5/math-problems/lean/Definitions/Def_SunConj_ChayoteG6.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

namespace SunConj

/-- Gamma part of Sun's `g` of Conjecture 5.6, as a function of a complex variable;
`4096 ^ z` is written `exp (z * log 4096)`. -/
def chayoteB6 (z : ℂ) : ℂ :=
  Complex.Gamma (4 * z + 1) ^ 2 /
    (Complex.exp (z * (Real.log 4096 : ℂ)) * Complex.Gamma (z + 1) ^ 2 * Complex.Gamma (2 * z + 1) ^ 3)

/-- The polynomial factor of Sun's `g` of Conjecture 5.6. -/
def chayoteP6 (z : ℂ) : ℂ := 48 * z ^ 2 + 32 * z + 3

/-- Complex extension of `g6`. -/
def chayoteG6 (z : ℂ) : ℂ := chayoteP6 z * chayoteB6 z / (2 * z + 1)

/-- The shifted series `S(z) = ∑_{k ≥ 0} g(k + z)`. -/
def chayoteS6 (z : ℂ) : ℂ := ∑' k : ℕ, chayoteG6 ((k : ℂ) + z)

end SunConj


