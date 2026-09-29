-- Prove2me | Definitions.Def_FCP_CatalanConstant
-- name    : FCP_CatalanConstant
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:07:19.772777+00:00
-- url     : https://prove2.me/theorems/c85bb306-aa23-43c0-9d60-afbd23b11b07
-- title:
--   Catalan's constant $G = \sum_{n \ge 0} (-1)^n/(2n+1)^2$
-- statement:
--   Catalan's constant is the sum of the alternating series
--   $$G = \sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2} = 0.915965\ldots,$$
--   defined here as the real infinite sum of that series. Whether $G$ is irrational is one of the open problems in this mission.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Irrational.lean); https://en.wikipedia.org/wiki/Catalan%27s_constant

import Mathlib

namespace FCP.Constants

/-- Catalan's constant `G = ∑_{n ≥ 0} (-1)^n / (2n + 1)^2 ≈ 0.915965…`. -/
noncomputable def catalanConstant : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1) ^ 2

end FCP.Constants


