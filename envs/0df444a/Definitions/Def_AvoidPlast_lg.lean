-- Prove2me | Definitions.Def_AvoidPlast_lg
-- name    : AvoidPlast_lg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:02.35843+00:00
-- url     : https://prove2.me/theorems/c591b281-6fe9-4099-b8d9-ced67c837a32
-- title:
--   The logarithm $\log_2(n+2)$
-- statement:
--   The real number $\log_2(n+2)$, used in every log and polylog bound. It is at least $1$ for every $n$, so the bounds are meaningful at $n=0$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 1.2, p.3; Section 4, p.17

import Mathlib

namespace AvoidPlast

/-- The logarithm `log₂(n + 2)` used in every log and polylog bound (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §1.2, p.3 and §4,
p.17). It is at least `1` for every `n`, so the bounds are meaningful at `n = 0`. -/
noncomputable def lg (n : ℕ) : ℝ := Real.logb 2 ((n : ℝ) + 2)

end AvoidPlast


