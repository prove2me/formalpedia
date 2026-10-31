-- Prove2me | Definitions.Def_DeltaSLearning_confSize
-- name    : DeltaSLearning_confSize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:10:12.487879+00:00
-- url     : https://prove2.me/theorems/6c5b2c1a-52ed-4a74-99da-de333cd6fca5
-- title:
--   Confidence sizes $\Delta^n=2\theta\log(8N^2)/\sqrt n$
-- statement:
--   Theorem 3's confidence sizes for a horizon of $N$ epochs, $\Delta^n := 2\theta\log(8N^2)/\sqrt n$ for $n\ge1$.
--
--   **Formalization Note** For $N\ge1$ the logarithm is positive.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3, p.17

import Mathlib
import Definitions.Def_DeltaSLearning_theta

namespace DeltaSLearning

/-- Theorem 3's confidence sizes `Δⁿ = 2θ log(8N²) / √n` for a horizon of `N` epochs.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3,
p.17.

**Formalization Note** Indexed by the 1-based epoch `n`; the value at `n = 0` is unused. For
`N ≥ 1`, `8N² > 1`, so the logarithm is positive. -/
noncomputable def confSize (cp : Params) (N n : ℕ) : ℝ :=
  2 * theta cp * Real.log (8 * (N : ℝ) ^ 2) / Real.sqrt n

end DeltaSLearning


