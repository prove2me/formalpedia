-- Prove2me | Definitions.Def_DeltaSLearning_stepSize
-- name    : DeltaSLearning_stepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:09:37.254805+00:00
-- url     : https://prove2.me/theorems/51743b02-a1c8-4915-bd0c-838e57cf662d
-- title:
--   Step sizes $\eta^n=\beta/(\xi\sqrt n)$
-- statement:
--   Theorem 3's step sizes $\eta^n := \beta/(\xi\sqrt n)$ for epochs $n\ge1$.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3, p.17

import Mathlib
import Definitions.Def_DeltaSLearning_xi

namespace DeltaSLearning

/-- Theorem 3's step sizes `ηⁿ = β / (ξ √n)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 3,
p.17.

**Formalization Note** Indexed by the 1-based epoch `n`; the value at `n = 0` is unused. -/
noncomputable def stepSize (cp : Params) (n : ℕ) : ℝ :=
  cp.β / (xi cp * Real.sqrt n)

end DeltaSLearning


