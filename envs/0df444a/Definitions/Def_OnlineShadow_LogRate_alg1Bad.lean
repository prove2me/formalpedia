-- Prove2me | Definitions.Def_OnlineShadow_LogRate_alg1Bad
-- name    : OnlineShadow_LogRate_alg1Bad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:15:27.742195+00:00
-- url     : https://prove2.me/theorems/78d58e42-703d-41f2-be05-ee53f29c1b78
-- title:
--   A bad outcome occurs in a run of Algorithm 1
-- statement:
--   A run of Algorithm 1 on the outcome string $\omega$ has a **bad outcome** if some soft binary measurement it performs, corresponding to $(B,\theta)$, either flags while $(B,\theta)$ is low ($\mathrm{Tr}(B\rho)\le\theta-\varepsilon/4$) or passes while $(B,\theta)$ is high ($\mathrm{Tr}(B\rho)>\theta$). A round is bad (Definition 4.3) if a bad outcome occurs in it. Tests the algorithm skips are never bad.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.3, p. 11; Definition 4.1, p. 10

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_alg1Run
import Definitions.Def_OnlineShadow_LogRate_IsLowTest
import Definitions.Def_OnlineShadow_LogRate_IsHighTest

namespace OnlineShadow.LogRate

/-- A **bad outcome** occurs in the run of Algorithm 1 on the outcome string `ω`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027
submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.3, p.11): some soft
binary measurement actually performed, for `(B, θ)`, flags while `(B, θ)` is low, or passes while
`(B, θ)` is high (Definition 4.1, for the unknown state `ρ`). Skipped tests are never bad. -/
def alg1Bad {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ω : Fin (2 * (m + K)) → Bool) : Prop :=
  ∃ s ∈ (alg1Run n m K ε lam adv ω).steps,
    (IsLowTest ρ s.obs s.thr ε ∧ s.flag = true) ∨ (IsHighTest ρ s.obs s.thr ∧ s.flag = false)

end OnlineShadow.LogRate


