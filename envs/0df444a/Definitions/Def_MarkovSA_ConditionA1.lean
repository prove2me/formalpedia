-- Prove2me | Definitions.Def_MarkovSA_ConditionA1
-- name    : MarkovSA_ConditionA1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:10.734216+00:00
-- url     : https://prove2.me/theorems/5db1ab0c-bc5f-4aa8-9261-e27b95d77419
-- title:
--   Condition A.1 — non-increasing stepsizes with $\alpha_{k-t_k,k-1}\le\min(\varphi_2/(\varphi_3A^2),1/(4A))$
-- statement:
--   **Condition A.1.** The sequence $(\alpha_k)$ is non-increasing and
--
--   $$
--   \alpha_{k-t_k,k-1}\le\min\Big(\frac{\varphi_2}{\varphi_3A^2},\frac1{4A}\Big)\qquad\text{for all }k\ge t_k.
--   $$
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Condition A.1, p.24

import Mathlib
import Definitions.Def_MarkovSA_winSum

namespace MarkovSA

/-- **Condition A.1** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.24): the stepsizes are non-increasing and
`α_{k−t_k, k−1} ≤ min(φ₂/(φ₃A²), 1/(4A))` for all `k ≥ t_k`. -/
def ConditionA1 (t : ℕ → ℕ) (α : ℕ → ℝ) (φ₂ φ₃ A : ℝ) : Prop :=
  Antitone α ∧ ∀ k, t k ≤ k → winSum α (k - t k) k ≤ min (φ₂ / (φ₃ * A ^ 2)) (1 / (4 * A))

end MarkovSA


