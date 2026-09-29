-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
-- name    : FoundationsML_ReinforcementLearning_IsOptimalPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:34:18.981983+00:00
-- url     : https://prove2.me/theorems/4d8ac693-544a-45ab-be4f-38b171adaa85
-- title:
--   Optimal policy (Definition 17.4)
-- statement:
--   **Definition 17.4 (Optimal policy), p. 382, PDF p. 399.** A policy $\pi^*$ is optimal if its
--   value is maximal for every state $s\in S$, that is, for any policy $\pi$ and any state
--   $s\in S$, $V_{\pi^*}(s)\ge V_\pi(s)$.
--
--   **Formalization Note.** `IsOptimalPolicy π P Er γ` quantifies over every `π'` satisfying
--   `IsPolicy π'` (every stochastic or deterministic policy, matching the book's unrestricted
--   "for any policy $\pi$"), requiring `PolicyValue π' P Er γ s ≤ PolicyValue π P Er γ s` for
--   every state `s`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 382, Definition 17.4 (PDF p. 399)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy

namespace FoundationsML.ReinforcementLearning

/-- Definition 17.4 (Optimal policy; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 382, PDF p. 399): a policy `π*` is optimal if
`∀ π, ∀ s, V_{π*}(s) ≥ V_π(s)`. -/
def IsOptimalPolicy {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) : Prop :=
  ∀ π' : S → A → ℝ, IsPolicy π' → ∀ s : S, PolicyValue π' P Er γ s ≤ PolicyValue π P Er γ s

end FoundationsML.ReinforcementLearning


