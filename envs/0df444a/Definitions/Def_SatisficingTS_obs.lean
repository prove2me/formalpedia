-- Prove2me | Definitions.Def_SatisficingTS_obs
-- name    : SatisficingTS_obs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:51.293136+00:00
-- url     : https://prove2.me/theorems/0fe3b804-86f4-4521-9c45-8d7e512f7918
-- title:
--   The action–outcome process $(A_t, Y_t)$
-- statement:
--   Given a policy $\psi$, a system function $g$, the parameter $\theta$, the disturbances $(W_t)$ and the policy's randomness $\xi$, the action–outcome process is defined by recursion on $t\ge0$:
--   $$
--   A_t=\psi_t(\mathcal H_{t-1},\xi),\qquad Y_t=g(A_t,\theta,W_t),\qquad \mathcal H_{t-1}=(A_0,Y_0,\dots,A_{t-1},Y_{t-1}).
--   $$
--   $\mathrm{obs}_t(\omega)$ is the pair $(A_t(\omega),Y_t(\omega))$. The reward collected in period $t$ is $R_t=R(Y_t)$.
--
--   This is the process every quantity of the paper (regret, information ratio, mutual information with the history) is computed from.
--
--   **Formalization Note** Defined by well-founded recursion on $t$: the history passed to $\psi_t$ is $i\mapsto\mathrm{obs}_i(\omega)$ for $i<t$.
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §2, pp.4–5 (A_t = ψ_t(H_{t−1}, ξ), Y_t = g(A_t, θ, W_t), R_t ≡ R(Y_t))

import Mathlib

namespace SatisficingTS

/-- **The action–outcome process `(A_t, Y_t)`** (Russo & Van Roy, *Satisficing in Time-Sensitive
Bandit Learning*, arXiv:1803.02855v2, §2, pp.4–5): `A_t = ψ_t(H_{t−1}, ξ)` and
`Y_t = g(A_t, θ, W_t)`, where `H_{t−1} = (A_0, Y_0, …, A_{t−1}, Y_{t−1})`.

`obs ψ g θ W ξ t ω = (A_t ω, Y_t ω)`, defined by strong recursion on `t`: the history passed to
`ψ_t` is the function `i ↦ obs ψ g θ W ξ i ω` on `Fin t`.

**Formalization Note.** Histories are 0-based: the paper's `H_{t−1}` is the `t`-entry tuple
`(obs 0 ω, …, obs (t−1) ω)` (`hist t`), and `H_{−1}` is empty. The paper's reward is
`R_t = R(Y_t) = R ((obs ψ g θ W ξ t ω).2)`. -/
def obs {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*}
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (g : 𝒜 → Θ → 𝒲 → 𝒴)
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (t : ℕ) (ω : Ω) : 𝒜 × 𝒴 :=
  (ψ t (fun i => obs ψ g θ W ξ (i : ℕ) ω) (ξ ω),
    g (ψ t (fun i => obs ψ g θ W ξ (i : ℕ) ω) (ξ ω)) (θ ω) (W t ω))
termination_by t
decreasing_by all_goals exact i.isLt

end SatisficingTS


