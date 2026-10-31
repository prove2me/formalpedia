-- Prove2me | Definitions.Def_PersuadeFly_value
-- name    : PersuadeFly_value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:00.001756+00:00
-- url     : https://prove2.me/theorems/a29598a9-b191-48a1-91b1-090aae00040c
-- title:
--   The sender's expected utility $V(\mu,\sigma)$
-- statement:
--   The sender's expected utility under prior $\mu$ and mechanism $\sigma$ (with obedient receivers) is
--   $$
--   V(\mu,\sigma)=\sum_{\omega\in\Omega}\sum_{a\in A}\mu(\omega)\,\sigma(\omega,a)\,v(\omega,a).
--   $$
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.1, p.15

import Mathlib
import Definitions.Def_PersuadeFly_Instance

namespace PersuadeFly

/-- **The sender's expected utility `V(μ, σ)`.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.1, p.15:
`V(μ, σ) = ∑_{ω ∈ Ω} ∑_{a ∈ A} μ(ω) σ(ω, a) v(ω, a)`. -/
def value {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (μ : Ω → ℝ)
    (σ : Ω → A → ℝ) : ℝ :=
  ∑ ω, ∑ a, μ ω * σ ω a * I.v ω a

end PersuadeFly


