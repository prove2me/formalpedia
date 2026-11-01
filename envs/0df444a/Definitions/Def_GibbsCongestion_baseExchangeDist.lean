-- Prove2me | Definitions.Def_GibbsCongestion_baseExchangeDist
-- name    : GibbsCongestion_baseExchangeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:19.92534+00:00
-- url     : https://prove2.me/theorems/e1e00a51-3eb9-48f7-974f-286d80f78f0c
-- title:
--   Stationary distribution $\pi(B)\propto w(B)$ of the base-exchange chain
-- statement:
--   On the bases of positive weight, $\pi(B)=w(B)/\sum_{B'}w(B')$: the distribution $\pi(\alpha)\propto w(\alpha)$ of §2.4, the stationary distribution of the base-exchange Markov chain.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib

namespace GibbsCongestion

/-- The distribution `π(B) = w(B) / ∑_{B'} w(B')` on the bases of positive weight, the
stationary distribution of the base-exchange chain (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11). -/
noncomputable def baseExchangeDist {α : Type*} [Fintype α] [DecidableEq α] (𝔅 : Finset (Finset α))
    (w : Finset α → ℝ) : {B : Finset α // B ∈ 𝔅 ∧ 0 < w B} → ℝ :=
  fun B => w B.1 / ∑ B' : {B : Finset α // B ∈ 𝔅 ∧ 0 < w B}, w B'.1

end GibbsCongestion


