-- Prove2me | Definitions.Def_PersuadeFly_IsMechanism
-- name    : PersuadeFly_IsMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:14.072597+00:00
-- url     : https://prove2.me/theorems/a5c12995-2bd5-41b6-a2f8-9fa18e16ad6d
-- title:
--   Signaling mechanism $\sigma\in\mathcal S$
-- statement:
--   A **signaling mechanism** is a map $\sigma:\Omega\times A\to\mathbb R$ such that $\sigma(\omega,\cdot)\in\Delta(A)$ for every state $\omega$; $\sigma(\omega,a)$ is the probability of recommending action $a$ when the state is $\omega$. The set of all mechanisms is
--   $$
--   \mathcal S=\{\sigma:\sigma(\omega,\cdot)\in\Delta(A)\ \text{for each }\omega\in\Omega\}.
--   $$
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.1, p.14

import Mathlib

namespace PersuadeFly

/-- **Signaling mechanism.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.1, p.14: `S = {σ : σ(ω, ·) ∈ Δ(A) for each ω ∈ Ω}`, where
`σ(ω, a)` is the probability of recommending `a` in state `ω`. -/
def IsMechanism {Ω A : Type} [Fintype A] (σ : Ω → A → ℝ) : Prop :=
  ∀ ω, σ ω ∈ stdSimplex ℝ A

end PersuadeFly


