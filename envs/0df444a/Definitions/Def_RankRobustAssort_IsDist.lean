-- Prove2me | Definitions.Def_RankRobustAssort_IsDist
-- name    : RankRobustAssort_IsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:15.044357+00:00
-- url     : https://prove2.me/theorems/7ef7f30a-1025-423e-86cb-6ae14274ab75
-- title:
--   Probability distribution $\lambda\in\Delta_\Sigma$ over rankings
-- statement:
--   Let $\Sigma$ be the set of all $(n+1)!$ rankings of the products $\{0,\dots,n\}$. A vector $\lambda=(\lambda_\sigma)_{\sigma\in\Sigma}$ is a **probability distribution over rankings**, $\lambda\in\Delta_\Sigma$, when
--
--   $$
--   \lambda_\sigma\ge0\ \text{ for all }\sigma\in\Sigma,\qquad \sum_{\sigma\in\Sigma}\lambda_\sigma=1.
--   $$
--
--   A ranking-based choice model is parameterized by such a $\lambda$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Notation p.6 and §2, p.7

import Mathlib

namespace RankRobustAssort

/-- `IsDist λ` says that `λ` is a probability distribution over the rankings, `λ ∈ Δ_Σ`.

Sturt, arXiv:2112.05010v4, Notation, p.6 (`Δ_A ≜ {λ : ∑_{a∈A} λ_a = 1, λ_a ≥ 0 ∀a ∈ A}`) and §2,
p.7 (a ranking-based choice model is parameterized by a probability distribution `λ` over the set
`Σ` of all rankings).

Formalization Note: `Σ` is `Equiv.Perm (Fin (n+1))` (all `(n+1)!` rankings), and `λ` is a
real-valued function on it. -/
def IsDist {n : ℕ} (lam : Equiv.Perm (Fin (n + 1)) → ℝ) : Prop :=
  (∀ σ, 0 ≤ lam σ) ∧ ∑ σ, lam σ = 1

end RankRobustAssort


