-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_maxEntObjective
-- name    : RouzeFranca_LearnGibbs_maxEntObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:43.276366+00:00
-- url     : https://prove2.me/theorems/2cd62ea9-89df-44b2-8c94-fbec5b656415
-- title:
--   The maximum-entropy objective $f(\mu)=\log\mathcal Z(\mu)+\beta\sum_i e_i(\lambda)\mu_i$
-- statement:
--   Let $E_1,\dots,E_m$ be observables on $n$ qubits, $\beta$ an inverse temperature and $\lambda\in\mathbb R^m$ the target parameter. The **maximum-entropy objective** is the function $f:\mathbb R^m\to\mathbb R$,
--   $$
--   f(\mu)=\log\mathcal Z(\mu)+\beta\sum_{i=1}^m e_i(\lambda)\,\mu_i ,
--   $$
--   where $\mathcal Z$ is the partition function and $e(\lambda)$ the expectation vector of the Gibbs state $\sigma(\lambda)$.
--
--   It is the objective of the dual (21) of the maximum-entropy problem; its minimizer over $B_{\ell_\infty}(0,1)$ is $\lambda$, and it depends on $\lambda$ only through the measurable expectation values $e(\lambda)$.
--
--   **Formalization Note** The target parameter $\lambda$ is written `lam` in Lean (`λ` is a reserved word).
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Lemma A.1, Eq. (24), p. 15; §3.1, p. 8

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

namespace RouzeFranca.LearnGibbs

/-- The maximum-entropy objective `f(μ) = log Z(μ) + β ∑ᵢ eᵢ(λ) μᵢ` attached to the target
parameter `lam` (the paper's `λ`).

Rouzé, Stilck França, arXiv:2107.03333v4, Lemma A.1, Eq. (24), p. 15, and §3.1, p. 8 ("If we
define the function f : µ ↦ log(Z(µ)) + β Σ µ_i e_i(λ)").

**Formalization Note.** `lam` stands for the paper's `λ` (a reserved word in Lean). Defined for
all `μ ∈ ℝ^m`. -/
noncomputable def maxEntObjective {n m : ℕ} (E : Fin m → Mat n) (β : ℝ)
    (lam : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) → ℝ :=
  fun μ => logPartition E β μ + β * ∑ i, expect E β lam i * μ i

end RouzeFranca.LearnGibbs


