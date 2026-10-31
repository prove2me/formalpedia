-- Prove2me | Definitions.Def_LatentRobust_sigmaMin
-- name    : LatentRobust_sigmaMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:33.445623+00:00
-- url     : https://prove2.me/theorems/531a429e-4a03-4c9b-b4d4-7dbf837f4f89
-- title:
--   The smallest nonzero singular value $\sigma_{\min}(W)$
-- statement:
--   For a real $d\times k$ matrix $W$, viewed as a linear map $\mathbb R^k\to\mathbb R^d$ between Euclidean spaces, let $\sigma_1(W)\ge\sigma_2(W)\ge\dots\ge\sigma_k(W)\ge 0$ be its singular values (the square roots of the eigenvalues of $W^\top W$). The quantity
--   $$
--   \sigma_{\min}(W)=\sigma_k(W)
--   $$
--   is the smallest nonzero singular value when $W$ has full column rank and $k\ge 1$.
--
--   It measures how weakly the latent directions are scaled when embedded in the ambient space, and it is the quantity in the condition (7) of Theorem 3.1.
--
--   **Formalization Note** Mathlib lists the singular values in decreasing order from index $0$, so $\sigma_k$ is the value at index $k-1$. All statements using $\sigma_{\min}$ assume full column rank and $k\ge1$; outside that case the value is not the paper's.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §1.1 Notation, p.4 ("σmin(W) denote its smallest “nonzero” singular value")

import Mathlib

namespace LatentRobust

/-- The smallest singular value `σ_min(W)` of a `d × k` real matrix `W`
(Javanmard, Mehrabi, arXiv:2110.11950v2, §1.1 Notation, p.4: "`σmin(W)` denote its smallest
“nonzero” singular value").

**Formalization Note** `W` acts as the linear map `ℝ^k → ℝ^d` (Euclidean spaces), and Mathlib's
`singularValues` lists its singular values in decreasing order starting at index `0`. The value
at index `k − 1` is the `k`-th (last) one. For a `W` of full column rank with `k ≥ 1` (the
paper's standing assumption, p.6) all `k` singular values are positive, so this is the smallest
nonzero singular value. Every statement using `sigmaMin` assumes full column rank and `k ≥ 1`. -/
noncomputable def sigmaMin {d k : ℕ} (W : Matrix (Fin d) (Fin k) ℝ) : ℝ :=
  (Matrix.toEuclideanLin W).singularValues (k - 1)

end LatentRobust


