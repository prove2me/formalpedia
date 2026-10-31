-- Prove2me | Definitions.Def_SQMeanEstimation_lqNorm
-- name    : SQMeanEstimation_lqNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:57.264326+00:00
-- url     : https://prove2.me/theorems/08ff1f12-7f85-4bb2-bb57-bcf5739d48f8
-- title:
--   $\ell_q$ norm $\|x\|_q=(\sum_i|x_i|^q)^{1/q}$ on $\mathbb R^d$
-- statement:
--   For $q>0$ and a vector $x\in\mathbb R^d$,
--   $$
--   \|x\|_q=\Big(\sum_{i=1}^d |x_i|^q\Big)^{1/q}.
--   $$
--   For $q\ge1$ this is the $\ell_q$ norm of the normed space $\ell_q^d=(\mathbb R^d,\|\cdot\|_q)$, and its unit ball $B_q^d=\{x:\|x\|_q\le1\}$ is the domain of the $\ell_q$ mean estimation problem. Lemma 3.12 also uses the expression for arbitrary exponents $0<p<r$.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` (coordinate $i$ of the paper is index $i-1$), and the powers are real powers `Real.rpow`.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, §2, p.10

import Mathlib

namespace SQMeanEstimation

/-- **The ℓq norm on ℝᵈ.**
Feldman, Guzmán, Vempala, *Statistical Query Algorithms for Mean Vector Estimation and Stochastic
Convex Optimization*, arXiv:1512.09170v2, §2, p.10: "for a vector x ∈ ℝᵈ,
‖x‖ₚ ≐ (Σ_{i∈[d]} |xᵢ|ᵖ)^{1/p}".

**Formalization Note.** ℝᵈ is `Fin d → ℝ` (the paper's coordinate `i` is index `i - 1`). The
power is `Real.rpow`. This is a norm only for `q ≥ 1`; for `q > 0` it is still the paper's
expression. The unit ball `Bᵈ_q` is `{x | lqNorm q x ≤ 1}`. -/
noncomputable def lqNorm {d : ℕ} (q : ℝ) (x : Fin d → ℝ) : ℝ :=
  (∑ i, |x i| ^ q) ^ (1 / q)

end SQMeanEstimation


