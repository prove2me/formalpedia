-- Prove2me | Definitions.Def_CertDRO_NNSmooth_Softmax
-- name    : CertDRO_NNSmooth_Softmax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:32:28.07926+00:00
-- url     : https://prove2.me/theorems/a336cf4d-a3a5-4408-a385-b7f7ea16b36c
-- title:
--   The softmax probabilities p(v) and the softmax loss σ_y(v) = −log p_y(v) of (19)
-- statement:
--   For a logit vector $v\in\mathbb R^K$ the **softmax probabilities** are
--   $$p_k(v)=\frac{\exp(v_k)}{\sum_{j=1}^{K}\exp(v_j)},\qquad p(v)=\sum_{k=1}^{K}p_k(v)\,e_k\in\mathbb R^K,$$
--   and the **softmax loss** of the class $y\in\{1,\dots,K\}$ is
--   $$\sigma_y(v)=-\log p_y(v)=-\log\frac{\exp(v_y)}{\sum_{j=1}^{K}\exp(v_j)}.$$
--   Composed with the logits $v=F_L(\theta;x)$ of a network, this is the classification loss $\ell(\theta;(x,y))=-\log p_y(\theta;x)$ of (19).
--
--   **Formalization Note** $\mathbb R^K$ is `EuclideanSpace ℝ (Fin K)` and classes are `Fin K` (0-based). Whenever a class $y$ exists, $K\ge1$, the denominator is positive and the logarithm is applied to a number in $(0,1]$, so no junk value of `Real.log` is involved.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 12, (19); p. 46, §B.9 (σ_y and p(x))

import Mathlib

namespace CertDRO.NNSmooth

/-- The softmax probability vector `p(v) = ∑_k p_k(v) e_k ∈ ℝ^K` of a logit vector `v ∈ ℝ^K`,
with `p_k(v) = exp(v_k) / ∑_{j=1}^K exp(v_j)` ((19), p. 12, and §B.9, p. 46). -/
noncomputable def softmaxProb {K : ℕ} (v : EuclideanSpace ℝ (Fin K)) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (fun k => Real.exp (v k) / ∑ j, Real.exp (v j))

/-- The softmax loss of the class `y` as a function of the logits, (19) and §B.9:
`σ_y(v) = −log p_y(v) = −log (exp(v_y) / ∑_{j=1}^K exp(v_j))`. -/
noncomputable def softmaxLoss {K : ℕ} (y : Fin K) (v : EuclideanSpace ℝ (Fin K)) : ℝ :=
  -Real.log (Real.exp (v y) / ∑ j, Real.exp (v j))

end CertDRO.NNSmooth


