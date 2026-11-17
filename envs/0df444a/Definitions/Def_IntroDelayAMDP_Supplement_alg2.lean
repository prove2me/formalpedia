-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg2
-- name    : IntroDelayAMDP_Supplement_alg2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:56.075562+00:00
-- url     : https://prove2.me/theorems/776df269-aea5-4f65-800e-6606ced259a8
-- title:
--   Algorithm 2 — region construction
-- statement:
--   **Algorithm 2 (Region Construction).** Input: features $\phi_1,\dots,\phi_{\sqrt K}\in\mathbb R^d$, a regularization $\lambda>0$ and a probability threshold $\theta$. Starting from $R=\{1,\dots,\sqrt K\}$, the outer loop builds regions $C_j$ with empirical probabilities $\hat p_j$ and truncated covariances $\hat\Sigma_j$ until at most $\sqrt K\theta$ features are left, and returns $(C_j,\hat p_j,\hat\Sigma_j)_j$ in order. Algorithms 3 and 5 call it in every layer with the layer's features of the last $\sqrt K$ processed episodes.
--
--
--   **Formalization Note** Indices are $0$-based positions in the input list.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, p.17

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_alg2Loop

namespace IntroDelayAMDP.Supplement

/-- **Algorithm 2 (Region Construction)** (printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). "Input: Features `ϕ₁, …, ϕ_{√K} ∈ ℝ^d`;
regularization `λ > 0`; probability threshold `θ`. 1: Let `R ← {1, …, √K}` index the features not in any
region yet, and `j ← 0`. … 10: return `(C_j, p̂_j, Σ̂_j)` for all `j`."
`alg2 rule feats λ θ √K` runs `alg2Loop` from `R = {0, …, |feats| − 1}` (0-based indices of the list
`feats`) and no regions, with `r = 2d log(1 + 1/λ)`, and returns the regions in order. The callers pass
exactly `√K` features. -/
noncomputable def alg2 {d : ℕ} (rule : RemovalRule d) (feats : List (Fin d → ℝ)) (lam θ : ℝ)
    (sqrtK : ℕ) : List (Region d) :=
  alg2Loop rule (fun i => feats.getD i 0) lam (2 * d * Real.log (1 + 1 / lam)) sqrtK θ
    (feats.length + 1) (Finset.range feats.length) []

end IntroDelayAMDP.Supplement


