-- Prove2me | Definitions.Def_OrabonaOL_OGD_IsProjectedOGDRun
-- name    : OrabonaOL_OGD_IsProjectedOGDRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:18.460377+00:00
-- url     : https://prove2.me/theorems/08b6f8ca-9e9e-4788-8e8f-fd0dd7e6ca09
-- title:
--   A run of Projected Online Gradient Descent (Algorithm 2.1)
-- statement:
--   Let $V \subseteq \mathbb{R}^d$, let $\eta_1, \eta_2, \dots$ be step sizes, let $\ell_1, \ell_2, \dots : \mathbb{R}^d \to \mathbb{R}$ be loss functions, and let $T \in \mathbb{N}$ be the number of rounds. A sequence of predictions $x_1, x_2, \dots$ is a **run of Projected Online Gradient Descent** (Algorithm 2.1) on $V$ for $T$ rounds if
--
--   1. the first prediction is admissible: $x_1 \in V$;
--   2. for every round $t = 1, \dots, T$, with $g_t = \nabla \ell_t(x_t)$,
--   $$
--   x_{t+1} = \Pi_V(x_t - \eta_t g_t) = \operatorname{argmin}_{y \in V} \|x_t - \eta_t g_t - y\|_2 .
--   $$
--
--   At round $t$ the algorithm outputs $x_t$, pays $\ell_t(x_t)$, takes a gradient step of length $\eta_t$ and projects back onto $V$. This predicate is the object about which the regret bound of Theorem 2.13 is stated.
--
--   **Formalization Note** Indices are 1-based: $x_1$ is the first prediction and $x_{T+1}$ is the output of the last projection. Values of the sequences at index $0$ or beyond the horizon are unconstrained. The projection is the predicate `IsEuclideanProj`, and $\nabla$ is Mathlib's `gradient`. The algorithm's requirements ($V$ non-empty, closed and convex; $\eta_t > 0$; each $\ell_t$ convex and differentiable on an open set containing $V$) are hypotheses of the theorems about runs, not part of this predicate. The losses form an arbitrary sequence, so losses chosen adaptively by an adversary are covered.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 12 (PDF p. 24), Algorithm 2.1 (Projected Online Gradient Descent)

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace OrabonaOL.OGD

/-- **A run of Projected Online Gradient Descent (Algorithm 2.1).**
Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 12 (PDF p. 24),
Algorithm 2.1 "Projected Online Gradient Descent (OGD)".

`IsProjectedOGDRun V η ℓ T x` says that the sequence of predictions `x` is produced by
Algorithm 2.1 on the feasible set `V`, with step sizes `η` and losses `ℓ`, for `T` rounds:
the first prediction satisfies `x 1 ∈ V`, and for every round `t = 1, …, T`, with
`g_t = ∇ℓ_t(x_t)`, the next prediction is the Euclidean projection
`x_{t+1} = Π_V(x_t − η_t g_t)`.

**Formalization Note.** Indices are 1-based: `x 1` is the first prediction, `η t` and `ℓ t`
are the step size and loss of round `t`, and `x (T + 1)` is the output of the last projection;
values of `η`, `ℓ`, `x` at index `0` or beyond `T` (resp. `T + 1`) are not constrained. The
gradient is Mathlib's `gradient`; the hypotheses that make it the true gradient (each `ℓ t`
differentiable on an open set containing `V`), the positivity of the step sizes and the
convexity of the losses are hypotheses of the theorems about runs, not part of this predicate.
The losses are an arbitrary sequence, so a run against an adaptive adversary is covered. -/
def IsProjectedOGDRun {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d))) (η : ℕ → ℝ)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (T : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 1 ∈ V ∧ ∀ t ∈ Finset.Icc 1 T,
    IsEuclideanProj V (x t - η t • gradient (ℓ t) (x t)) (x (t + 1))

end OrabonaOL.OGD


