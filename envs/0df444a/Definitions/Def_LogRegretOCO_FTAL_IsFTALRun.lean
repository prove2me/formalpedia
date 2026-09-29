-- Prove2me | Definitions.Def_LogRegretOCO_FTAL_IsFTALRun
-- name    : LogRegretOCO_FTAL_IsFTALRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:38:39.117973+00:00
-- url     : https://prove2.me/theorems/546e31c3-7331-4f71-bb13-3116bfb55af7
-- title:
--   Follow the Approximate Leader, version 1 (Fig. 3)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be a convex decision set, $\beta$ a real parameter, and $f_1, f_2, \dots$ differentiable cost functions. Given the points $x_1, x_2, \dots$ played so far, write $\nabla_\tau = \nabla f_\tau(x_\tau)$ and define the **approximate cost** of round $\tau$ by
--
--   $$
--   \tilde f_\tau(x) = f_\tau(x_\tau) + \nabla_\tau^\top (x - x_\tau) + \frac{\beta}{2} (x - x_\tau)^\top \nabla_\tau \nabla_\tau^\top (x - x_\tau).
--   $$
--
--   The sequence $x_1, x_2, \dots$ is a run of **Follow the Approximate Leader** (FTAL, version 1) with parameter $\beta$ if $x_1 \in P$ is arbitrary and, for every $t \ge 1$,
--
--   $$
--   x_t \in \arg\min_{x \in P} \sum_{\tau=1}^{t-1} \tilde f_\tau(x),
--   $$
--
--   i.e. it is a run of Follow the Leader on the approximate costs $\tilde f_\tau$. The definition is not circular: $\tilde f_\tau$ depends only on $x_\tau$, and $x_t$ only uses $\tilde f_\tau$ with $\tau < t$.
--
--   FTAL replaces each cost by a quadratic lower model built from its gradient; for $\alpha$-exp-concave costs and $\beta = \tfrac12 \min\{1/(4GD), \alpha\}$ it has logarithmic regret (Theorem 6).
--
--   **Formalization Note** The file defines `approxLoss f x β τ z` $= \tilde f_\tau(z)$ and `IsFTALRun P β f x := IsFTLRun P (approxLoss f x β) x`. The quadratic form $(x - x_\tau)^\top \nabla_\tau \nabla_\tau^\top (x - x_\tau)$ is written as the squared inner product $\langle \nabla_\tau, x - x_\tau\rangle^2$, which is the same number. The gradient is Mathlib's `gradient` of the ambient function $f_\tau$ on $\mathbb{R}^n$. Only version 1 of Fig. 3 is formalized; version 2 (Newton-like form with a Moore–Penrose pseudoinverse) and the equivalence Lemma 4 are not part of this mission.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 180, Fig. 3 (Follow the Approximate Leader, version 1)

import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL

/-- The approximate cost of round `τ` in Follow the Approximate Leader (Fig. 3, version 1,
p. 180): with `∇_τ = ∇f_τ(x_τ)`,
`f̃_τ(z) = f_τ(x_τ) + ∇_τᵀ(z - x_τ) + (β/2) (z - x_τ)ᵀ ∇_τ ∇_τᵀ (z - x_τ)`.
The quadratic form `(z - x_τ)ᵀ ∇_τ ∇_τᵀ (z - x_τ)` equals `⟪∇_τ, z - x_τ⟫ ^ 2`. -/
noncomputable def approxLoss {n : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (β : ℝ) (τ : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f τ (x τ) + inner ℝ (gradient (f τ) (x τ)) (z - x τ)
    + β / 2 * (inner ℝ (gradient (f τ) (x τ)) (z - x τ)) ^ 2

/-- Follow the Approximate Leader, version 1 (Fig. 3, p. 180): `x 1 ∈ P` is arbitrary and, for
`t ≥ 2`, `x t` minimises `∑_{τ=1}^{t-1} f̃_τ` over `P`, where `f̃_τ = approxLoss f x β τ`. This
is Follow the Leader run on the approximate costs; `f̃_τ` only involves `x τ` with `τ < t`, so the
predicate on the whole trajectory is well founded. -/
def IsFTALRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (β : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  IsFTLRun P (approxLoss f x β) x

end LogRegretOCO.FTAL


