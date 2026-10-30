-- Prove2me | Definitions.Def_AdaGradDHS_Diag_IsOneStronglyConvexWrt
-- name    : AdaGradDHS_Diag_IsOneStronglyConvexWrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:21.979467+00:00
-- url     : https://prove2.me/theorems/c465717f-513d-4746-b374-f5aa7e52c351
-- title:
--   $\psi$ is 1-strongly convex with respect to a seminorm (on a set $X$)
-- statement:
--   Let $X \subseteq \mathbb{R}^d$, $\psi : \mathbb{R}^d \to \mathbb{R}$ and let $\|\cdot\|_\psi$ be a seminorm on $\mathbb{R}^d$. We say $\psi$ is **1-strongly convex with respect to $\|\cdot\|_\psi$ on $X$** if $\psi$ is differentiable at every point of $X$ and, for all $x, y \in X$,
--   $$\psi(y) \ge \psi(x) + \langle \nabla\psi(x),\, y - x\rangle + \tfrac12 \|x - y\|_\psi^2 .$$
--
--   This is the standing assumption of Section 2 of the paper on the time-varying proximal functions $\psi_t$, under which the regret bounds of Propositions 2 and 3 hold. Equivalently, $B_\psi(y, x) \ge \tfrac12\|x - y\|_\psi^2$ for $x, y \in X$.
--
--   **Formalization Note** The paper states the inequality for all $x, y \in \mathbb{R}^d$; here it is asked only on $X$, so every theorem assuming it covers the paper's case. Differentiability on $X$ makes Mathlib's `gradient` the true gradient there. The seminorm may vanish on nonzero vectors.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §2, p. 2129 (unnumbered definition of 1-strong convexity w.r.t. a semi-norm)

import Mathlib

namespace AdaGradDHS.Diag

/-- **`ψ` is 1-strongly convex with respect to a seminorm `‖·‖_ψ` (on a set `X`).**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §2, p. 2129 (unnumbered): "We also assume that ψt is 1-strongly convex with respect to a
time-dependent semi-norm ‖·‖ψt. Formally, ψ is 1-strongly convex with respect to ‖·‖ψ if
ψ(y) ≥ ψ(x) + ⟨∇ψ(x), y − x⟩ + ½‖x − y‖²ψ."

`IsOneStronglyConvexWrt X ψ n` says: `ψ` is differentiable at every point of `X`, and for all
`x, y ∈ X`, `ψ x + ⟨∇ψ(x), y − x⟩ + ½ n(x − y)² ≤ ψ y`.

**Formalization Note.** The paper states the inequality for all `x, y` (on `ℝ^d`); here it is
required only for `x, y ∈ X`, the set over which the algorithms optimize. A function strongly
convex on `ℝ^d` satisfies it for every `X`, so every theorem assuming this predicate is at least
as general as the paper's. Differentiability on `X` makes Mathlib's `gradient` (which is `0` at
non-differentiable points) the true gradient there. `n` is a `Seminorm` (the paper's
"semi-norm"); it may vanish on nonzero vectors. -/
def IsOneStronglyConvexWrt {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : Seminorm ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ x ∈ X, DifferentiableAt ℝ ψ x) ∧
    ∀ x ∈ X, ∀ y ∈ X, ψ x + inner ℝ (gradient ψ x) (y - x) + 1 / 2 * n (x - y) ^ 2 ≤ ψ y

end AdaGradDHS.Diag


