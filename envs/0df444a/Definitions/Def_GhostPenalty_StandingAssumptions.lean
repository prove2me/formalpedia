-- Prove2me | Definitions.Def_GhostPenalty_StandingAssumptions
-- name    : GhostPenalty_StandingAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:58.509137+00:00
-- url     : https://prove2.me/theorems/e8aafad5-6f30-45da-8984-11d458a1604e
-- title:
--   Blanket assumptions on problem (P)
-- statement:
--   Problem (P) is
--   $$\operatorname*{minimize}_x\ f(x)\quad\text{s.t.}\quad g(x)\le 0,\ x\in K.$$
--   The **blanket assumptions** of the paper are: $K\subseteq\mathbb R^n$ is nonempty, closed and convex, and $f:\mathbb R^n\to\mathbb R$ and $g:\mathbb R^n\to\mathbb R^m$ are $C^{1,1}$ on an open set $U\supseteq K$, that is, continuously differentiable on $U$ with locally Lipschitz gradients.
--
--   No feasibility, no constraint qualification, no boundedness of $K$ and no global Lipschitz constant is assumed.
--
--   **Formalization Note** $C^{1,1}$ on $U$ is: differentiable on $U$ and `gradient` locally Lipschitz on $U$ (a locally Lipschitz gradient is continuous). One open set serves $f$ and every $g_i$, as in the source.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §1, problem (P), p.1

import Mathlib

namespace GhostPenalty

/-- **Blanket assumptions on problem (P).**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §1, (P), p.1: "minimize_x f(x) s.t. g(x) ≤ 0, x ∈ K, (P)
where K ⊆ ℝⁿ is a nonempty closed and convex set, and f : ℝⁿ → ℝ and g : ℝⁿ → ℝᵐ are C^{1,1}
(i.e., continuously differentiable with locally Lipschitz gradients) functions on an open set
containing K." These are assumed throughout the paper (§2, p.5: "under the blanket assumptions
indicated in the Introduction").

`StandingAssumptions K f g` says: `K` is nonempty, closed and convex, and there is one open set
`U ⊇ K` on which `f` and every `g_i` are differentiable with locally Lipschitz gradient.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, the constraints are indexed by
`Fin m`. C^{1,1} on `U` is "differentiable on `U` with `gradient` locally Lipschitz on `U`"
(Mathlib's `LocallyLipschitzOn`); a locally Lipschitz gradient is continuous, so this is
continuous differentiability with locally Lipschitz gradient. No global Lipschitz constant, no
boundedness of `K`, no feasibility and no constraint qualification is assumed. -/
def StandingAssumptions {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ K ⊆ U ∧
      (DifferentiableOn ℝ f U ∧ LocallyLipschitzOn U (gradient f)) ∧
      ∀ i, DifferentiableOn ℝ (g i) U ∧ LocallyLipschitzOn U (gradient (g i))

end GhostPenalty


