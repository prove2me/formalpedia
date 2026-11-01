-- Prove2me | Definitions.Def_HomotopyProxVM_IsClosedFn
-- name    : HomotopyProxVM_IsClosedFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:51.694393+00:00
-- url     : https://prove2.me/theorems/44509c22-4d24-445d-8e5a-679054406a0b
-- title:
--   Closed function, on the domain-and-values encoding
-- statement:
--   A function $g:\mathbb R^p\to\mathbb R\cup\{+\infty\}$ is **closed** if its epigraph is a closed subset of $\mathbb R^p\times\mathbb R$. For $g$ given by its effective domain $D$ and its finite values on $D$, the epigraph is
--
--   $$
--   \{(x,t)\in\mathbb R^p\times\mathbb R: x\in D,\ g(x)\le t\}.
--   $$
--
--   Together with properness and convexity this is the standing assumption on $g$ in problem (1). It is what makes the scaled proximal operator and the solutions of the parametrized problem exist.
--
--   **Formalization Note** The encoding is the one of the published `OneStepProx.IsProperConvex`, whose definition does not include closedness; values of the Lean function off $D$ are never read.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, (1), p.1, "proper, closed, and convex functions"

import Mathlib

namespace HomotopyProxVM

/-- The function `g : ℝᵖ → ℝ ∪ {+∞}` is closed: its epigraph is a closed set
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, (1), p.1, "proper, closed, and convex").

**Formalization Note.** `g` is encoded by its effective domain `D` and its finite values on `D`, as
in `OneStepProx.IsProperConvex`, whose definition does not include closedness. The epigraph of the
extended function is `{(x, t) | x ∈ D ∧ g x ≤ t}`; values of `g` off `D` are never read. -/
def IsClosedFn {p : ℕ} (D : Set (EuclideanSpace ℝ (Fin p)))
    (g : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  IsClosed {q : EuclideanSpace ℝ (Fin p) × ℝ | q.1 ∈ D ∧ g q.1 ≤ q.2}

end HomotopyProxVM


