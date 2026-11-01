-- Prove2me | Definitions.Def_HomotopyProxVM_IsStronglyConvexParam
-- name    : HomotopyProxVM_IsStronglyConvexParam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:50.751986+00:00
-- url     : https://prove2.me/theorems/9c325742-c018-4477-bb19-ef633888952b
-- title:
--   $\mu_f$-strong convexity of $f$
-- statement:
--   A function $f:\mathbb R^p\to\mathbb R$ is **$\mu$-strongly convex** if $\mu>0$ and
--
--   $$
--   x\mapsto f(x)-\frac{\mu}{2}\|x\|_2^2
--   $$
--
--   remains convex. The number $\mu$ is the strong convexity parameter. This is half of Assumption 2 and the source of the contraction factor $\omega$.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`. The definition is the paper's wording; Mathlib's `strongConvexOn_iff_convex` identifies it with `StrongConvexOn ℝ Set.univ μ f`. That $f$ is real-valued on all of $\mathbb R^p$ is explained in `IsSmoothParam`.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §2.1, p.5

import Mathlib

namespace HomotopyProxVM

/-- `f` is `μ`-strongly convex: `μ > 0` and `f(·) − (μ/2)‖·‖₂²` remains convex
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §2.1, p.5).

**Formalization Note.** `ℝᵖ` is `EuclideanSpace ℝ (Fin p)` and `f` is real-valued on all of it; see
the note on `IsSmoothParam` for why that is this paper's `f` under Assumption 2. The display is the
paper's own wording; Mathlib's `strongConvexOn_iff_convex` identifies it with
`StrongConvexOn ℝ Set.univ μ f`. -/
def IsStronglyConvexParam {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ConvexOn ℝ Set.univ (fun x => f x - μ / 2 * ‖x‖ ^ 2)

end HomotopyProxVM


