-- Prove2me | Definitions.Def_OneStepProx_IsProperConvex
-- name    : OneStepProx_IsProperConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:50.788979+00:00
-- url     : https://prove2.me/theorems/6f6c2f6f-115d-4078-89d6-3a0ce01e4ce1
-- title:
--   A proper convex function $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$, as a domain and its finite values
-- statement:
--   A function $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ is **proper** if it is finite somewhere and **convex** if it is convex as an extended-valued function. Such a function is described here by its effective domain $D=\{x: h(x)<\infty\}$ and its finite values on $D$: the pair $(D,h)$ is proper convex if
--
--   1. $D$ is nonempty, and
--   2. $D$ is convex and $h$ is convex on $D$.
--
--   The extended function is $h(x)$ for $x\in D$ and $+\infty$ for $x\notin D$. This is the nonsmooth part of the composite model, a penalty or a constraint.
--
--   **Formalization Note** Every proper convex function $\mathbb R^d\to\mathbb R\cup\{\infty\}$ has this form, and the values of the Lean function $h$ off $D$ are never read. Lower semicontinuity is not part of the definition: the paper does not assume it.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, §1.2, p.5, "h : ℝd → ℝ ∪ {∞} is convex and potentially nonsmooth"; Theorem 2.1, p.6, "hn is convex and proper"

import Mathlib

namespace OneStepProx

/-- `h : ℝ^d → ℝ ∪ {∞}` is proper and convex (Bassett & Deride, arXiv:2004.14521v3, §1.2, p.5, and
Theorem 2.1, p.6). The function is encoded by its effective domain `D` and its finite values `h`
on `D`: the extended function equals `h x` for `x ∈ D` and `+∞` for `x ∉ D`.

**Formalization Note.** Every proper convex function `ℝ^d → ℝ ∪ {∞}` has this form, and the
values of `h` off `D` are never read. `ConvexOn ℝ D h` contains the convexity of `D`. No lower
semicontinuity is required: the paper does not assume it, and it assumes the existence of the
minimizers it needs instead. -/
def IsProperConvex {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  D.Nonempty ∧ ConvexOn ℝ D h

end OneStepProx


