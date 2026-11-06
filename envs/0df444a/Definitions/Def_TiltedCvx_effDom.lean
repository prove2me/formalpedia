-- Prove2me | Definitions.Def_TiltedCvx_effDom
-- name    : TiltedCvx_effDom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:08.741817+00:00
-- url     : https://prove2.me/theorems/1d0ecd2e-aba6-4f8e-84af-849169d54222
-- title:
--   Effective domain $\operatorname{dom}(f)$
-- statement:
--   For an extended-real-valued function $f:\mathbb R^d\to\overline{\mathbb R}$, where $\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}$, the (effective) domain of $f$ is the set of points where $f$ is finite:
--
--   $$
--   \operatorname{dom}(f):=\{x\in\mathbb R^d \mid f(x)\in\mathbb R\}.
--   $$
--
--   Every inequality between function values in this mission is taken at points of the domain, where the values are real numbers.
--
--   **Formalization Note** The ambient space is a real inner product space $E$ (for $\mathbb R^d$ take `EuclideanSpace ℝ (Fin d)`), and $\overline{\mathbb R}$ is `EReal`, so $f(x)\in\mathbb R$ means $f(x)\ne\pm\infty$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.10

import Mathlib

namespace TiltedCvx

/-- **Effective domain.** Pedramfar–Khanna–Quinn–Aggarwal, *Tilted Convexity and an Exact
Offline–Online Separation*, arXiv:2611.03472, §3, p.10: for `f : ℝ^d → ℝ̄`,
`dom(f) := {x ∈ ℝ^d | f(x) ∈ ℝ}`.

**Formalization Note** The ambient space is a real inner product space `E` (ℝ^d is
`EuclideanSpace ℝ (Fin d)`, and the one-dimensional examples use `ℝ`). `ℝ̄` is `EReal`, so
`f x ∈ ℝ` is `f x ≠ ⊤ ∧ f x ≠ ⊥`. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

end TiltedCvx


