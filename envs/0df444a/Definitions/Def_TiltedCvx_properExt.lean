-- Prove2me | Definitions.Def_TiltedCvx_properExt
-- name    : TiltedCvx_properExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:13.347555+00:00
-- url     : https://prove2.me/theorems/69037453-9d09-4e4e-9c88-624ba7c72496
-- title:
--   Proper extension $\tilde f$
-- statement:
--   Given a nonempty set $X\subseteq\mathbb R^d$ and $f:X\to\mathbb R$, its **proper extension** $\tilde f:\mathbb R^d\to\overline{\mathbb R}$ equals $f$ on $X$ and $+\infty$ on $\mathbb R^d\setminus X$. Subdifferentials of a function defined on a subset always refer to its proper extension.
--
--   **Formalization Note** Here $f$ is a real function on all of $E$, of which only the values on $X$ are used.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.10

import Mathlib

namespace TiltedCvx

open Classical in
/-- **Proper extension.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §3, p.10: given a
non-empty set `X ⊆ ℝ^d` and `f : X → ℝ̄`, its proper extension `f̃` equals `f` on `X` and `+∞` on
`ℝ^d ∖ X`; subdifferentials of `f` always refer to `f̃`.

**Formalization Note** Here `f` is real-valued and given on all of `E`; only its values on `X`
matter. -/
noncomputable def properExt {E : Type*} (X : Set E) (f : E → ℝ) : E → EReal :=
  fun z => if z ∈ X then ((f z : ℝ) : EReal) else ⊤

end TiltedCvx


