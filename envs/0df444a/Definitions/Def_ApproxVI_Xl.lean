-- Prove2me | Definitions.Def_ApproxVI_Xl
-- name    : ApproxVI_Xl
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:07.615302+00:00
-- url     : https://prove2.me/theorems/a1f90eaa-a3d5-476a-a4e9-61155753efa5
-- title:
--   The linearly interpolated trajectory $X_l$ of (20)
-- statement:
--   Let $x_n$ be the iterates and $\tilde x_{n+1}$ the pre-projection points of the projective scheme (18). The **linearly interpolated trajectory** is $X_l(t_n)=x_n$ and
--
--   $$
--   X_l(t)=\Big(1-\frac{t-t_n}{a(n)}\Big)x_n+\frac{t-t_n}{a(n)}\,\tilde x_{n+1},\qquad t\in[t_n,t_{n+1}).
--   $$
--
--   It is right continuous with jumps where the projection acts.
--
--   **Formalization Note** $n$ is the interval index of $t$; at $t=t_n$ the formula gives $x_n$, so the two cases are one formula.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, (20), p.22

import Mathlib
import Definitions.Def_ApproxVI_segIdx

namespace ApproxVI

/-- The linearly interpolated trajectory (20) of Ramaswamy & Bhatnagar, *Analyzing Approximate
Value Iteration Algorithms*, arXiv:1709.04673v5, §6.1, p.22:
`X_l(t) := xₙ` for `t = tₙ`, and
`X_l(t) := (1 − (t − tₙ)/a(n)) xₙ + ((t − tₙ)/a(n)) x̃ₙ₊₁` for `t ∈ [tₙ, tₙ₊₁)`.
Here `x` is the iterate sequence and `xt` the pre-projection sequence `x̃` of (18).

**Formalization Note** `n` is `segIdx a t`, the index of the interval containing `t`. At
`t = tₙ` the second formula gives `xₙ`, so the two cases of (20) are one formula. -/
noncomputable def Xl {d : ℕ} (a : ℕ → ℝ) (x xt : ℕ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  (1 - (t - tSeq a (segIdx a t)) / a (segIdx a t)) • x (segIdx a t) +
    ((t - tSeq a (segIdx a t)) / a (segIdx a t)) • xt (segIdx a t + 1)

end ApproxVI


