-- Prove2me | Definitions.Def_ApproxVI_Wl
-- name    : ApproxVI_Wl
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:12.398997+00:00
-- url     : https://prove2.me/theorems/0729a7d3-5232-4b7f-9088-e49f48e712c7
-- title:
--   The linearly interpolated noise trajectory $W_l$
-- statement:
--   For noise terms $M_{n+1}$, the interpolated noise trajectory is $W_l(t_n)=\sum_{m=0}^{n-1}a(m)M_{m+1}$ and
--
--   $$
--   W_l(t)=\Big(1-\frac{t-t_n}{a(n)}\Big)W_l(t_n)+\frac{t-t_n}{a(n)}\,W_l(t_{n+1}),\qquad t\in[t_n,t_{n+1}).
--   $$
--
--   **Formalization Note** $n$ is the interval index of $t$; the grid values are the partial sums written out.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, p.22

import Mathlib
import Definitions.Def_ApproxVI_segIdx

namespace ApproxVI

/-- The linearly interpolated noise trajectory of Ramaswamy & Bhatnagar, *Analyzing Approximate
Value Iteration Algorithms*, arXiv:1709.04673v5, §6.1, p.22:
`W_l(t) := Σ_{m=0}^{n−1} a(m) M_{m+1}` for `t = tₙ`, and
`W_l(t) := (1 − (t − tₙ)/a(n)) W_l(tₙ) + ((t − tₙ)/a(n)) W_l(tₙ₊₁)` for `t ∈ [tₙ, tₙ₊₁)`.

**Formalization Note** `n` is `segIdx a t`, the index of the interval containing `t`; the
grid values `W_l(tₙ)` and `W_l(tₙ₊₁)` are written out as the partial sums. At `t = tₙ` the
second formula gives the first. -/
noncomputable def Wl {d : ℕ} (a : ℕ → ℝ) (M : ℕ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  (1 - (t - tSeq a (segIdx a t)) / a (segIdx a t)) •
      (∑ m ∈ Finset.range (segIdx a t), a m • M (m + 1)) +
    ((t - tSeq a (segIdx a t)) / a (segIdx a t)) •
      (∑ m ∈ Finset.range (segIdx a t + 1), a m • M (m + 1))

end ApproxVI


