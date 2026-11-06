-- Prove2me | Definitions.Def_GlobalSinkhorn_scalingRadius
-- name    : GlobalSinkhorn_scalingRadius
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:21:24.544798+00:00
-- url     : https://prove2.me/theorems/24902a77-096e-4c22-a041-0da7e6020531
-- title:
--   The optimal logarithmic scaling radius $D(A;B)$
-- statement:
--   Let $A$ be a nonnegative row-stochastic $n\times n$ matrix and $B$ a doubly stochastic positive diagonal scaling of $A$. The **optimal logarithmic scaling radius** is
--   $$
--   D(A;B)=\min\Big\{\max\{\|u\|_\infty,\|v\|_\infty\}\ :\ u,v\in\mathbb R^n,\ B=\operatorname{diag}(e^{u})\,A\,\operatorname{diag}(e^{-v})\Big\},
--   $$
--   with componentwise exponentials. The minimum runs over all logarithmic representations of the scaling, with no normalization of the diagonal factors. It measures how far the input $A$ must be rescaled to reach its doubly stochastic scaling $B$, and it enters the iteration bound of Theorem 1.1 linearly.
--
--   **Formalization Note** $\|u\|_\infty$ is Mathlib's sup norm on `Fin n → ℝ`, so `max ‖u‖ ‖v‖` is $\|(u,v)\|_\infty$. The minimum is written as an `sInf` over the set of attained values; this set is nonempty when a scaling exists, bounded below by $0$, and its infimum is attained (milestone `GlobalSinkhorn.scalingRadius_attained`). If no scaling exists the `sInf` of the empty set is the junk value $0$; every statement of the mission assumes a scaling exists. Note the sign: $e^{-v}$ multiplies on the right.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Definition 2.1, Eq. (15), p.13

import Mathlib

open Matrix

namespace GlobalSinkhorn

/-- The optimal logarithmic scaling radius
`D(A; B) = min {max(‖u‖∞, ‖v‖∞) : B = diag(eᵘ) A diag(e⁻ᵛ)}`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Definition 2.1, Eq. (15), p.13.

**Formalization Note.** `u v : Fin n → ℝ` carry Mathlib's sup norm, so `max ‖u‖ ‖v‖` is
`‖(u, v)‖∞`. The paper's `min` is an `sInf`: the set is bounded below by `0`, it is nonempty
when `B` is a positive diagonal scaling of `A`, and the infimum is attained
(`GlobalSinkhorn.scalingRadius_attained`). On the empty set (no scaling exists) the `sInf` is
the junk value `0`; every statement of the mission assumes a scaling exists. -/
noncomputable def scalingRadius {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ u v : Fin n → ℝ,
    B = Matrix.diagonal (fun i => Real.exp (u i)) * A *
        Matrix.diagonal (fun j => Real.exp (-v j)) ∧
      r = max ‖u‖ ‖v‖}

end GlobalSinkhorn


