-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_weightGap
-- name    : MatrixLeeSidford_Supplement_weightGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:11:56.226473+00:00
-- url     : https://prove2.me/theorems/4ec481af-aa4b-42a0-ae25-21947bdcf142
-- title:
--   Weight gap $\Delta_y(G)=f_y(G)-f_y(G_*(y))$
-- statement:
--   Let $y$ be a feasible dual point, $S=S(y)\succ0$, and let $f_y(G)=\frac1s\operatorname{tr}[L_y(G)^s]-\log\det G-m$ be the Lewis-weight objective at $y$, minimized over $G\succ0$ by the optimal weight $G_*(y)$. The **weight gap** of a weight $G\succ0$ is
--   $$
--   \Delta_y(G):=f_y(G)-f_y(G_*(y))\ \ge 0 .
--   $$
--   A weight is **accurate** at $y$ if $\Delta_y(G)\le\eta$ and **warm** if $\Delta_y(G)\le\eta_w$, with $\eta\le\eta_w$ fixed in (8.11).
--
--   The gap measures how far the weight maintained by the algorithm is from the optimal weight that defines the barrier.
--
--   **Formalization Note** $f_y$ and $G_*(y)$ are the base mission's published objective and optimal weight (a chosen minimizer). The trace power $s$ is a parameter; Part II takes $s=2\lceil\log(2mn)\rceil$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 8.1, p.53

import Mathlib
import Definitions.Def_MatrixLeeSidford_fObj
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_MatrixLeeSidford_slack

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **weight gap** `Δ_y(G) := f_y(G) − f_y(G_*(y))` of a weight `G ≻ 0` at a feasible point `y`
(Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 8.1, p.53). A weight is *accurate* at `y` if `Δ_y(G) ≤ η` and *warm* if
`Δ_y(G) ≤ η_w` (p.53).

**Formalization Note** `f_y` is the published `fObj` at the slack `S(y)` and `G_*(y)` the published
`optWeightAt` (a chosen minimizer of `f_y` over `G ≻ 0`, Theorem 2.1(a)). The trace power `s` is a
parameter; Part II uses `s = sParam m n` (Definition 5.1). -/
noncomputable def weightGap {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (y : EuclideanSpace ℝ (Fin m))
    (G : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  fObj A (slack A C y) s G - fObj A (slack A C y) s (optWeightAt A C s y)

end MatrixLeeSidford.Supplement


