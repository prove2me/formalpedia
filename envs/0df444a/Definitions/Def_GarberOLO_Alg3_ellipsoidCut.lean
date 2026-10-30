-- Prove2me | Definitions.Def_GarberOLO_Alg3_ellipsoidCut
-- name    : GarberOLO_Alg3_ellipsoidCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:57.797821+00:00
-- url     : https://prove2.me/theorems/0d56588f-c9b8-463d-a311-b6a1c788a2c8
-- title:
--   One central-cut step of the Ellipsoid method
-- statement:
--   An Ellipsoid state $(w, A)$, with $w \in \mathbb R^d$ and $A$ a positive definite $d\times d$ matrix, represents $E = \{z : (z-w)^\top A^{-1}(z-w) \le 1\}$. A **cut** with a vector $g$ keeps the half-space $\{z : g\cdot(z - w) \le 0\}$ and replaces $E$ by the smallest ellipsoid containing the kept half:
--
--   1. if $g = 0$, the state is unchanged;
--   2. otherwise let $b = Ag/\sqrt{g^\top A g}$; for $d = 1$ the new state is $(w - b/2,\ A/4)$ (bisection); for $d \ne 1$ it is
--   $$\Big(w - \frac{b}{d+1},\ \ \frac{d^2}{d^2-1}\Big(A - \frac{2}{d+1}\, b b^\top\Big)\Big).$$
--
--   This is the central-cut Ellipsoid method of Bubeck's monograph (the paper's reference [5]), on which Lemma 5's procedure runs.
--
--   **Formalization Note** The paper does not restate the method. The two degenerate cases ($d = 1$, where the standard formula divides by zero, and $g = 0$) are fixed as above; for $d = 0$ every vector is $0$ and the step is irrelevant.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, p. 9 ("the Ellipsoid method [10, 5]"); Bubeck, Convex Optimization: Algorithms and Complexity, §2.2

import Mathlib

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

/-- **One central-cut step of the Ellipsoid method** (Lemma 5, Reading 1).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, p. 9: "Consider an attempt to apply the Ellipsoid method for N iterations …
use v − x as a separating hyperplane for the Ellipsoid method … use w as a separating hyperplane
for the Ellipsoid method". The paper cites the Ellipsoid method of its references [10, 5]
(Bubeck, *Convex Optimization: Algorithms and Complexity*, §2.2) without restating it.

A state `(w, A)` stands for the ellipsoid `{z | (z − w)ᵀ A⁻¹ (z − w) ≤ 1}` with center `w` and
positive definite shape matrix `A`. `ellipsoidCut (w, A) g` is the state after the cut with the
vector `g`, which keeps the half-space `{z | ⟪g, z − w⟫ ≤ 0}`:
* if `g = 0`, the state is unchanged;
* otherwise, with `b := A g / √(gᵀ A g)`,
  * for `d = 1`: `(w − b/2, A/4)` (bisection: the half-interval is its own minimal ellipsoid);
  * for `d ≠ 1`: `(w − b/(d+1), d²/(d²−1) · (A − 2/(d+1) · b bᵀ))`, the standard central-cut update.

**Formalization Note.** (Reading 1 of the mission.) The paper does not spell out the method; this
is the central-cut Ellipsoid method of its reference, with two degenerate cases fixed: for
`d = 1` the standard formula divides by `d² − 1 = 0` and is replaced by bisection; a zero cut
vector (which arises only when the oracle returns `v = x`) leaves the ellipsoid unchanged. For
`d = 0` the general branch applies; every vector is `0` there, so the step is irrelevant.
`A g` is `Matrix.toEuclideanLin A g` and `gᵀ A g` is `⟪g, A g⟫`. -/
noncomputable def ellipsoidCut {d : ℕ}
    (st : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ) (g : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ :=
  if g = 0 then st
  else
    let b : EuclideanSpace ℝ (Fin d) :=
      (Real.sqrt ⟪g, Matrix.toEuclideanLin st.2 g⟫)⁻¹ • Matrix.toEuclideanLin st.2 g
    if d = 1 then
      (st.1 - (1 / 2 : ℝ) • b, (1 / 4 : ℝ) • st.2)
    else
      (st.1 - (1 / ((d : ℝ) + 1)) • b,
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) •
          (st.2 - (2 / ((d : ℝ) + 1)) • Matrix.vecMulVec (fun i => b i) (fun i => b i)))

end GarberOLO.Alg3


