-- Prove2me | Definitions.Def_GarberOLO_Alg3_sdState
-- name    : GarberOLO_Alg3_sdState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:51:30.758718+00:00
-- url     : https://prove2.me/theorems/3947f976-0270-432e-82b6-d0a2c0dc650c
-- title:
--   Ellipsoid states of the Separation-or-Decomposition procedure
-- statement:
--   Fix $x \in \mathbb R^d$ and $\varepsilon > 0$. The procedure of Lemma 5 runs the Ellipsoid method on the feasibility problem
--   $$\text{find } w:\ \ (x - z)\cdot w \ge \varepsilon\ \ \forall z \in \alpha K,\quad \|w\| \le 1. \tag{4}$$
--   It starts from the unit ball $B(0,1)$ (center $0$, shape $I$). At the current center $w$ it computes $(v, s) = \hat{\mathcal O}_K(-w)$ and
--
--   1. if $(x - v)\cdot w < \varepsilon$, cuts with $v - x$;
--   2. else, if $\|w\| > 1$, cuts with $w$;
--   3. otherwise stops (Problem (4) is declared feasible) and the state is kept.
--
--   $\mathrm{sdState}(j)$ is the state at the start of iteration $j = 0, 1, 2, \dots$.
--
--   **Formalization Note** The initial ellipsoid $B(0,1)$ is a reading (the paper does not name it; its proof needs $B(h/2, r) \subset B(0,1) \subseteq E_0$). Keeping the state after a stop is a convention; only the states up to the first stop are used.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, p. 9 (steps 1–3)

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_extOracle
import Definitions.Def_GarberOLO_Alg3_ellipsoidCut

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

/-- **The Ellipsoid states of the Separation-or-Decomposition procedure** (Lemma 5).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, p. 9: "each iteration of the Ellipsoid method applies the following consecutive
steps:
1. (v, s) ← Ô_K(−w), where w is the current iterate. If (x − v) · w < ε, use v − x as a
separating hyperplane for the Ellipsoid method and continue to the next iteration
2. if ‖w‖ > 1, use w as a separating hyperplane for the Ellipsoid method and continue to the
next iteration
3. otherwise (‖w‖ ≤ 1 and (x − v) · w ≥ ε), declare Problem (4) feasible and return the vector w."

`sdState S OK x ε j` is the ellipsoid `(center, shape)` at the start of iteration `j`
(iterations numbered from 0). The initial state is `(0, I)`, the unit ball B(0, 1). At center
`w`, with `v := (extOracle S OK (−w)).1`: if `⟪x − v, w⟫ < ε` the next state is the cut with
`v − x`; else if `1 < ‖w‖` it is the cut with `w`; else (step 3, the procedure stops) the state
is left unchanged.

**Formalization Note.** (Reading 1.) The initial ellipsoid E₀ = B(0, 1) is the ball of
Problem (4)'s constraint ‖w‖ ≤ 1; the paper does not name E₀, and its proof (p. 11) needs
B(h/2, r) ⊂ E₀. Freezing the state after a stop is a convention: `sepOrDec` reads only the
states up to the first stop. -/
noncomputable def sdState {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    ℕ → EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ
  | 0 => (0, 1)
  | j + 1 =>
    let st := sdState S OK x ε j
    let v := (extOracle S OK (-st.1)).1
    if ⟪x - v, st.1⟫ < ε then ellipsoidCut st (v - x)
    else if 1 < ‖st.1‖ then ellipsoidCut st st.1
    else st

end GarberOLO.Alg3


