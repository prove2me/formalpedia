-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_PiecewiseInexact
-- name    : GlobalInexactNewton_Backtracking_Supplement_PiecewiseInexact
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:43:29.456806+00:00
-- url     : https://prove2.me/theorems/95213260-5142-4beb-8ae4-e714f7cc5c1b
-- title:
--   Piecewise affine inexact Newton curves (6.2)
-- statement:
--   At a point $x$, choose a nonempty finite list of steps $v_1,\ldots,v_N$ and levels $1=\ell_0>\ell_1>\cdots>\ell_N=\bar\eta$, with $v_0=0$, $\ell_1\le\eta_{\max}$ and $\|F(x)+F'(x)v_j\|\le\ell_j\|F(x)\|$. On every interval $[\ell_{j+1},\ell_j]$, define
--
--   $$\sigma(\eta)=\frac{\eta-\ell_{j+1}}{\ell_j-\ell_{j+1}}v_j+\frac{\ell_j-\eta}{\ell_j-\ell_{j+1}}v_{j+1}.$$
--
--   This is the paper's extension of straight-line backtracking to a list of inexact Newton steps. Vertex residuals satisfy inequalities, rather than equalities. **Formalization Note** The real norm is arbitrary; finite-dimensionality and continuous differentiability are hypotheses of the theorems. Natural-number lists are used only through index $N$, which is strictly positive. Values outside the curve's domain are immaterial.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 411, Piecewise linear inexact Newton curve (6.2); DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

namespace GlobalInexactNewton.Backtracking.Supplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vertices and affine parametrization in (6.2), including their residual inequalities. -/
def IsPiecewiseInexactCurve (F : E → E) (x : E) (ηmax ηbar : ℝ) (σ : ℝ → E) : Prop :=
  ∃ (N : ℕ) (level : ℕ → ℝ) (v : ℕ → E),
    0 < N ∧ level 0 = 1 ∧ v 0 = 0 ∧ level N = ηbar ∧ level 1 ≤ ηmax ∧
    (∀ j < N, level (j + 1) < level j) ∧
    (∀ j, 1 ≤ j → j ≤ N → InexactNewtonCond F x (v j) (level j)) ∧
    ∀ j < N, ∀ η ∈ Set.Icc (level (j + 1)) (level j),
      σ η = ((η - level (j + 1)) / (level j - level (j + 1))) • v j +
        ((level j - η) / (level j - level (j + 1))) • v (j + 1)

end GlobalInexactNewton.Backtracking.Supplement


