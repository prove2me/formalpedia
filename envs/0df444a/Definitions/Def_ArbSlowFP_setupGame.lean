-- Prove2me | Definitions.Def_ArbSlowFP_setupGame
-- name    : ArbSlowFP_setupGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:45:54.154194+00:00
-- url     : https://prove2.me/theorems/5845d235-5ca5-4918-97d2-312981fc6297
-- title:
--   Setup game (22)
-- statement:
--   For $A\in\mathbb Q^{m\times m}$ and a score vector $g$ (in the paper $g=f+\beta$), put $f^\star=g+(1-\min_ig_i)\mathbf 1_m\ge\mathbf 1_m$ and
--   $$\hat A=\begin{pmatrix}0&-(f^\star)^\top\\f^\star&A\end{pmatrix},$$
--   with the setup action listed first. The setup action's payoff column gives the required initial scores from zero counts.
--
--   **Formalization Note** The action type is `Option ι`, with the setup action `none`.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.30, eq. (22)

import Mathlib

open Matrix

namespace ArbSlowFP

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The smallest entry `min_i g_i`, used in (22), p.30. -/
def minEntry (g : ι → ℚ) : ℚ := Finset.univ.inf' Finset.univ_nonempty g

/-- `f⋆ = g + (1 - min_i g_i) 1_m ≥ 1_m` of (22), p.30, with `g = f + β`. -/
def setupVec (g : ι → ℚ) : ι → ℚ := fun i => g i + (1 - minEntry g)

/-- The game of (22), p.30, with one additional setup action: `Â = [[0, -(f⋆)⊤], [f⋆, A]]`. The setup
action is `none`, and the recurrent actions are `some i`. -/
def setupGame (A : Matrix ι ι ℚ) (g : ι → ℚ) : Matrix (Option ι) (Option ι) ℚ :=
  Matrix.of fun x y =>
    match x, y with
    | none, none => 0
    | none, some j => -setupVec g j
    | some i, none => setupVec g i
    | some i, some j => A i j

end ArbSlowFP


