-- Prove2me | Definitions.Def_NearestDSM_shiftVec
-- name    : NearestDSM_shiftVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:38.895202+00:00
-- url     : https://prove2.me/theorems/3566ed6e-c7af-4d24-8ebf-8300ba1ed076
-- title:
--   The shift direction $w$ of a set of rows $R$ and columns $C$
-- statement:
--   For a set $R$ of rows and a set $C$ of columns, define $w\in\mathbb R^{2n-1}$ by
--   $$
--   w_i=-1\ \ (i\in C),\qquad w_{n+i}=1\ \ (i\in R),
--   $$
--   and all other entries $0$. Moving from $y$ to $y+tw$ subtracts $t$ from the column multipliers $c_j$, $j\in C$, and adds $t$ to the row multipliers $r_i$, $i\in R$; it leaves the entries of $\hat x+A^Ty$ in rows $R$ and columns $C$ unchanged.
--
--   The columns $u^k$ of the matrix $U$ in (3.6)–(3.7) and the direction (3.12) used to find vertices are of this form.
--
--   **Formalization Note** The last row has no multiplier, so whether it belongs to $R$ does not affect $w$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (3.7) p.16, (3.12) p.20

import Mathlib
import Definitions.Def_NearestDSM_Dual

namespace NearestDSM

/-- The shift direction attached to a set `R` of rows and a set `C` of columns, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1,
displays (3.7), p.16 and (3.12), p.20: `w_i = −1` for `i ∈ C` and `w_{n+i} = 1` for `i ∈ R`, all
other entries `0`. Adding `t w` to `y` subtracts `t` from the column multipliers of `C` and adds
`t` to the row multipliers of `R`.

**Formalization Note.** Coordinate `Sum.inl j` is `c_j`, coordinate `Sum.inr i` is `r_i`, the
multiplier of row `Fin.castSucc i` (`Dual`). The last row `Fin.last n` has no coordinate, so its
membership in `R` does not affect the vector. -/
noncomputable def shiftVec {n : ℕ} (R C : Set (Fin (n + 1))) : Dual n :=
  open Classical in
  WithLp.toLp 2 fun i =>
    Sum.elim (fun j => if j ∈ C then (-1 : ℝ) else 0)
      (fun r => if Fin.castSucc r ∈ R then (1 : ℝ) else 0) i

end NearestDSM


