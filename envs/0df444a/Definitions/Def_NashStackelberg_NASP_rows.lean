-- Prove2me | Definitions.Def_NashStackelberg_NASP_rows
-- name    : NashStackelberg_NASP_rows
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:30.635266+00:00
-- url     : https://prove2.me/theorems/f9544dd2-3f6d-485e-8db7-5b30a3d67894
-- title:
--   The number $|\mathcal C^i|$ of complementarity conditions of a NASP player
-- statement:
--   The followers' problems of player $i$ are convex quadratic programs with linear constraints, so $\mathrm{SOL}(P^i(w^i))$ is described by their KKT conditions, with one complementarity condition $0\le\lambda_j\perp(b-Aw-By)_j\ge0$ per constraint row. The number of these conditions is
--   $$
--   |\mathcal C^i|=\sum_{k} r^i_k ,
--   $$
--   the total number of constraint rows of player $i$'s followers. The paper bounds the number of complementarity polyhedra of player $i$ by $2^{|\mathcal C^i|}$.
--
--   **Formalization Note** The count refers to the KKT system of the followers' problems as encoded in `FollowerGame`, one multiplier per row of $A_k w+B_k y_k\le b_k$.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, eq. (3), p.10, and p.11

import Mathlib
import Definitions.Def_NashStackelberg_NASP

namespace NashStackelberg

/-- **The number `|𝓒ⁱ|` of complementarity conditions of player `i`** (Carvalho, Dragotto, Feijoo,
Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, eq. (3), p.10, and
p.11: "𝓒ⁱ the set of indices for the complementarity conditions 0 ≤ xⁱⱼ ⊥ zⁱⱼ ≥ 0 describing
SOL(P(wⁱ))").

The followers' problems are convex quadratic programs with linear constraints, so `SOL(P(wⁱ))` is
described by their KKT conditions, with one complementarity condition per constraint row of a
follower. `|𝓒ⁱ|` is the total number of constraint rows of player `i`'s followers.

**Formalization Note.** The count is that of the KKT system of the followers' problems as encoded
in `FollowerGame` (one multiplier per row `Aₖ w + Bₖ yₖ ≤ bₖ`). -/
def NASP.rows {n : ℕ} (N : NASP n) (i : Fin n) : ℕ :=
  ∑ k, (N.P i).r k

end NashStackelberg


