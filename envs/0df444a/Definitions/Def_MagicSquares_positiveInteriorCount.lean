-- Prove2me | Definitions.Def_MagicSquares_positiveInteriorCount
-- name    : MagicSquares_positiveInteriorCount
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-20T21:15:31.343662+00:00
-- url     : https://prove2.me/theorems/f59f75e2-2a90-4fd2-8d09-f787ccdc5fce
-- title:
--   Interior (positive) semi-magic counting function
-- statement:
--   For order $n$ and line sum $t$, let $I_{n}(t)$ be the number of semi-magic squares with nonnegative integer entries, line sum $t$, and every entry strictly positive. In other words, $$I_{n}(t) = |\{M : \text{every row and column sums to } t,\ M_{ij} \ge 1\ \forall i,j\}|,$$ counted, as with $H_{n}$, over arrays with entries in $\{0,\dots,t\}$ (which loses nothing since every entry of a line-sum-$t$ square is at most $t$).
--
--   These are exactly the interior lattice points of the dilated Birkhoff polytope $t \cdot B_{n}$: dilating the polytope of doubly stochastic matrices and counting interior integral points. The count is the bridge between the Ehrhart--Macdonald reciprocity law, which evaluates the Ehrhart polynomial at negative integers in terms of interior points, and the elementary shift bijection $M \mapsto M - J$ that identifies positive squares of line sum $t$ with ordinary squares of line sum $t - n$.
--
--   **Formalization Note** Lean counts over `Square n (Fin (t+1))` with positivity stated as `1 ≤ (M i j : ℕ)` for the `Fin`-valued entries coerced to naturals, mirroring `semiMagicCount`.
-- source:
--   R. P. Stanley, Duke Math. J. 40 (1973), 607--632 (interior lattice points of the Birkhoff polytope); M. Beck, M. Cohen, J. Cuomo and P. Gribelyuk, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013).

import Definitions.Def_MagicSquares

set_option autoImplicit false

namespace MagicSquares

/-- The interior count: semi-magic squares of order `n` and line sum `t` with every entry positive. -/
noncomputable def positiveInteriorCount (n t : ℕ) : ℕ :=
  by classical exact (Finset.univ.filter (fun M : Square n (Fin (t + 1)) =>
    IsSemiMagic (fun i j => (M i j : ℕ)) t ∧ ∀ i j, 1 ≤ (M i j : ℕ))).card

end MagicSquares


