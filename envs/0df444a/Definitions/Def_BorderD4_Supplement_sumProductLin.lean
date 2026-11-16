-- Prove2me | Definitions.Def_BorderD4_Supplement_sumProductLin
-- name    : BorderD4_Supplement_sumProductLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:01:03.726711+00:00
-- url     : https://prove2.me/theorems/d82c558a-8c84-402f-b60a-9f3d00b1a52a
-- title:
--   $P_{k+1,n}$ in the variables $x_1,\dots,x_{(k+1)n}$
-- statement:
--   For $k\ge 0$ and $n\ge 1$, with $N=(k+1)n$ variables $x_1,\dots,x_N$,
--   $$P_{k+1,n}=\sum_{j=1}^{k+1}\prod_{t=(j-1)n+1}^{jn}x_t,$$
--   so that the first block is $x_1,\dots,x_n$. This is the published sum-product polynomial with its variables listed in one row, the indexing that Theorem 5.3 uses.
--
--   **Formalization Note** It is the image of `BorderD4.sumProduct` (variables $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$) under $(j,t)\mapsto t+nj$; the variable $x_i$ is the index $i-1$ of $\mathrm{Fin}\,N$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 1.2, p.4

import Mathlib
import Definitions.Def_BorderD4_sumProduct
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- The sum-product polynomial `P_{k+1,n} = ∑_{j=1}^{k+1} ∏_{t=(j−1)n+1}^{jn} x_t` in the linearly indexed variables
`x_1, …, x_N`, `N = (k+1)n`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 1.2, p.4.

**Formalization Note** The published `BorderD4.sumProduct` indexes the variables by `Fin (k+1) × Fin n`; this is its
image under `finProdFinEquiv : (j, t) ↦ t + n·j`, so the variables are `Fin ((k+1)*n)`, the page's `x_i` is the
index `i − 1`, and block `j` (1-based) is the indices `(j−1)n, …, jn − 1`. In particular the first block
`x_1, …, x_n` is the indices `0, …, n − 1`, as Theorem 5.3 needs. -/
noncomputable def sumProductLin (F : Type*) [Field F] (k n : ℕ) : MvPolynomial (Fin ((k + 1) * n)) F :=
  rename finProdFinEquiv (sumProduct F k n)

end BorderD4.Supplement


