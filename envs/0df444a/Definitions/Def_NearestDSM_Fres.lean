-- Prove2me | Definitions.Def_NearestDSM_Fres
-- name    : NearestDSM_Fres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:07.052965+00:00
-- url     : https://prove2.me/theorems/8769c564-e287-4b0e-81e6-82c4f5167e8c
-- title:
--   The optimality-condition function $F(y)=A(\hat x+A^Ty)_+-b$
-- statement:
--   Let $b\in\mathbb R^{2n-1}$ be the all-ones vector. The optimality conditions of the nearest doubly stochastic matrix problem are the nonsmooth system $F(y)=0$ in $y\in\mathbb R^{2n-1}$, where
--   $$
--   F(y):=A(\hat x+A^Ty)_+-b .
--   $$
--   Its column-$j$ coordinate is the $j$-th column sum of $X=\mathrm{Mat}(\hat x+A^Ty)_+$ minus one, and its row-$i$ coordinate ($i\le n-1$) is the $i$-th row sum of $X$ minus one.
--
--   The modified semismooth Newton method of the paper solves this system.
--
--   **Formalization Note** The paper's $n$ is $n+1$; the value lies in the Euclidean space of dual vectors.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (1.5) p.4, (2.5) p.8

import Mathlib
import Definitions.Def_NearestDSM_Xmat
open Matrix

namespace NearestDSM

/-- The optimality-condition function `F(y) := A(x̂ + Aᵀy)₊ − b`, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, (1.5), p.4
and (2.5), p.8, where `b ∈ ℝ^{2n−1}` is the all-ones vector. Its `Sum.inl j` coordinate is the
`j`-th column sum of `X = Mat(x̂ + Aᵀy)₊` minus one, and its `Sum.inr i` coordinate is the sum of
row `Fin.castSucc i` minus one.

**Formalization Note.** The paper's size `n` is `n + 1`; the value lies in `Dual n` with its
Euclidean norm. -/
noncomputable def Fres {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) : Dual n :=
  WithLp.toLp 2 (Amat n *ᵥ (fun p => Xmat Xh y p.1 p.2) - 1)

end NearestDSM


