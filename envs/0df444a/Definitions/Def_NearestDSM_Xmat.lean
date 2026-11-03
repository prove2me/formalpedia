-- Prove2me | Definitions.Def_NearestDSM_Xmat
-- name    : NearestDSM_Xmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:11.112418+00:00
-- url     : https://prove2.me/theorems/65cd3245-7c5e-43af-965f-206df9910efe
-- title:
--   The primal matrix $X=\mathrm{Mat}(\hat x+A^Ty)_+$
-- statement:
--   For $y\in\mathbb R^{2n-1}$ the primal matrix attached to $y$ is the entrywise positive part
--   $$
--   X=\mathrm{Mat}(\hat x+A^Ty)_+,\qquad X_{ij}=\max\{Y_{ij},0\},
--   $$
--   the projection of $Y=\mathrm{Mat}(\hat x+A^Ty)$ onto the nonnegative orthant.
--
--   By Theorem 1.1, $X$ is the nearest doubly stochastic matrix exactly when $F(y)=0$.
--
--   **Formalization Note** The paper's $n$ is $n+1$; the positive part is `max · 0`.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (2.4) p.7, (3.5) p.14

import Mathlib
import Definitions.Def_NearestDSM_Ymat

namespace NearestDSM

/-- `X = Mat(x̂ + Aᵀy)₊`, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, (2.4), p.7 and (3.5), p.14: the entrywise
positive part of `Y = Mat(x̂ + Aᵀy)`, i.e. its metric projection onto the nonnegative orthant (p.4).

**Formalization Note.** The positive part is `max · 0`. -/
noncomputable def Xmat {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun a b => max (Ymat Xh y a b) 0

end NearestDSM


