-- Prove2me | Definitions.Def_NearestDSM_Ymat
-- name    : NearestDSM_Ymat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:30.110578+00:00
-- url     : https://prove2.me/theorems/be46ba6f-5fc8-4caf-bb25-1b25faffbef9
-- title:
--   The matrix $Y=\mathrm{Mat}(\hat x+A^Ty)$
-- statement:
--   Throughout the paper a matrix $\hat X\in\mathbb R^{n\times n}$ is given, with $\hat x=\mathrm{vec}(\hat X)$. For a dual vector $y\in\mathbb R^{2n-1}$ define
--   $$
--   Y=\mathrm{Mat}(\hat x+A^Ty)\in\mathbb R^{n\times n}.
--   $$
--   By the structure of $A$, its entries are
--   $$
--   Y_{ij}=\begin{cases}\hat X_{ij}+r_i+c_j,& i\ne n,\\ \hat X_{ij}+c_j,& i=n.\end{cases}
--   $$
--   Nothing is assumed about $\hat X$.
--
--   The signs of the entries of $Y$ decide everything that follows: the primal point, the generalized Jacobian and the equivalence classes.
--
--   **Formalization Note** The paper's $n$ is $n+1$. The definition is the literal $\hat X+\mathrm{Mat}(A^Ty)$; the entrywise formula above is proved in the mission's verification file.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, p.3 (standing data X̂), (2.4) p.7, (3.5) p.14

import Mathlib
import Definitions.Def_NearestDSM_Dual
import Definitions.Def_NearestDSM_Amat
open Matrix

namespace NearestDSM

/-- `Y = Mat(x̂ + Aᵀy)`, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, (3.5), p.14, for the given matrix `X̂ = Xh`
(p.3: "Throughout this paper we assume we are given a matrix X̂ ∈ ℝ^{n×n}") and a dual vector `y`.

By the structure of `A`, entry `(a, b)` equals `X̂_{ab} + r_a + c_b` for a row `a` other than the
last one, and `X̂_{ab} + c_b` for the last row (display (2.4), p.7); this is checked in the
verification file.

**Formalization Note.** The paper's size `n` is `n + 1`; `x̂ = vec(X̂)` is `Xh` read on index
pairs. -/
def Ymat {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun a b => Xh a b + ((Amat n)ᵀ *ᵥ WithLp.ofLp y) (a, b)

end NearestDSM


