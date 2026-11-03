-- Prove2me | Definitions.Def_NearestDSM_Mset
-- name    : NearestDSM_Mset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:17.160613+00:00
-- url     : https://prove2.me/theorems/76837758-7404-4a87-a9ac-1cfebe4249a9
-- title:
--   The set $\mathcal M(y)$ of admissible $0$–$1$ weights
-- statement:
--   For $y\in\mathbb R^{2n-1}$, the set $\mathcal M(y)$ consists of the matrices $M\in\mathbb R^{n\times n}$ with
--   $$
--   M_{ij}=\begin{cases}1,&(\hat x+A^Ty)_{ij}>0,\\ \text{any value in }[0,1],&(\hat x+A^Ty)_{ij}=0,\\ 0,&(\hat x+A^Ty)_{ij}<0.\end{cases}
--   $$
--   It records the possible slopes of the positive part at each entry, and parametrizes the generalized Jacobian of $F$.
--
--   **Formalization Note** The paper's $n$ is $n+1$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (2.6), p.8

import Mathlib
import Definitions.Def_NearestDSM_Ymat

namespace NearestDSM

/-- The set `M(y)` of Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (2.6), p.8: the matrices `M ∈ ℝ^{n×n}` with
`M_{ij} = 1` if `(x̂ + Aᵀy)_{ij} > 0`, `M_{ij} ∈ [0, 1]` if `(x̂ + Aᵀy)_{ij} = 0`, and `M_{ij} = 0`
if `(x̂ + Aᵀy)_{ij} < 0`.

**Formalization Note.** The paper's size `n` is `n + 1`. -/
def Mset {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) :
    Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {M | ∀ a b, (0 < Ymat Xh y a b → M a b = 1) ∧ (Ymat Xh y a b = 0 → M a b ∈ Set.Icc (0 : ℝ) 1) ∧
    (Ymat Xh y a b < 0 → M a b = 0)}

end NearestDSM


