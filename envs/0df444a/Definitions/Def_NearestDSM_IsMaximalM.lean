-- Prove2me | Definitions.Def_NearestDSM_IsMaximalM
-- name    : NearestDSM_IsMaximalM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:24.935312+00:00
-- url     : https://prove2.me/theorems/cd36b0e1-78fd-4a83-ac08-f951738589ee
-- title:
--   Maximal matrices $M\in\mathcal M(y)$
-- statement:
--   A matrix $M\in\mathcal M(y)$ is **maximal** for $y$ if
--   $$
--   (\hat x+A^Ty)_{ij}\ge 0\ \Longrightarrow\ M_{ij}=1 .
--   $$
--   Since $M\in\mathcal M(y)$ also forces $M_{ij}=0$ where $(\hat x+A^Ty)_{ij}<0$, the maximal matrix is unique: it is the $0$–$1$ indicator of the entries where $\hat x+A^Ty$ is nonnegative. The corresponding $V(M)$ is called the maximal element of $\partial F(y)$.
--
--   **Formalization Note** The paper's $n$ is $n+1$. Uniqueness (the predicate holds exactly for `Mmax`) is proved in the verification file.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, display (3.9), p.17

import Mathlib
import Definitions.Def_NearestDSM_Mset

namespace NearestDSM

/-- A matrix `M ∈ M(y)` is **maximal** for `y`, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, display (3.9), p.17, if
`(x̂ + Aᵀy)_{ij} ≥ 0 ⟹ M_{ij} = 1`.

**Formalization Note.** Together with `M ∈ M(y)` this determines `M`: it is `Mmax Xh y`
(checked in the verification file). The paper's size `n` is `n + 1`. -/
def IsMaximalM {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  M ∈ Mset Xh y ∧ ∀ a b, 0 ≤ Ymat Xh y a b → M a b = 1

end NearestDSM


