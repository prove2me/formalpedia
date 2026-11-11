-- Prove2me | Definitions.Def_NCQuadLB_pal
-- name    : NCQuadLB_pal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:22.993837+00:00
-- url     : https://prove2.me/theorems/7bcbdd01-62a6-4b6b-bfb8-110122521748
-- title:
--   The palindrome polynomial $\mathrm{Pal}_{n,d}(X,Y)$
-- statement:
--   Let $\mathbb F$ be a field and let $X=\{x_1,\dots,x_n\}$, $Y=\{y_1,\dots,y_n\}$ be disjoint sets of noncommuting variables. The **palindrome polynomial** is
--
--   $$
--   \mathrm{Pal}_{n,d}(X,Y)=\sum_{(i_1,\dots,i_d)\in[n]^d}\Bigl(\prod_{j=1}^d x_{i_j}\Bigr)\Bigl(\prod_{j=1}^d y_{i_{d+1-j}}\Bigr)\in\mathbb F\langle X,Y\rangle,
--   $$
--
--   the sum of the words $x_{i_1}\cdots x_{i_d}\,y_{i_d}\cdots y_{i_1}$. The module also names the monomial $x_{i_1}\cdots x_{i_d}$ of an index tuple.
--
--   It is the explicit polynomial of the lower bound: it has circuits of size $O(nd)$, and the mission shows that this is optimal.
--
--   **Formalization Note** $\mathbb F\langle X,Y\rangle$ is the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, with $x_j$ the left and $y_j$ the right copy of $j$; indices start at $0$. The $Y$-word is reversed ($y_{i_d}\cdots y_{i_1}$).
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), §1, p.2

import Mathlib

namespace NCQuadLB

/-- The monomial `x_{i_1} x_{i_2} ⋯ x_{i_d}` of `F⟨X, Y⟩` for an index tuple `i = (i_1, …, i_d)`, with
`X = {x_j}` the variables `Sum.inl j`. -/
noncomputable def xMonomial (F : Type*) [CommSemiring F] {n d : ℕ} (i : Fin d → Fin n) :
    FreeAlgebra F (Fin n ⊕ Fin n) :=
  (List.ofFn fun j => FreeAlgebra.ι F (Sum.inl (i j) : Fin n ⊕ Fin n)).prod

/-- The reversed monomial `y_{i_d} y_{i_{d-1}} ⋯ y_{i_1}` of `F⟨X, Y⟩`, with `Y = {y_j}` the variables
`Sum.inr j`. -/
noncomputable def yMonomialRev (F : Type*) [CommSemiring F] {n d : ℕ} (i : Fin d → Fin n) :
    FreeAlgebra F (Fin n ⊕ Fin n) :=
  (List.ofFn fun j => FreeAlgebra.ι F (Sum.inr (i (Fin.rev j)) : Fin n ⊕ Fin n)).prod

/-- The **palindrome polynomial** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative
Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, §1, p.2):
`Pal_{n,d}(X, Y) = ∑_{(i_1,…,i_d) ∈ [n]^d} (∏_{j=1}^d x_{i_j}) (∏_{j=1}^d y_{i_{d+1-j}})`
in `F⟨X, Y⟩`, `X = {x_1,…,x_n}`, `Y = {y_1,…,y_n}`.

**Formalization Note** `F⟨X, Y⟩` is `FreeAlgebra F (Fin n ⊕ Fin n)`: `x_j` is `ι (Sum.inl j)` and
`y_j` is `ι (Sum.inr j)`, with 0-based indices. The products are taken in index order, so the
`Y`-word is `y_{i_d} ⋯ y_{i_1}` (`Fin.rev`). -/
noncomputable def pal (F : Type*) [CommSemiring F] (n d : ℕ) : FreeAlgebra F (Fin n ⊕ Fin n) :=
  ∑ i : Fin d → Fin n, xMonomial F i * yMonomialRev F i

end NCQuadLB


