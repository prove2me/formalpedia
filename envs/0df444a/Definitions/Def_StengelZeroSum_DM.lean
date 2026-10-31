-- Prove2me | Definitions.Def_StengelZeroSum_DM
-- name    : StengelZeroSum_DM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:50.62889+00:00
-- url     : https://prove2.me/theorems/597d4606-c77d-41a4-a488-bf79b8b75923
-- title:
--   The game $D_M$ of (60)
-- statement:
--   For a $k\times k$ matrix $C$, a vector $d\in\mathbb R^k$ and $M\in\mathbb R$, the zero-sum game
--
--   $$
--   D_M=\begin{bmatrix} C & -d\\ d^\top & 0\\ \mathbf 1^\top & -M\end{bmatrix}
--   $$
--
--   with $k+2$ rows (strategies $(q,r,s)$ of the maximizing row player) and $k+1$ columns (strategies $(z,t)$ of the minimizing column player). For $C$, $d$ of (57) it is the game $B_M$ of (51).
--
--   **Formalization Note** The $k$ coordinates are an arbitrary finite type $\iota$; columns are $\iota\oplus\mathrm{Unit}$ and rows $(\iota\oplus\mathrm{Unit})\oplus\mathrm{Unit}$.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 8, eq. (60), p.21

import Mathlib

namespace StengelZeroSum

/-- The zero-sum game `D_M` of (60),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 8,
eq. (60), p.21: for `C ∈ ℝ^{k×k}`, `d ∈ ℝ^k` and `M ∈ ℝ`,
```
D_M = [ C   −d ]
      [ d⊤   0 ]
      [ 1⊤  −M ]
```

**Formalization Note** The `k` coordinates form an arbitrary finite type `ι`. The columns
`ι ⊕ Unit` are `(z, t)`; the rows `(ι ⊕ Unit) ⊕ Unit` are `(q, r, s)`: `.inl (.inl i)` is row
`i` of `[C, −d]`, `.inl (.inr ())` is the row `[d⊤, 0]` and `.inr ()` is the row `[1⊤, −M]`. -/
def DM {ι : Type*} (C : Matrix ι ι ℝ) (d : ι → ℝ) (M : ℝ) :
    Matrix ((ι ⊕ Unit) ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.of fun r s =>
    match r, s with
    | .inl (.inl i), .inl j => C i j
    | .inl (.inl i), .inr _ => -d i
    | .inl (.inr _), .inl j => d j
    | .inl (.inr _), .inr _ => 0
    | .inr _, .inl _ => 1
    | .inr _, .inr _ => -M

end StengelZeroSum


