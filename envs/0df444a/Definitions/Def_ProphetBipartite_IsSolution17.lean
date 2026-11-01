-- Prove2me | Definitions.Def_ProphetBipartite_IsSolution17
-- name    : ProphetBipartite_IsSolution17
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.846868+00:00
-- url     : https://prove2.me/theorems/efe50ac6-528c-4e9e-8927-bab3fdf4723a
-- title:
--   The semi-linear system (16)–(17) for the prices
-- statement:
--   Let $M$ and $Q$ be real $n\times m$ matrices, rows indexed by $L$ and columns by $R$, and write $[x]^+=\max\{x,0\}$. Vectors $l\in\mathbb R^L$, $r\in\mathbb R^R$ **solve (17)** when
--
--   $$
--   l_i=\sum_{j\in R}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+\quad\forall i\in L,\qquad
--   r_j=\sum_{i\in L}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+\quad\forall j\in R.
--   $$
--
--   This is system (16), $A^+\mathbb 1_R=L\,\mathbb 1_L$ and $\mathbb 1_L^\top A^+=\mathbb 1_R^\top R$ with $A^+=[M-L\cdot Q-Q\cdot R]^+$, $L=\mathrm{diag}(l)$, $R=\mathrm{diag}(r)$, written entrywise. Its solutions are the prices of Theorem 3.1.
--
--   **Formalization Note** Any solution is nonnegative, each coordinate being a sum of positive parts.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, (16) p.9, (17) p.10

import Mathlib

namespace ProphetBipartite

/-- **The system of semi-linear equations (17) (equivalently (16)).** Gravin & Wang,
arXiv:1902.06243v1, (16) p.9 and (17) p.10: for real `n × m` matrices `M`, `Q` (rows indexed by the
left part `L`, columns by the right part `R`), the vectors `l`, `r` solve

`l_i = ∑_{j=1}^{m} [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺` for every `i`, and
`r_j = ∑_{i=1}^{n} [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺` for every `j`,

where `[x]⁺ = max{x, 0}`. This is (16), `A⁺ 𝟙_R = L 𝟙_L` and `𝟙_Lᵀ A⁺ = 𝟙_Rᵀ R` with
`A⁺ = [M − L·Q − Q·R]⁺`, written entrywise.

**Formalization Note.** `l`, `r` are real vectors; any solution is automatically nonnegative, each
coordinate being a sum of positive parts. -/
def IsSolution17 {L R : Type*} [Fintype L] [Fintype R] (M Q : L → R → ℝ) (l : L → ℝ)
    (r : R → ℝ) : Prop :=
  (∀ i, l i = ∑ j, max (M i j - Q i j * (l i + r j)) 0) ∧
    ∀ j, r j = ∑ i, max (M i j - Q i j * (l i + r j)) 0

end ProphetBipartite


