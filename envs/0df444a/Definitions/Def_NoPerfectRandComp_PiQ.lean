-- Prove2me | Definitions.Def_NoPerfectRandComp_PiQ
-- name    : NoPerfectRandComp_PiQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:36.856012+00:00
-- url     : https://prove2.me/theorems/c938f0dd-5e21-40c3-bb14-87085e77a84b
-- title:
--   The pointer predicate $\Pi_q$
-- statement:
--   An input is a $q\times q$ array $x$ of pointer cells, $x_{i,j}$ in row $i$ and column $j$. The **pointer predicate** $\Pi_q(x)$ is one precisely when there are a cell $(i^*, j^*)$ and rows $\ell_j \in [q]$ such that
--   1. every value bit in column $j^*$ is one;
--   2. if $i \ne i^*$ and $j \ne j^*$, then $\mathrm{row}_j(x_{i,j^*}) = \bot$;
--   3. for every $j \ne j^*$, $\mathrm{row}_j(x_{i^*,j^*}) = \ell_j$ and $v(x_{\ell_j,j}) = 0$;
--   4. exactly $(q-1)/2$ columns $j \ne j^*$ satisfy $\mathrm{col}(x_{\ell_j,j}) = j^*$ and $\mathrm{row}_{j^*}(x_{\ell_j,j}) = i^*$.
--
--   All other fields are unrestricted; the predicate is zero on every other array. A one-input is certified by its special column and the cells it links to.
--
--   **Formalization Note** $(q-1)/2$ is natural-number division, exact at odd $q$, which is the case wherever $\Pi_q$ is used. The value of $\ell$ at $j^*$ is unused.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §5.1, p.18

import Mathlib
import Definitions.Def_NoPerfectRandComp_PtrCell

namespace NoPerfectRandComp

/-- The pointer predicate `Π_q` on a `q × q` array of pointer cells (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §5.1, p.18).
`Π_q(x) = 1` precisely when there are a cell `(i*, j*)` and rows `ℓ_j ∈ [q]` with
(i) every value bit in column `j*` one; (ii) `row_j(x_{i,j*}) = ⊥` whenever `i ≠ i*` and
`j ≠ j*`; (iii) for every `j ≠ j*`, `row_j(x_{i*,j*}) = ℓ_j` and `v(x_{ℓ_j, j}) = 0`; (iv) exactly
`(q − 1)/2` columns `j ≠ j*` satisfy `col(x_{ℓ_j, j}) = j*` and `row_{j*}(x_{ℓ_j, j}) = i*`.

**Formalization Note** Cells are indexed `(row i, column j)`. `ℓ` is a function `[q] → [q]`
whose value at `j*` is unused. `(q − 1)/2` is natural-number division, exact for odd `q`, which is
the case wherever `Π_q` is used. -/
def PiQ (q : ℕ) (x : Fin q × Fin q → PtrCell q) : Bool :=
  decide (∃ (is js : Fin q) (ℓ : Fin q → Fin q),
    (∀ i, (x (i, js)).1 = true) ∧
    (∀ i, i ≠ is → ∀ j, j ≠ js → (x (i, js)).2.1 j = none) ∧
    (∀ j, j ≠ js → (x (is, js)).2.1 j = some (ℓ j) ∧ (x (ℓ j, j)).1 = false) ∧
    (Finset.univ.filter (fun j => j ≠ js ∧ (x (ℓ j, j)).2.2 = some js ∧
      (x (ℓ j, j)).2.1 js = some is)).card = (q - 1) / 2)

end NoPerfectRandComp


