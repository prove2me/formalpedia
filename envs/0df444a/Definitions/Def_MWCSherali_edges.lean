-- Prove2me | Definitions.Def_MWCSherali_edges
-- name    : MWCSherali_edges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:54.786354+00:00
-- url     : https://prove2.me/theorems/9c24fa8d-36e0-4154-a7e3-89dc712e10a3
-- title:
--   The edge set $E_{k,n}$ of the discrete simplex
-- statement:
--   The edges of the discrete simplex are
--
--   $$E_{k,n}=\Big\{\{x,y\}\;\Big|\;x,y\in\Delta_{k,n},\ \exists\, i\neq j\in[k],\ x=y+\tfrac1n e_i-\tfrac1n e_j\Big\},$$
--
--   the pairs of points at $\ell_1$ distance $2/n$. Non-opposite cut instances are weight functions on $E_{k,n}$.
--
--   **Formalization Note** In integer coordinates the condition reads $x+e_j=y+e_i$ (no truncated subtraction). Edges are unordered pairs.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14 (E_{k,n}); §1.1, p.4

import Mathlib
import Definitions.Def_MWCSherali_Grid

namespace MWCSherali

/-- **The edge set `E_{k,n}` of the discrete simplex.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14:
`E_{k,n} = {{x, y} | x, y ∈ Δ_{k,n}, ∃ i ≠ j ∈ [k], x = y + (1/n)e_i − (1/n)e_j}`.

**Formalization Note.** In integer coordinates the condition `x = y + e_i/n − e_j/n` reads
`x + e_j = y + e_i` as vectors of natural numbers (no truncated subtraction). Edges are unordered
pairs, elements of `Sym2 (Grid k n)`. -/
def edges (k n : ℕ) : Finset (Sym2 (Grid k n)) :=
  ((Finset.univ : Finset (Grid k n × Grid k n)).filter fun p =>
      ∃ i j : Fin k, i ≠ j ∧ p.1.1 + Pi.single j 1 = p.2.1 + Pi.single i 1).image
    fun p => s(p.1, p.2)

end MWCSherali


