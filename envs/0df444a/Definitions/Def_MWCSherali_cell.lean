-- Prove2me | Definitions.Def_MWCSherali_cell
-- name    : MWCSherali_cell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:11.342882+00:00
-- url     : https://prove2.me/theorems/e8ad375d-759c-47a2-8482-580f60e2c42e
-- title:
--   Downward cells $D(v)$
-- statement:
--   For $v\in\Delta_{k,n+1}$ the **downward cell** of $\Delta_{k,n}$ is
--
--   $$D(v)=\Big\{u\in\Delta_{k,n}\;\Big|\;\exists\, i\in[k],\ u=\tfrac{n+1}{n}v-\tfrac1n e_i\Big\}.$$
--
--   $D_{k,n}$ is the set of downward cells; it is in one-to-one correspondence with $\Delta_{k,n+1}$. Cells may be degenerate, e.g. $D(e_i)=\{e_i\}$.
--
--   **Formalization Note** Cells are indexed by $V=(n+1)v\in\Delta_{k,n+1}$ in integer coordinates, where the condition reads $u+e_i=V$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.2, p.15

import Mathlib
import Definitions.Def_MWCSherali_Grid

namespace MWCSherali

/-- **Downward cells `D(v)`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of
Nov. 3, 2026), §2.2, p.15: for `v ∈ Δ_{k,n+1}`,
`D(v) = {u ∈ Δ_{k,n} | ∃ i ∈ [k], u = ((n+1)/n) v − (1/n) e_i}`; `D_{k,n}` is the set of these
cells, in one-to-one correspondence with `Δ_{k,n+1}`.

**Formalization Note.** Cells are indexed by `V : Grid k (n+1)` (the integer coordinates
`(n+1)v`). In integer coordinates `u = ((n+1)v − e_i)/n` reads `u + e_i = V`. Degenerate cells
(fewer than `k` vertices, e.g. `D(e_i) = {e_i}`) are included, as in the paper. -/
def cell {k n : ℕ} (V : Grid k (n + 1)) : Finset (Grid k n) :=
  Finset.univ.filter fun u => ∃ i, u.1 + Pi.single i 1 = V.1

end MWCSherali


