-- Prove2me | Definitions.Def_MWCSherali_corner
-- name    : MWCSherali_corner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:01.420119+00:00
-- url     : https://prove2.me/theorems/18f3a5e5-e864-4c42-b799-26682ae8f6a3
-- title:
--   The terminal $e_i$ of $\Delta_{k,n}$
-- statement:
--   For $i\in[k]$, $e_i$ is the $i$-th standard basis vector, a vertex of $\Delta_{k,n}$: the **terminal** $i$ of the simplex. In integer coordinates it is $n e_i$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §1.1, p.3; §2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid

namespace MWCSherali

/-- **The terminal `e_i` of `Δ_{k,n}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), §1.1, p.3 ("`e_i` denotes the `i`-th standard basis vector") and §2.1,
p.14 (the case `x = e_i` of `L^no`).

**Formalization Note.** In integer coordinates `y = n·x` the vertex `e_i` is `n·e_i`, i.e.
`Pi.single i n`; the index `i : Fin k` is 0-based. -/
def corner (k n : ℕ) (i : Fin k) : Grid k n :=
  ⟨Pi.single i n, by simp⟩

end MWCSherali


