-- Prove2me | Definitions.Def_FlexibleNRM_maxResources
-- name    : FlexibleNRM_maxResources
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:33.510827+00:00
-- url     : https://prove2.me/theorems/3549b75a-a25a-4d02-ba51-ceb23869b3ab
-- title:
--   The maximum number of resources used by a route, $L$
-- statement:
--   $$L=\max_{j\in\mathcal J,\ p\in\mathcal R_j}|A_p|.$$
--   This is the constant in the performance guarantee $1/(1+\theta L)$.
--
--   **Formalization Note** The value is $0$ when there are no products, and in that case every revenue in the mission is $0$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §3, p.11

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- `L = max_{j ∈ J, p ∈ R_j} |A_p|`, the maximum number of resources used by a route.

Zhu, Topaloglu, manuscript of November 16, 2022, §3, p.11.

**Formalization Note** The maximum is a `Finset.sup` in `ℕ`. With `n = 0` the index set is empty and
the value is `0`; for `n > 0` it is the paper's maximum, because `R_j` and `A_p` are nonempty. -/
def maxResources {n m r : ℕ} (N : Network n m r) : ℕ :=
  Finset.univ.sup fun j => (N.R j).sup fun p => (N.A p).card

end FlexibleNRM


