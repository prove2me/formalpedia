-- Prove2me | Definitions.Def_MultimodularDocks_depotCost
-- name    : MultimodularDocks_depotCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:46.483282+00:00
-- url     : https://prove2.me/theorems/9cee7447-5c34-41e6-928a-3aadd03eb7c4
-- title:
--   Depot cost $c_D(d,b)=d+b-B$
-- statement:
--   The dummy **depot** station $D$, added to turn problem (P1) into (P2), has the cost
--
--   $$
--   c_D(d,b)=d+b-B,
--   $$
--
--   so that the depot is charged for every dock it holds beyond the $B$ it starts with. In the paper it has the band $l_D=B\le d+b\le u_D=2B+D$.
--
--   **Formalization Note** The band is not part of this function; it is given by the bounds of the depot station in an instance.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2, p.12

import Mathlib

namespace MultimodularDocks

/-- **The depot station's cost** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §2, p.12):
`c_D(d, b) = d + b − B`, used for the dummy station `D` with `l_D = B`, `u_D = 2B + D` that turns
problem (P1) into (P2).

**Formalization Note** The band `l_D ≤ d + b ≤ u_D` is not part of this function; it is the
station's lower and upper bound in an `Instance`. -/
def depotCost (B : ℤ) (d b : ℤ) : ℝ :=
  ((d + b - B : ℤ) : ℝ)

end MultimodularDocks


