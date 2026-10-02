-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMaxDiff
-- name    : DiscreteConvex_LConvexFunctions_ArgMaxDiff
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:45.795342+00:00
-- url     : https://prove2.me/theorems/96b63525-587b-47f9-9cf1-179b778d334e
-- title:
--   Coordinates achieving the maximum componentwise gap
-- statement:
--   $X = \arg\max_{v \in V} \{p(v) - q(v)\}$: the coordinates at which $p - q$ attains its maximum. Supporting notion for axiom (L$^\natural$-APR[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, supporting axiom (L♮-APR[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180 (supporting axiom (L♮-APR[Z]))

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180: the coordinates achieving the maximum
componentwise gap between two integer vectors, used in axiom (L♮-APR[Z]), in
`DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- `X = arg max_{v ∈ V} \{p(v) - q(v)\}`: the coordinates at which `p - q` attains its
maximum. -/
def ArgMaxDiff {V : Type*} [Fintype V] [DecidableEq V] (p q : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => ∀ w : V, p w - q w ≤ p v - q v)

end DiscreteConvex.LConvexFunctions


