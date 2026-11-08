-- Prove2me | Definitions.Def_GraphNNSphere_successor
-- name    : GraphNNSphere_successor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:29.462471+00:00
-- url     : https://prove2.me/theorems/c54a885d-4195-459e-ba1d-3011c9589eb5
-- title:
--   Successor of a point in a greedy run
-- statement:
--   For a nonempty neighbor list $G(x)$, the successor of $x$ with respect to $q$ is its listed point closest to $q$. It is undefined for an empty list.
--
--   **Formalization Note** The minimum is taken in the lexicographic order on (distance to $q$, label), so a distance tie is broken by label. Ties among distinct points occur only on the bisectors, which have measure zero.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §2.1, p.14

import Mathlib
import Definitions.Def_GraphNNSphere_geo
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- The successor of `cur`: its listed point closest to `q`, when the list is nonempty (Lu, *Sharp
Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript
sha256 93565bc5…), §2.1, p.14).

**Formalization Note** The minimum is taken for the lexicographic order on (distance to `q`,
label), so a distance tie is broken by label. Ties occur only on the bisectors, which have measure
zero and which every query set of the mission excludes or may exclude. -/
noncomputable def successor {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (cur : Fin n) : Option (Fin n) :=
  if h : (G cur).Nonempty then
    some (ofLex (((G cur).image (fun j => toLex (geo q (X j), j))).min' (h.image _))).2
  else none

end GraphNNSphere


