-- Prove2me | Definitions.Def_GraphNNSphere_NavGraph
-- name    : GraphNNSphere_NavGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:10.398945+00:00
-- url     : https://prove2.me/theorems/01d6684c-7021-40b1-a7c5-a5fefaad870c
-- title:
--   Neighbor lists on the labels
-- statement:
--   An assignment of a neighbor list to each data label. Lists are finite sets of labels, so their entries are distinct.
--
--   **Formalization Note** The paper identifies each label with its point, since points are almost surely distinct. Here the graph lives on labels.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib

namespace GraphNNSphere

/-- The neighbor lists of a graph on the data labels (Lu, *Sharp Limits of Graph-Based Nearest
Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3).

**Formalization Note** Each list is a `Finset` of labels, which records that its entries are
distinct. The paper identifies a label with its point, as points are almost surely distinct. -/
abbrev NavGraph (n : ℕ) : Type := Fin n → Finset (Fin n)

end GraphNNSphere


