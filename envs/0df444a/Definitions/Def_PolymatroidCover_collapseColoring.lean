-- Prove2me | Definitions.Def_PolymatroidCover_collapseColoring
-- name    : PolymatroidCover_collapseColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:24.980623+00:00
-- url     : https://prove2.me/theorems/3845f2dd-38eb-468f-9d75-9e2f722b6787
-- title:
--   Recolored coloring $S'$ of a collapse step
-- statement:
--   In a collapse step of Algorithm 1 the blocking set of the adding pair $(a, j)$ is empty. If $a \ne h$, the element $a$, currently in a blocking set of color $j'$, is **recolored** from $j'$ to $j$:
--
--   $$
--   S'_j = S_j \cup \{a\}, \qquad S'_{j'} = S_{j'} \setminus \{a\}, \qquad S'_r = S_r \ (r \ne j, j').
--   $$
--
--   If $a = h$, the algorithm sets $S'_j = S_j \cup \{h\}$, keeps the other classes, and returns the coloring.
--
--   **Formalization Note** `collapseColoring col a j j'` is the first map and `addColoring col h j` the second; in every use $j \ne j'$.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Algorithm 1, lines 14 and 19, p.14 (PDF p.16); p.17 (PDF p.19)

import Mathlib

namespace PolymatroidCover

/-- The recolored coloring `S'` of a collapse step with `a ≠ h` (Algorithm 1, line 19,
Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16; printed p.17 = PDF p.19): the element `a` is moved from its
color class `S_{j'}` into `S_j`, i.e. `S'_j = S_j ∪ {a}`, `S'_{j'} = S_{j'} \ {a}`, and every
other class is unchanged.

**Formalization Note** The case split tests `j` first; in every use `j ≠ j'` holds (Fact 1),
and the definition does not depend on an update order there. -/
def collapseColoring {n k : ℕ} (col : Fin k → Finset (Fin n)) (a : Fin n) (j j' : Fin k) :
    Fin k → Finset (Fin n) :=
  fun r => if r = j then insert a (col j) else if r = j' then (col j').erase a else col r

/-- The returned coloring of a collapse step with `a = h` (Algorithm 1, lines 14–15,
Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16): `S'_j = S_j ∪ {h}`, every other class unchanged. -/
def addColoring {n k : ℕ} (col : Fin k → Finset (Fin n)) (h : Fin n) (j : Fin k) :
    Fin k → Finset (Fin n) :=
  fun r => if r = j then insert h (col j) else col r

end PolymatroidCover


