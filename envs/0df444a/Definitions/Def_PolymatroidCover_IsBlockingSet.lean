-- Prove2me | Definitions.Def_PolymatroidCover_IsBlockingSet
-- name    : PolymatroidCover_IsBlockingSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:20.856451+00:00
-- url     : https://prove2.me/theorems/cc956995-40db-4f9d-b510-971328e76927
-- title:
--   Blocking set: Step 6 of Algorithm 1 / eq. (8)
-- statement:
--   Let $T$ be a search sequence, $S_1 \sqcup \dots \sqcup S_k$ the current coloring and $(a, j)$ an adding pair. The **blocking set** of $(a, j)$ is the (inclusion-wise) minimal minimizer $R$ of
--
--   $$
--   \min_{X \subseteq S_j \setminus B_j} \tilde f\big(X \mid \{a\} \cup A_j \cup B_j\big),
--   $$
--
--   with $A_j, B_j$ taken over all layers of $T$. If $R = \emptyset$, then $\{a\} \cup S_j$ is independent and $a$ can be colored $j$; otherwise $R$ is the part of $S_j$ that blocks this.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, p.12 (PDF p.14), eq. (8); Algorithm 1, Step 6, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PolymatroidCover_defic
import Definitions.Def_PolymatroidCover_IsMinimalMinimizer
import Definitions.Def_PolymatroidCover_Layer

namespace PolymatroidCover

/-- `R` is the blocking set of the adding pair `(a, j)` for the search sequence `T` and the
coloring `col` (Step 6 of Algorithm 1, Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.14 = PDF p.16; eq. (8), printed p.12 =
PDF p.14; (V2) of Definition 3.2, printed p.13): `R` is the (inclusion-wise) minimal minimizer
of
```
min_{X ⊆ S_j \ B_j} f̃(X | {a} ∪ A_j ∪ B_j),
```
with `A_j`, `B_j` taken over all layers of `T` and `S_j = col j`.

**Formalization Note** `f̃(X | S)` is `deficCond f X S = f̃(X ∪ S) − f̃(S)`. -/
def IsBlockingSet {n k : ℕ} (f : Finset (Fin n) → ℕ) (col : Fin k → Finset (Fin n))
    (T : List (Layer n k)) (a : Fin n) (j : Fin k) (R : Finset (Fin n)) : Prop :=
  IsMinimalMinimizer (fun X => deficCond f X (insert a (addSet T j ∪ blockSet T j)))
    (col j \ blockSet T j) R

end PolymatroidCover


