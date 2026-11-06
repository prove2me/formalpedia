-- Prove2me | Definitions.Def_PolymatroidCover_IsValidColoring
-- name    : PolymatroidCover_IsValidColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:11.157015+00:00
-- url     : https://prove2.me/theorems/31713c68-d6b9-4547-9953-a9ca7459a439
-- title:
--   Valid $k$-coloring of $S \subseteq E$
-- statement:
--   Let $f$ be a polymatroid on $E$ and $k$ a positive integer. A **$k$-coloring** of a set $S \subseteq E$ is a partition $S = S_1 \sqcup \dots \sqcup S_k$; it is **valid** if every color class $S_j$ is independent. A valid $k$-coloring of $E$ is a covering of $E$ by at most $k$ independent sets.
--
--   **Formalization Note** A coloring is a map from the colors `Fin k` (0-based) to subsets of `Fin n`; the classes are pairwise disjoint, their union is $S$, and empty classes are allowed.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PolymatroidCover_IsIndep

namespace PolymatroidCover

/-- A valid `k`-coloring of `S ⊆ E` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3, printed p.11 = PDF p.13): a partition
`S = S_1 ⊔ ⋯ ⊔ S_k` in which every class `S_j` is independent.

**Formalization Note** The coloring is a map `col : Fin k → Finset (Fin n)` (colors are
0-based, `col j` is `S_{j+1}`); the classes are pairwise disjoint and their union is `S`.
Empty classes are allowed. -/
def IsValidColoring {n k : ℕ} (f : Finset (Fin n) → ℕ) (S : Finset (Fin n))
    (col : Fin k → Finset (Fin n)) : Prop :=
  (∀ i j : Fin k, i ≠ j → Disjoint (col i) (col j)) ∧
    Finset.univ.biUnion col = S ∧ ∀ j : Fin k, IsIndep f (col j)

end PolymatroidCover


