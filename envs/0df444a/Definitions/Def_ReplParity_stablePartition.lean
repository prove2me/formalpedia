-- Prove2me | Definitions.Def_ReplParity_stablePartition
-- name    : ReplParity_stablePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:40.160869+00:00
-- url     : https://prove2.me/theorems/723476d9-5225-4b44-9099-b69f3acbfc1e
-- title:
--   Stable partition of a sequence of vectors (§2.4)
-- statement:
--   Given an ordered sequence $S$ of nonzero vectors in $\mathbb F_2^n$, the **stable partition** is obtained by repeated greedy passes. Each pass scans the remaining vectors in order, keeps every vector that is linearly independent of the vectors kept so far in this pass, and removes the kept set as one part. Zero vectors carry no information about spans and are discarded before partitioning. The **span of a part** is the subspace its vectors generate.
--
--   The partition is due to Kaplan, Mansour, Moran, Stemmer and Tur, and it is the source of stability in the learners of §3: deleting one sample point changes the multiset of part spans very little (Theorem 2.6).
--
--   **Formalization Note** A nonzero vector is linearly independent of an independent set exactly when it lies outside the set's span, which is the test used. Each pass on a nonempty sequence of nonzero vectors keeps its first vector, so $|S|$ passes always suffice.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.4, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

open Classical in
/-- One greedy pass with the vectors `kept` so far: scanning in order, a vector outside the span
of the kept vectors is kept, any other vector is left for the next pass. Returns
`(kept vectors, remaining vectors)`, both in their original order. -/
noncomputable def passAux {n : ℕ} : List (Vec n) → List (Vec n) → List (Vec n) × List (Vec n)
  | kept, [] => (kept, [])
  | kept, v :: vs =>
      if v ∈ Submodule.span (ZMod 2) {x | x ∈ kept} then
        ((passAux kept vs).1, v :: (passAux kept vs).2)
      else passAux (kept ++ [v]) vs

/-- One greedy pass over a sequence, starting with nothing kept. -/
noncomputable def greedyPass {n : ℕ} (l : List (Vec n)) : List (Vec n) × List (Vec n) :=
  passAux [] l

open Classical in
/-- Repeated greedy passes, each removing its kept set as one part; at most `k` passes. -/
noncomputable def partitionFuel {n : ℕ} : ℕ → List (Vec n) → List (List (Vec n))
  | 0, _ => []
  | k + 1, l =>
      if (greedyPass l).1 = [] then [] else (greedyPass l).1 :: partitionFuel k (greedyPass l).2

/-- **Stable partition (§2.4).** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity
and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…), §2.4, p.13
(PDF p.15): "Given an ordered sequence S of nonzero vectors in 𝔽ⁿ₂, the partition is obtained by
repeated greedy passes. Each pass scans the remaining vectors in order, keeps every vector that is
linearly independent of the vectors kept so far in this pass, and removes the kept set as one
part." and "Zero vectors carry no information about spans, and we discard them before
partitioning."

`stablePartition S` is the list of parts, in the order the passes produce them.

**Formalization Note.** Zero vectors are discarded first. A nonzero vector is linearly independent
of an independent set exactly when it lies outside its span, which is the test used. Every pass
on a nonempty sequence of nonzero vectors keeps its first vector, so `|S|` passes suffice; the
pass budget never cuts the partition short. -/
noncomputable def stablePartition {n : ℕ} (S : List (Vec n)) : List (List (Vec n)) :=
  partitionFuel S.length (S.filter (fun v => v ≠ 0))

/-- The span of a part. -/
noncomputable def spanOf {n : ℕ} (P : List (Vec n)) : Subsp n :=
  Submodule.span (ZMod 2) {x | x ∈ P}

end ReplParity


