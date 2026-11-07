-- Prove2me | Definitions.Def_LCPlanarSteiner_IsJunctionPartition
-- name    : LCPlanarSteiner_IsJunctionPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:37.633196+00:00
-- url     : https://prove2.me/theorems/c9722355-6d58-48af-8404-4d5ec781f653
-- title:
--   Partitions of the pairs into junctions
-- statement:
--   A **junction** $(H', v, I)$ is a set $H'$ of original arcs, an original vertex $v$ (its root) and a nonempty set $I$ of pair indices; its density is $c(H')/|I|$. A finite list of junctions $(H_z, v_z, I_z)$ is a **junction partition** of the $r$ pairs with arm bound $x$ when
--   1. every $I_z$ is a nonempty set of pair indices and every $v_z$ is a vertex;
--   2. every pair $i \in I_z$ satisfies $\mathrm{dist}_{H_z}(s_i, v_z) + \mathrm{dist}_{H_z}(v_z, t_i) \le x$;
--   3. every index $i \in [r]$ lies in exactly one $I_z$.
--
--   Lemmas 4.1 and 4.4 produce such partitions.
--
--   **Formalization Note** A junction listed twice counts twice in $\sum_z c(H_z)$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4, p.9; Lemma 4.1, p.10

import Mathlib
import Definitions.Def_LCPlanarSteiner_ArmsLE

namespace LCPlanarSteiner

/-- **A partition of the demand indices into junctions with arm bound `x`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4, p.9: "A junction (H′, v, I) is an original subgraph, an original root, and a nonempty set
of original pair indices. Its density is c(H′)/|I|."; Lemma 4.1, p.10: "There are junctions
(H_z, v_z, I_z), with v_z ∈ V(P) and nonempty I_z partitioning [r], such that
dist_{H_z}(s_i, v_z) + dist_{H_z}(v_z, t_i) ≤ (1 + η)h (i ∈ I_z)".

`IsJunctionPartition G dem zs x`: `zs` is a finite list of junctions `(H_z, v_z, I_z)` (an arc set,
a vertex `v_z < n`, an index set), each `I_z` is a nonempty set of indices of `dem`, every pair
`i ∈ I_z` has `dist_{H_z}(s_i, v_z) + dist_{H_z}(v_z, t_i) ≤ x`, and every index `i < r` lies in
exactly one `I_z`.

**Formalization Note.** A junction may be listed twice; it then counts twice in `Σ_z c(H_z)`, which
only makes a cost bound harder. Indices are `0, …, r − 1`. -/
def IsJunctionPartition (G : Net) (dem : List (ℕ × ℕ)) (zs : List (Finset ℕ × ℕ × Finset ℕ))
    (x : ℚ) : Prop :=
  (∀ z ∈ zs, z.2.1 < G.n ∧ z.2.2.Nonempty ∧
    ∀ i ∈ z.2.2, i < dem.length ∧
      ArmsLE G z.1 z.2.1 (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 x) ∧
  ∀ i < dem.length, (zs.filter fun z => decide (i ∈ z.2.2)).length = 1

end LCPlanarSteiner


