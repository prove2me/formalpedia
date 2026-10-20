-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P12
-- name    : QAlgorithms_Papers_Independent_Frontier18_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:50:55.1868+00:00
-- url     : https://prove2.me/theorems/dcf98c95-1a83-4888-8396-00816ce65b72
-- title:
--   Definitions for Bounds on entanglement distillation and secret key agreement for quantum broadcast channels
-- statement:
--   The objects the formalized statements of *Bounds on entanglement distillation and secret key agreement for quantum broadcast channels* (arXiv:1503.08139) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsPartyPartition`: A partition of a finite party set into nonempty disjoint blocks, arXiv:1503.08139v2, PDF pp.8-9, (2.34)-(2.35). The disjointness condition concerns distinct blocks.
--   - `partitionIntersections`: The nonempty intersections A(M,G), arXiv:1503.08139v2, PDF p.16, Definition 10, (3.74), and p.25, (6.3). This groups tensor factors; it does not trace out any member of M. Its intended use assumes `IsPartyPartition S G` and `M ⊆ S`.
--   - `crossingSubsets`: Crossing subsets C(G), arXiv:1503.08139v2, PDF p.16, Definition 9, corrected using example (3.73) and the explicit removal rule in the proof on p.17, (3.82). Printed: remove only empty and singleton subsets. Changed: keep exactly subsets meeting at least two blocks. Why: a resource confined to one block has zero entanglement across the partition. Intended use assumes `IsPartyPartition S G`. For a one-block partition this definition has no crossing subsets. Independent moderation of this source correction remains pending.
-- source:
--   Bounds on entanglement distillation and secret key agreement for quantum broadcast channels, arXiv:1503.08139v2, https://arxiv.org/abs/1503.08139v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

/-!
# Broadcast entanglement and secret-key bounds: arXiv:1503.08139v2

The complete scalar assertion (7.18) is stated below. The eleven quantum result nodes
are explicitly deferred in HARD.md and GAPS.json: the actual multipartite entropy,
private-resource target, and adaptive broadcast-protocol interfaces are unfinished.
The partition definitions are only combinatorial groundwork, not surrogate quantum measures.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P12

open Filter
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)
open scoped Topology

/-- A partition of a finite party set into nonempty disjoint blocks,
arXiv:1503.08139v2, PDF pp.8-9, (2.34)-(2.35).
The disjointness condition concerns distinct blocks. -/
def IsPartyPartition {Party : Type*} [DecidableEq Party]
    (S : Finset Party) (G : Finset (Finset Party)) : Prop :=
  (∀ X ∈ G, X.Nonempty) ∧
    (∀ X ∈ G, ∀ Y ∈ G, X ≠ Y → Disjoint X Y) ∧
    G.biUnion id = S

/-- The nonempty intersections A(M,G), arXiv:1503.08139v2, PDF p.16,
Definition 10, (3.74), and p.25, (6.3). This groups tensor factors; it does not trace
out any member of M. Its intended use assumes `IsPartyPartition S G` and `M ⊆ S`. -/
def partitionIntersections {Party : Type*} [DecidableEq Party]
    (G : Finset (Finset Party)) (M : Finset Party) : Finset (Finset Party) :=
  (G.image (fun X => X ∩ M)).erase ∅

/-- Crossing subsets C(G), arXiv:1503.08139v2, PDF p.16, Definition 9,
corrected using example (3.73) and the explicit removal rule in the proof on p.17,
(3.82). Printed: remove only empty and singleton subsets. Changed: keep exactly
subsets meeting at least two blocks. Why: a resource confined to one block has
zero entanglement across the partition. Intended use assumes `IsPartyPartition S G`.
For a one-block partition this definition has no crossing subsets. Independent
moderation of this source correction remains pending. -/
def crossingSubsets {Party : Type*} [DecidableEq Party]
    (S : Finset Party) (G : Finset (Finset Party)) : Finset (Finset Party) :=
  S.powerset.filter (fun M => 2 ≤ (partitionIntersections G M).card)

/-- Vacuum entropy, including the continuous convention at zero (PDF p.28). -/
example : thermalEntropy 0 = 0 := by
  simp [thermalEntropy]

/-- At lambda = 1 the difference is identically zero, so monotonicity must be
nonstrict (PDF p.28, (7.18)). -/
example (x : ℝ) : thermalEntropy x - thermalEntropy (1 * x) = 0 := by
  simp

/-- The empty party set has its usual empty partition. Quantum resource bounds
concern nontrivial partitions, rather than this edge case (PDF pp.8-9). -/
example : IsPartyPartition (∅ : Finset ℕ) ∅ := by
  simp [IsPartyPartition]

/-- An empty resource subset meets no block (PDF p.16, Definition 10). -/
example {Party : Type*} [DecidableEq Party] (G : Finset (Finset Party)) :
    partitionIntersections G ∅ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro X hX
  obtain ⟨Y, hY, hYX⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hX).2
  have hzero : X = ∅ := by simpa using hYX.symm
  exact (Finset.mem_erase.mp hX).1 hzero

/-- With no blocks there are no crossing subsets (PDF p.16, Definition 9,
with the correction specified above). -/
example {Party : Type*} [DecidableEq Party] (S : Finset Party) :
    crossingSubsets S ∅ = ∅ := by
  simp [crossingSubsets, partitionIntersections]

end QAlgorithms.Papers.Independent.Frontier18.P12


