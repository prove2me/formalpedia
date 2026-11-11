-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:12:36.958973+00:00
-- url     : https://prove2.me/theorems/65478e98-7803-47e7-b6a0-eb413a096c4c
-- title:
--   Canonical History Marks
-- statement:
--   Definitions and structural lemmas for Canonical History Marks, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks
set_option autoImplicit false
namespace QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat) (sigma : Input S n)
abbrev Node := Σ i : LevelIndex (n + 2), GraphVertex S i.val
def physicalNode (i : LevelIndex n) (v : GraphVertex S (i.val + 2)) : Node S n :=
  ⟨LevelTwoHistory.physicalLevel i, v⟩
def oneNode (v : GraphVertex S 1) : Node S n := ⟨⟨1, by omega⟩, v⟩
def root : Node S n := ⟨0, ()⟩
def rootVertex (S : OddScale) : GraphVertex S 0 := ()
noncomputable def oneMarks : Finset (GraphVertex S 1) :=
  Finset.univ.filter (fun u => ∃ v ∈ baseMarks S n sigma, parent S 1 v = some u)
noncomputable def rootMarks : Finset (GraphVertex S 0) := by
  letI : Decidable (oneMarks S n sigma).Nonempty := Classical.propDecidable _
  exact if (oneMarks S n sigma).Nonempty then {rootVertex S} else ∅
noncomputable def physicalNodes : Finset (Node S n) :=
  Finset.univ.biUnion (fun i : LevelIndex n =>
    (physicalMarks S n sigma i).image (physicalNode S n i))
noncomputable def marks : Finset (Node S n) :=
  physicalNodes S n sigma ∪ (oneMarks S n sigma).image (oneNode S n) ∪
    (rootMarks S n sigma).image (fun _ => root S n)
def markedAdjacent (u v : Node S n) : Prop :=
  (decodingGraph S (n + 2)).adjacent u v ∧ u ∈ marks S n sigma ∧ v ∈ marks S n sigma
noncomputable def rootComponent : Finset (Node S n) :=
  if root S n ∈ marks S n sigma then
    Finset.univ.filter (fun w => w ∈ marks S n sigma ∧
      Relation.ReflTransGen (markedAdjacent S n sigma) w (root S n))
  else ∅
noncomputable def actualMarks (j : Nat)
    (s : Input S (2 * j)) : Finset (Node S (2 * j)) := marks S (2 * j) s
noncomputable def actualRootComponent (j : Nat)
    (s : Input S (2 * j)) : Finset (Node S (2 * j)) := rootComponent S (2 * j) s
end QEC.Coding.BDL26CanonicalHistoryMarks


