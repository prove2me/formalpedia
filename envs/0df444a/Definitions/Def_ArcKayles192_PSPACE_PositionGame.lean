-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_PositionGame
-- name    : ArcKayles192_PSPACE_PositionGame
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:04.582964+00:00
-- url     : https://prove2.me/theorems/a6f1c27e-cedd-472a-aabd-098f5db979d3
-- title:
--   Arc Kayles as a finite game on characteristic vectors
-- statement:
--   For an adjacency-matrix instance with $n$ vertices, a position is represented by an $n$-bit characteristic vector: bit $i$ says whether vertex $i$ remains. The successor generator scans all ordered pairs $(u,v)$ and, whenever both bits are set and $uv$ is an edge, emits the vector obtained by clearing those two bits. The resulting finite game uses the number of remaining vertices as rank, and validity means exactly that the vector has length $n$. Thus every move strictly decreases rank, all successors remain valid, and membership in the successor list is equivalent to the existence of a legal Arc Kayles move.
--
--   This is the explicit position representation and move enumeration used by the depth-first polynomial-space evaluation argument. Valid positions have $n$ bits, and a play has at most $n$ moves (indeed at most $n/2$).
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), p.1 (a move deletes both endpoints), p.2 (finite normal-play game), and p.5, proof of Theorem 1 (positions use O(N^2) bits and at most N/2 moves; the characteristic-vector specialization uses exactly N bits).

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_Complexity_FiniteGame_PolyGame

namespace ArcKayles192.PSPACE

open Complexity.FiniteGame

/-- The characteristic vector of a set of vertices. -/
def posBits {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ S)

/-- The set of vertices whose bit is set in a binary word. Bits beyond the word are false. -/
def bitsSet {n : ℕ} (s : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => s.getD i.val false = true

@[simp] theorem bitsSet_posBits {n : ℕ} (S : Finset (Fin n)) :
    bitsSet (posBits S) = S := by
  ext i
  simp [bitsSet, posBits]

/-- Enumerate all ordered endpoint pairs and output the deletion vector for every legal move. -/
def nextPositions (I : GraphInstance) (s : List Bool) : List (List Bool) :=
  (List.finRange I.n).flatMap fun u =>
    (List.finRange I.n).flatMap fun v =>
      if u ∈ bitsSet s ∧ v ∈ bitsSet s ∧ I.adj u v = true then
        [posBits (bitsSet s \ {u, v})]
      else []

/-- Arc Kayles as a finite game on characteristic vectors. -/
def arcKaylesGame : Game GraphInstance where
  enc := GraphInstance.enc
  start I := posBits (Finset.univ : Finset (Fin I.n))
  next := nextPositions
  rank I s := (bitsSet s).card
  valid I s := s.length = I.n
  start_valid I := by
    change (posBits (Finset.univ : Finset (Fin I.n))).length = I.n
    simp [posBits]
  next_valid I s t _ ht := by
    simp only [nextPositions, List.mem_flatMap, List.mem_finRange, true_and] at ht
    obtain ⟨u, v, ht⟩ := ht
    split_ifs at ht with h
    · simp only [List.mem_singleton] at ht
      subst t
      change (posBits (bitsSet s \ {u, v})).length = I.n
      simp [posBits]
    · simp at ht
  rank_next I s t ht := by
    simp only [nextPositions, List.mem_flatMap, List.mem_finRange, true_and] at ht
    obtain ⟨u, v, ht⟩ := ht
    split_ifs at ht with h
    · simp only [List.mem_singleton] at ht
      subst t
      change (bitsSet (posBits (bitsSet s \ {u, v}))).card < (bitsSet s).card
      rw [bitsSet_posBits]
      exact card_sdiff_pair_lt v h.1
    · simp at ht

/-- Membership in the successor list is exactly the existence of a legal Arc Kayles move. -/
theorem mem_nextPositions_iff (I : GraphInstance) (s t : List Bool) :
    t ∈ nextPositions I s ↔ ∃ u v, u ∈ bitsSet s ∧ v ∈ bitsSet s ∧ I.adj u v = true ∧
      t = posBits (bitsSet s \ {u, v}) := by
  simp only [nextPositions, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨u, v, ht⟩
    split_ifs at ht with h
    · simp only [List.mem_singleton] at ht
      exact ⟨u, v, h.1, h.2.1, h.2.2, ht⟩
    · simp at ht
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    exact ⟨u, v, by simp [hu, hv, huv]⟩

end ArcKayles192.PSPACE


