-- Prove2me | solution 1 for ArcKayles192.PSPACE.arcKayles_polyGame
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:09.841253+00:00
-- url     : https://prove2.me/submissions/5fbe879c-5d0c-4584-af67-1d54bc3accf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_Complexity_FiniteGame_PolyGame
import Definitions.Def_ArcKayles192_PSPACE_PositionGame
import Theorems.Thm_ArcKayles192_PSPACE_nextPositions_polytime

open ArcKayles192.PSPACE
open Complexity.FiniteGame
open OptimalQueuingComplexity.Restless

namespace ArcKayles192.PSPACE

/-- The recursive characteristic-vector game has exactly the normal-play Arc Kayles outcome. -/
theorem outcome_aux (I : GraphInstance) (s : List Bool)
    (hs : arcKaylesGame.valid I s) :
    arcKaylesGame.wins I s ↔ FirstPlayerWins I.graph (bitsSet s) := by
  rw [Game.wins, FirstPlayerWins]
  constructor
  · rintro ⟨t, ht, hnot⟩
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := (mem_nextPositions_iff I s t).mp ht
    have hrec := outcome_aux I (posBits (bitsSet s \ {u, v}))
      (arcKaylesGame.next_valid I s _ hs ht)
    refine ⟨u, v, ⟨hu, hv, huv⟩, ?_⟩
    exact fun hw => hnot (hrec.mpr (by simpa using hw))
  · rintro ⟨u, v, ⟨hu, hv, huv⟩, hnot⟩
    let t := posBits (bitsSet s \ {u, v})
    have ht : t ∈ arcKaylesGame.next I s :=
      (mem_nextPositions_iff I s t).mpr ⟨u, v, hu, hv, huv, rfl⟩
    refine ⟨t, ht, ?_⟩
    have hrec := outcome_aux I t (arcKaylesGame.next_valid I s t hs ht)
    exact fun hw => hnot (by simpa [t] using hrec.mp hw)
termination_by arcKaylesGame.rank I s
decreasing_by all_goals exact arcKaylesGame.rank_next I s _ ht

end ArcKayles192.PSPACE

theorem solution :
    ∃ G : Complexity.FiniteGame.PolyGame GraphInstance,
      G.enc = GraphInstance.enc ∧
      ∀ I, G.wins I (G.start I) ↔ arcKayles I := by
  have enc_length (I : GraphInstance) :
      (GraphInstance.enc I).length = I.n ^ 2 + I.n + 1 := by
    simp [GraphInstance.enc, pow_two]
    omega
  have n_le_enc (I : GraphInstance) : I.n ≤ (GraphInstance.enc I).length := by
    rw [enc_length]
    omega
  let G : PolyGame GraphInstance :=
    { toGame := arcKaylesGame
      positionBound := Polynomial.X
      depthBound := Polynomial.X
      start_length I := by
        change (posBits (Finset.univ : Finset (Fin I.n))).length ≤
          Polynomial.eval (GraphInstance.enc I).length Polynomial.X
        simpa [posBits] using n_le_enc I
      next_length I s t _ ht := by
        obtain ⟨u, v, hu, hv, huv, rfl⟩ := (mem_nextPositions_iff I s t).mp ht
        change (posBits (bitsSet s \ {u, v})).length ≤
          Polynomial.eval (GraphInstance.enc I).length Polynomial.X
        simpa [posBits] using n_le_enc I
      rank_bound I s _ := by
        change (bitsSet s).card ≤ Polynomial.eval (GraphInstance.enc I).length Polynomial.X
        exact (Finset.card_le_univ _).trans (by simpa using n_le_enc I)
      next_computable := nextPositions_polytime }
  refine ⟨G, rfl, ?_⟩
  intro I
  change arcKaylesGame.wins I (posBits (Finset.univ : Finset (Fin I.n))) ↔
    FirstPlayerWins I.graph Finset.univ
  have h := outcome_aux I (posBits (Finset.univ : Finset (Fin I.n)))
    (arcKaylesGame.start_valid I)
  simpa using h