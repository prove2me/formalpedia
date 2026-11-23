-- Prove2me | solution 1 for ArcKayles192.PSPACE.theorem_1_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:45:02.685812+00:00
-- url     : https://prove2.me/submissions/5a05b730-2406-4bd9-84b6-72decd5a4d08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Theorems.Thm_Complexity_FiniteGame_PolyGame_inPSPACE
import Theorems.Thm_ArcKayles192_PSPACE_arcKayles_polyGame

open OptimalQueuingComplexity.Restless ArcKayles192.PSPACE

/-- **Theorem 1, membership half** (proof of Theorem 1, p.5). ARC KAYLES, with the standard
adjacency-matrix encoding, is in PSPACE. -/
theorem solution : InPSPACE GraphInstance.enc arcKayles := by
  obtain ⟨G, hEnc, hWins⟩ := arcKayles_polyGame
  have h := Complexity.FiniteGame.PolyGame.inPSPACE G
  rw [hEnc] at h
  have hp : (fun a => G.wins a (G.start a)) = arcKayles := by
    funext I
    exact propext (hWins I)
  rw [hp] at h
  exact h