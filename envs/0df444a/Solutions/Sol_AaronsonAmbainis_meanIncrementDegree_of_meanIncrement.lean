-- Prove2me | solution 1 for AaronsonAmbainis.meanIncrementDegree_of_meanIncrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:11.14252+00:00
-- url     : https://prove2.me/submissions/1cb37331-46cc-4488-bddb-f7ff62019468

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution :
    MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound := by
  intro hM hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := hM ι f (Real.pi ^ 2 * (d : ℝ) ^ 2) a ha0 haK hacov hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring
end AaronsonAmbainis
