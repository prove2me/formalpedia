-- Prove2me | solution 1 for AaronsonAmbainis.mainTheorem_of_influence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:12.650393+00:00
-- url     : https://prove2.me/submissions/4bc2d0e4-e655-4e0c-8447-879faa4cd946

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Theorems.Thm_AaronsonAmbainis_Average_influence_of_incr


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution :
    InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem := by
  intro hI hS hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring
end AaronsonAmbainis
