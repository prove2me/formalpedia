-- Prove2me | solution 1 for AaronsonAmbainis.mainTheoremImproved_of_influence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:15.185505+00:00
-- url     : https://prove2.me/submissions/41b0ccf6-6217-42c9-8ec9-5664d183d5b4

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Theorems.Thm_AaronsonAmbainis_rows_of_rowBound
import Theorems.Thm_AaronsonAmbainis_Average_influence_of_incr


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution :
    InfluenceBound → SensitivityBound → RowBound → MainTheoremImproved := by
  intro hI hS hRB ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := rows_of_rowBound hRB d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring
end AaronsonAmbainis
