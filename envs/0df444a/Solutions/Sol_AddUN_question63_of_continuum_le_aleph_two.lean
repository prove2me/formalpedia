-- Prove2me | solution 1 for AddUN.question63_of_continuum_le_aleph_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:10.662805+00:00
-- url     : https://prove2.me/submissions/7d65ee9c-8f3b-4dcd-9bd5-ed15ff552165

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
public import Theorems.Thm_AddUN_corollaries_of_theoremB

set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution (hB : TheoremB) (hG : Grzegorek) (hle : GotoCor513)
    (h : (𝔠 : Cardinal.{0}) ≤ ℵ_ 2) : Question63 :=
  ((corollaries_of_theoremB hB hG hle).2.1 h).symm
end AddUN
