-- Prove2me | solution 1 for AddUN.corollaryA_of_theoremB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:50.963858+00:00
-- url     : https://prove2.me/submissions/de38a4f4-b6c5-44b8-8e2e-75defc388c18

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements

set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN
namespace AddUN
theorem _root_.solution (hB : TheoremB) (hG : Grzegorek) : CorollaryA := by
  intro h
  obtain ⟨A, hA, hcard⟩ := hG
  exact hB A hA (hcard.trans h)
end AddUN
