-- Prove2me | Definitions.Def_AaronsonAmbainis_AxiomReport
-- name    : AaronsonAmbainis_AxiomReport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:33:13.978971+00:00
-- url     : https://prove2.me/theorems/0c2cb946-b2e7-4165-9522-622f532170b7
-- title:
--   Axiom Report
-- statement:
--   Definitions and structural lemmas for Axiom Report, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/AxiomReport.lean

import Definitions.Def_AaronsonAmbainis_Main
import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_DetTheorem
import Definitions.Def_AaronsonAmbainis_DetBij_Main
import Definitions.Def_AaronsonAmbainis_DetBij_Bijection
import Definitions.Def_AaronsonAmbainis_DetLow_Corollary
import Definitions.Def_AaronsonAmbainis_TwoSided_Main
import Definitions.Def_AaronsonAmbainis_Level_Main
import Definitions.Def_AaronsonAmbainis_Average_Main
import Definitions.Def_AaronsonAmbainis_Row_Main
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
import Definitions.Def_AaronsonAmbainis_Pack_Main
import Definitions.Def_AaronsonAmbainis_Dual_Main
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Theorems.Thm_AaronsonAmbainis_DetBij_detInequality_of_lowest
import Theorems.Thm_AaronsonAmbainis_DetLow_lowestBound
import Theorems.Thm_AaronsonAmbainis_DetLow_lowestUnit
import Theorems.Thm_AaronsonAmbainis_influence_of_meanIncrement
import Theorems.Thm_AaronsonAmbainis_integratedAllPairs_of_allPairs
import Theorems.Thm_AaronsonAmbainis_mainTheorem_of_influence
import Theorems.Thm_AaronsonAmbainis_meanIncrement_of_thirdMoment
import Theorems.Thm_AaronsonAmbainis_rowBoundPM_of_packing
import Theorems.Thm_AaronsonAmbainis_sensitivity_of_block
import Theorems.Thm_AaronsonAmbainis_thirdMoment_of_integratedAllPairs

set_option autoImplicit true
open AaronsonAmbainis
example : LowestUnit := DetLow.lowestUnit
example : LowestBound := DetLow.lowestBound
example : LowestUnit → LowestBound → DetInequality :=
  DetBij.detInequality_of_lowest
example : AllPairsInequality → InfluenceBound :=
  fun hAllPairs => influence_of_meanIncrement (meanIncrement_of_thirdMoment
    (thirdMoment_of_integratedAllPairs (integratedAllPairs_of_allPairs hAllPairs)))
example : AllPairsInequality → BlockInequality → PackingBound → MainTheorem :=
  fun hAllPairs hBlock hPacking =>
    mainTheorem_of_influence
      (influence_of_meanIncrement (meanIncrement_of_thirdMoment
        (thirdMoment_of_integratedAllPairs (integratedAllPairs_of_allPairs hAllPairs))))
      (sensitivity_of_block hBlock) (rowBoundPM_of_packing hPacking)


