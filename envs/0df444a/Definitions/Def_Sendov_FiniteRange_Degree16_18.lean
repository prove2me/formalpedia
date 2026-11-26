-- Prove2me | Definitions.Def_Sendov_FiniteRange_Degree16_18
-- name    : Sendov_FiniteRange_Degree16_18
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:06:52.301076+00:00
-- url     : https://prove2.me/theorems/08356fa0-dff2-4b82-98d8-c9d6818ec746
-- title:
--   Degree16 18
-- statement:
--   Definitions and structural lemmas for Degree16 18, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
namespace Sendov
namespace B16_18
def Lc : ℤ := 720720
def betac : ℤ := 9632409706279062743041
def tauc : ℤ := 65604308031184443540574573963916799164579355278379645304399696021576697292522316333712207898845459456442843781680661940474008113586613026045908148093916427474204047696513917860869931635574183554403391853205017812541311293282390174744915537500427122031507443987808875231567434632560187716182055857676129052451323844518845444325992588835078239595296506721823714704265478805643382244491222183969521021663658026171379394048234274188519553
def Nmomc : List ℤ :=
  [52612659000000, 170273696400000, 255339685800000, 239918448960000, 165235950648000, 99966121176960, 96500543870016, 8976458195712, 533837640960, 20291420160, 478172160, 6377472, 36864]
end B16_18
end Sendov


