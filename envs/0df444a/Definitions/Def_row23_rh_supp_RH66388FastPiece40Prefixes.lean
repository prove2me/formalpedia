-- Prove2me | Definitions.Def_row23_rh_supp_RH66388FastPiece40Prefixes
-- name    : row23_rh_supp_RH66388FastPiece40Prefixes
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:22:04.689292+00:00
-- url     : https://prove2.me/theorems/fed1a9e6-68c2-4af4-a0ac-c6029c99ff93
-- title:
--   Row 23 RH support: RH66388FastPiece40Prefixes
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block01
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block02
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block03
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block04
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block05
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block06
import Definitions.Def_row23_rh_supp_RH66388FastPiece40Block07
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388FastPiece40

theorem prefix01 : runO cfg oc 4000 state00 = state08 := transition01

theorem prefix02 : runO cfg oc 8000 state00 = state16 := by
  calc
    runO cfg oc 8000 state00 = runO cfg oc 4000 (runO cfg oc 4000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 4000 4000 state00
    _ = state16 := by rw [prefix01, transition02]

theorem prefix03 : runO cfg oc 12000 state00 = state24 := by
  calc
    runO cfg oc 12000 state00 = runO cfg oc 4000 (runO cfg oc 8000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 8000 4000 state00
    _ = state24 := by rw [prefix02, transition03]

theorem prefix04 : runO cfg oc 16000 state00 = state32 := by
  calc
    runO cfg oc 16000 state00 = runO cfg oc 4000 (runO cfg oc 12000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 12000 4000 state00
    _ = state32 := by rw [prefix03, transition04]

theorem prefix05 : runO cfg oc 19000 state00 = state38 := by
  calc
    runO cfg oc 19000 state00 = runO cfg oc 3000 (runO cfg oc 16000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 16000 3000 state00
    _ = state38 := by rw [prefix04, transition05]

theorem prefix06 : runO cfg oc 19498 state00 = state39 := by
  calc
    runO cfg oc 19498 state00 = runO cfg oc 498 (runO cfg oc 19000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 19000 498 state00
    _ = state39 := by rw [prefix05, transition06]

theorem prefix07 : runO cfg oc 19499 state00 = state40 := by
  calc
    runO cfg oc 19499 state00 = runO cfg oc 1 (runO cfg oc 19498 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 19498 1 state00
    _ = state40 := by rw [prefix06, transition07]

end RH66388FastPiece40
#print axioms RH66388FastPiece40.prefix06
#print axioms RH66388FastPiece40.prefix07


