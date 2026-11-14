-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Prefixes
-- name    : row23_rh_supp_RH66388Slab16Fast15Prefixes
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:18.074786+00:00
-- url     : https://prove2.me/theorems/53fc345c-7713-4c5d-bd83-b19908b61302
-- title:
--   Row 23 RH support: RH66388Slab16Fast15Prefixes
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block01
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block02
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block03
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block04
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block05
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block06
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block07
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block08
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block09
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block10
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block11
import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Block12
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Slab16Fast15
theorem prefix01 : runO cfg oc 2000 state00 = state04 := transition01
theorem prefix02 : runO cfg oc 4000 state00 = state08 := by
  calc
    runO cfg oc 4000 state00 = runO cfg oc 2000 (runO cfg oc 2000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 2000 2000 state00
    _ = state08 := by rw [prefix01, transition02]
theorem prefix03 : runO cfg oc 6000 state00 = state12 := by
  calc
    runO cfg oc 6000 state00 = runO cfg oc 2000 (runO cfg oc 4000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 4000 2000 state00
    _ = state12 := by rw [prefix02, transition03]
theorem prefix04 : runO cfg oc 8000 state00 = state16 := by
  calc
    runO cfg oc 8000 state00 = runO cfg oc 2000 (runO cfg oc 6000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 6000 2000 state00
    _ = state16 := by rw [prefix03, transition04]
theorem prefix05 : runO cfg oc 10000 state00 = state20 := by
  calc
    runO cfg oc 10000 state00 = runO cfg oc 2000 (runO cfg oc 8000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 8000 2000 state00
    _ = state20 := by rw [prefix04, transition05]
theorem prefix06 : runO cfg oc 12000 state00 = state24 := by
  calc
    runO cfg oc 12000 state00 = runO cfg oc 2000 (runO cfg oc 10000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 10000 2000 state00
    _ = state24 := by rw [prefix05, transition06]
theorem prefix07 : runO cfg oc 14000 state00 = state28 := by
  calc
    runO cfg oc 14000 state00 = runO cfg oc 2000 (runO cfg oc 12000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 12000 2000 state00
    _ = state28 := by rw [prefix06, transition07]
theorem prefix08 : runO cfg oc 16000 state00 = state32 := by
  calc
    runO cfg oc 16000 state00 = runO cfg oc 2000 (runO cfg oc 14000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 14000 2000 state00
    _ = state32 := by rw [prefix07, transition08]
theorem prefix09 : runO cfg oc 18000 state00 = state36 := by
  calc
    runO cfg oc 18000 state00 = runO cfg oc 2000 (runO cfg oc 16000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 16000 2000 state00
    _ = state36 := by rw [prefix08, transition09]
theorem prefix10 : runO cfg oc 19000 state00 = state38 := by
  calc
    runO cfg oc 19000 state00 = runO cfg oc 1000 (runO cfg oc 18000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 18000 1000 state00
    _ = state38 := by rw [prefix09, transition10]
theorem prefix11 : runO cfg oc 19499 state00 = state39 := by
  calc
    runO cfg oc 19499 state00 = runO cfg oc 499 (runO cfg oc 19000 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 19000 499 state00
    _ = state39 := by rw [prefix10, transition11]
theorem prefix12 : runO cfg oc 19500 state00 = state40 := by
  calc
    runO cfg oc 19500 state00 = runO cfg oc 1 (runO cfg oc 19499 state00) := by
      simpa only using RH65000ExtendedSlab.runO_add cfg oc 19499 1 state00
    _ = state40 := by rw [prefix11, transition12]
end RH66388Slab16Fast15
#print axioms RH66388Slab16Fast15.prefix11
#print axioms RH66388Slab16Fast15.prefix12


