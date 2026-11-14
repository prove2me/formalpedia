-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Cell00
-- name    : row23_rh_supp_RH66388Slab16Cell00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:42:03.152293+00:00
-- url     : https://prove2.me/theorems/59421159-4a5d-41f2-9219-969f1c515383
-- title:
--   Row 23 RH support: RH66388Slab16Cell00
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast00Prefixes
import Definitions.Def_row23_rh_supp_RH66388Slab16Pilot00R016Rest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388TopSlab16R016
theorem cell00_checked : Arb4.cellOK slab 0 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 (slab.cell 0).tn slab.tq) (slab.cell 0).oc
      (slab.N - 2) (StO.init (ArbEcon.OrderK.cfg64 (slab.cell 0).tn slab.tq) 5) =
      RH66388Slab16Pilot00.state39 := by
    change runO RH66388Slab16Fast00.cfg RH66388Slab16Fast00.oc 19499 RH66388Slab16Fast00.state00 = RH66388Slab16Fast00.state39
    exact RH66388Slab16Fast00.prefix11
  have h2 : runO (ArbEcon.OrderK.cfg64 (slab.cell 0).tn slab.tq) (slab.cell 0).oc 1
      RH66388Slab16Pilot00.state39 = RH66388Slab16Pilot00.state40 := by
    change runO RH66388Slab16Fast00.cfg RH66388Slab16Fast00.oc 1 RH66388Slab16Fast00.state39 = RH66388Slab16Fast00.state40
    exact RH66388Slab16Fast00.transition12
  unfold Arb4.cellOK
  dsimp only
  rw [h1, h2]
  exact pilot00_rest
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.cell00_checked


