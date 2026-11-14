-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Cell06
-- name    : row23_rh_supp_RH66388Slab16Cell06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:46:00.937671+00:00
-- url     : https://prove2.me/theorems/8636ccd4-7a81-47bb-bb90-8e255cf84dae
-- title:
--   Row 23 RH support: RH66388Slab16Cell06
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast06Prefixes
import Definitions.Def_row23_rh_supp_RH66388Slab16Pilot06R016Rest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388TopSlab16R016
theorem cell06_checked : Arb4.cellOK slab 6 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 (slab.cell 6).tn slab.tq) (slab.cell 6).oc
      (slab.N - 2) (StO.init (ArbEcon.OrderK.cfg64 (slab.cell 6).tn slab.tq) 5) =
      RH66388Slab16Pilot06.state39 := by
    change runO RH66388Slab16Fast06.cfg RH66388Slab16Fast06.oc 19499 RH66388Slab16Fast06.state00 = RH66388Slab16Fast06.state39
    exact RH66388Slab16Fast06.prefix11
  have h2 : runO (ArbEcon.OrderK.cfg64 (slab.cell 6).tn slab.tq) (slab.cell 6).oc 1
      RH66388Slab16Pilot06.state39 = RH66388Slab16Pilot06.state40 := by
    change runO RH66388Slab16Fast06.cfg RH66388Slab16Fast06.oc 1 RH66388Slab16Fast06.state39 = RH66388Slab16Fast06.state40
    exact RH66388Slab16Fast06.transition12
  unfold Arb4.cellOK
  dsimp only
  rw [h1, h2]
  exact pilot06_rest
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.cell06_checked


