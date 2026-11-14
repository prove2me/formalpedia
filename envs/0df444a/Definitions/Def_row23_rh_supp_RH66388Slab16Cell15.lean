-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Cell15
-- name    : row23_rh_supp_RH66388Slab16Cell15
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:26.733453+00:00
-- url     : https://prove2.me/theorems/98157d4e-d1f8-4c9f-b058-dc876a1eedf8
-- title:
--   Row 23 RH support: RH66388Slab16Cell15
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast15Prefixes
import Definitions.Def_row23_rh_supp_RH66388Slab16Pilot15R016Rest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388TopSlab16R016
theorem cell15_checked : Arb4.cellOK slab 15 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 (slab.cell 15).tn slab.tq) (slab.cell 15).oc
      (slab.N - 2) (StO.init (ArbEcon.OrderK.cfg64 (slab.cell 15).tn slab.tq) 5) =
      RH66388Slab16Pilot15.state39 := by
    change runO RH66388Slab16Fast15.cfg RH66388Slab16Fast15.oc 19499 RH66388Slab16Fast15.state00 = RH66388Slab16Fast15.state39
    exact RH66388Slab16Fast15.prefix11
  have h2 : runO (ArbEcon.OrderK.cfg64 (slab.cell 15).tn slab.tq) (slab.cell 15).oc 1
      RH66388Slab16Pilot15.state39 = RH66388Slab16Pilot15.state40 := by
    change runO RH66388Slab16Fast15.cfg RH66388Slab16Fast15.oc 1 RH66388Slab16Fast15.state39 = RH66388Slab16Fast15.state40
    exact RH66388Slab16Fast15.transition12
  unfold Arb4.cellOK
  dsimp only
  rw [h1, h2]
  exact pilot15_rest
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.cell15_checked


