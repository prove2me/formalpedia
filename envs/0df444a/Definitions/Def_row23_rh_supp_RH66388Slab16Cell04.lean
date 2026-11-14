-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Cell04
-- name    : row23_rh_supp_RH66388Slab16Cell04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:44:29.861523+00:00
-- url     : https://prove2.me/theorems/811f0d8e-bbad-41f7-b146-fbcb6d7fae1a
-- title:
--   Row 23 RH support: RH66388Slab16Cell04
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388Slab16Fast04Prefixes
import Definitions.Def_row23_rh_supp_RH66388Slab16Pilot04R016Rest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388TopSlab16R016
theorem cell04_checked : Arb4.cellOK slab 4 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 (slab.cell 4).tn slab.tq) (slab.cell 4).oc
      (slab.N - 2) (StO.init (ArbEcon.OrderK.cfg64 (slab.cell 4).tn slab.tq) 5) =
      RH66388Slab16Pilot04.state39 := by
    change runO RH66388Slab16Fast04.cfg RH66388Slab16Fast04.oc 19499 RH66388Slab16Fast04.state00 = RH66388Slab16Fast04.state39
    exact RH66388Slab16Fast04.prefix11
  have h2 : runO (ArbEcon.OrderK.cfg64 (slab.cell 4).tn slab.tq) (slab.cell 4).oc 1
      RH66388Slab16Pilot04.state39 = RH66388Slab16Pilot04.state40 := by
    change runO RH66388Slab16Fast04.cfg RH66388Slab16Fast04.oc 1 RH66388Slab16Fast04.state39 = RH66388Slab16Fast04.state40
    exact RH66388Slab16Fast04.transition12
  unfold Arb4.cellOK
  dsimp only
  rw [h1, h2]
  exact pilot04_rest
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.cell04_checked


