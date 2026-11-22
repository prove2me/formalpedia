-- Prove2me | Definitions.Def_row23_rh_supp_RH67156Slab16Cell08
-- name    : row23_rh_supp_RH67156Slab16Cell08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:15:07.526974+00:00
-- url     : https://prove2.me/theorems/255ec045-10f3-4f2e-b8d7-ce7fb85f0250
-- title:
--   Row 23 RH support: RH67156Slab16Cell08
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156Slab16Fast08Prefixes
import Definitions.Def_row23_rh_supp_RH67156Slab16Pilot08R016Rest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156TopSlab16R016
theorem cell08_checked : Arb4.cellOK slab 8 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 (slab.cell 8).tn slab.tq) (slab.cell 8).oc
      (slab.N - 2) (StO.init (ArbEcon.OrderK.cfg64 (slab.cell 8).tn slab.tq) 5) =
      RH67156Slab16Pilot08.state39 := by
    change runO RH67156Slab16Fast08.cfg RH67156Slab16Fast08.oc 19499 RH67156Slab16Fast08.state00 = RH67156Slab16Fast08.state39
    exact RH67156Slab16Fast08.prefix11
  have h2 : runO (ArbEcon.OrderK.cfg64 (slab.cell 8).tn slab.tq) (slab.cell 8).oc 1
      RH67156Slab16Pilot08.state39 = RH67156Slab16Pilot08.state40 := by
    change runO RH67156Slab16Fast08.cfg RH67156Slab16Fast08.oc 1 RH67156Slab16Fast08.state39 = RH67156Slab16Fast08.state40
    exact RH67156Slab16Fast08.transition12
  unfold Arb4.cellOK
  dsimp only
  rw [h1, h2]
  exact pilot08_rest
end RH67156TopSlab16R016
#print axioms RH67156TopSlab16R016.cell08_checked


