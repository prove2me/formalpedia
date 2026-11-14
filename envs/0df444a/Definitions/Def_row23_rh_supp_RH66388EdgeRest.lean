-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgeRest
-- name    : row23_rh_supp_RH66388EdgeRest
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:28:58.127376+00:00
-- url     : https://prove2.me/theorems/2426fafd-282d-4c8a-bb6b-c078595d64af
-- title:
--   Row 23 RH support: RH66388EdgeRest
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeBox00
import Definitions.Def_row23_rh_supp_RH66388EdgeBox40
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
open Arb4 Arb4.Q
namespace RH66388Edge

/-- All edge-checker conditions except the separately checked contour pieces. -/
theorem edge_rest_checked : H11K.edgeRest withBoxes = true := by
  rcases edge_endpoints with ⟨hm, ht, hx0, hxm, hc0, hc1⟩
  have hsteps : (List.range (withBoxes.m - 1)).all
      (fun j => decide (|(withBoxes.pc (j + 1)).kk - (withBoxes.pc j).kk| ≤ 3)) = true := by
    change (List.range (proposed.m - 1)).all
      (fun j => decide (|(proposed.pc (j + 1)).kk - (proposed.pc j).kk| ≤ 3)) = true
    exact proposed_steps
  have hlo : finalLoOK ((withBoxes.pc (withBoxes.m - 1)).kk - (withBoxes.pc 0).kk)
      withBoxes.qhi0 withBoxes.qlo1 withBoxes.Lo = true := by
    change finalLoOK 1 qhi0 qlo1 (Q.frac 0 1) = true
    exact argument_budget.1
  have hhi : finalHiOK ((withBoxes.pc (withBoxes.m - 1)).kk - (withBoxes.pc 0).kk)
      withBoxes.qlo0 withBoxes.qhi1 withBoxes.Hi = true := by
    change finalHiOK 1 qlo0 qhi1 (Q.frac 1 1) = true
    exact argument_budget.2
  simp only [H11K.edgeRest, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, ht⟩, hx0⟩, hxm⟩, hsteps⟩, hc0⟩, hc1⟩, endpoint0_checked⟩, endpoint1_checked⟩, hlo⟩, hhi⟩

end RH66388Edge
#print axioms RH66388Edge.edge_rest_checked


