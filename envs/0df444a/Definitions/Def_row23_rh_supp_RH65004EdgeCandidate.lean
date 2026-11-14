-- Prove2me | Definitions.Def_row23_rh_supp_RH65004EdgeCandidate
-- name    : row23_rh_supp_RH65004EdgeCandidate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:21:13.225649+00:00
-- url     : https://prove2.me/theorems/2bc3676b-9fe6-4f24-a9fb-ef7788fdedb8
-- title:
--   Row 23 RH support: RH65004EdgeCandidate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_ArdaRH65K_Edge65000Data
import Definitions.Def_row23_rh_supp_RH65004EdgeOctants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH65004Edge

/-- Candidate contour with updated height, charts, and conservative scalar budgets. -/
def proposed : EdgeD := { H65K.Edge.E with
  tn := 65004
  pc := fun j => { H65K.Edge.E.pc j with
    kk := octant j
    U := Q.ofNat 65005
    Qr := (H65K.Edge.E.pc j).Qr * 1001 / 1000
    E := Q.mul (Q.ofNat 2) (H65K.Edge.E.pc j).E } }

/-- Adjacent proposed charts meet the edge checker's step condition. -/
theorem proposed_steps :
    (List.range (proposed.m - 1)).all
      (fun j => decide (|(proposed.pc (j + 1)).kk - (proposed.pc j).kk| ≤ 3)) = true := by
  decide +kernel

/-- The old horizontal intervals still cover the same contour. -/
theorem proposed_cover :
    (List.range proposed.m).all (fun j =>
      Arb4.inRad (proposed.x j) (proposed.pc j) &&
      Arb4.inRad (proposed.x (j + 1)) (proposed.pc j)) = true := by
  decide +kernel

/-- The magnitude-budget checks do not depend on the ordinate. -/
theorem proposed_growth :
    (List.range proposed.m).all (fun j => Arb4.gOK proposed.N (proposed.pc j)) = true := by
  decide +kernel

end RH65004Edge
#print axioms RH65004Edge.proposed_steps
#print axioms RH65004Edge.proposed_cover
#print axioms RH65004Edge.proposed_growth


