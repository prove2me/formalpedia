-- Prove2me | Definitions.Def_row23_rh_supp_RH65004EdgeOctants
-- name    : row23_rh_supp_RH65004EdgeOctants
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:18.629008+00:00
-- url     : https://prove2.me/theorems/7f7d4d78-7790-48f4-928f-7cefd1d1b440
-- title:
--   Row 23 RH support: RH65004EdgeOctants
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65004Edge

/-- Candidate chart indices for the horizontal contour at height 65004. -/
def octant (j : Nat) : Int := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), (-1), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2), (-2)] : List Int).getD j 0

/-- The proposed charts satisfy the required adjacent-step condition. -/
theorem octant_steps :
    (List.range 40).all (fun j => decide (|octant (j + 1) - octant j| ≤ 3)) = true := by
  decide

end RH65004Edge
#print axioms RH65004Edge.octant_steps


