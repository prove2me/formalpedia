-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgeCandidate
-- name    : row23_rh_supp_RH66388EdgeCandidate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:23:21.129602+00:00
-- url     : https://prove2.me/theorems/afb15a6a-20f8-4d96-86f7-d5d610e25466
-- title:
--   Row 23 RH support: RH66388EdgeCandidate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65004EdgeTight
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH66388Edge

def octant (j : Nat) : Int := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Int).getD j 0

def proposed : EdgeD := { RH65004Edge.tight with
  tn := 66388
  pc := fun j => { RH65004Edge.tight.pc j with kk := octant j, U := Q.ofNat 66389, E := Q.mul (Q.frac 1460 1000) (RH65004Edge.tight.pc j).E, Qr := (RH65004Edge.tight.pc j).Qr * 1460 / 1000, FN := (RH65004Edge.tight.pc j).FN * 170, FD := (RH65004Edge.tight.pc j).FD * 100 } }

theorem proposed_steps :
    (List.range (proposed.m - 1)).all
      (fun j => decide (|(proposed.pc (j + 1)).kk - (proposed.pc j).kk| ≤ 3)) = true := by
  decide +kernel

theorem proposed_cover :
    (List.range proposed.m).all (fun j =>
      Arb4.inRad (proposed.x j) (proposed.pc j) &&
      Arb4.inRad (proposed.x (j + 1)) (proposed.pc j)) = true := by
  decide +kernel

theorem proposed_growth :
    (List.range proposed.m).all (fun j => Arb4.gOK proposed.N (proposed.pc j)) = true := by
  decide +kernel

theorem proposed_remainders :
    (List.range proposed.m).all (fun j => Arb4.remOK proposed.tn proposed.tq proposed.N (proposed.pc j)) = true := by
  decide +kernel

theorem proposed_budgets :
    (List.range proposed.m).all (fun j => Arb4.budgetOK proposed.N proposed.L (proposed.pc j)) = true := by
  decide +kernel
end RH66388Edge
#print axioms RH66388Edge.proposed_steps
#print axioms RH66388Edge.proposed_cover
#print axioms RH66388Edge.proposed_growth
#print axioms RH66388Edge.proposed_remainders
#print axioms RH66388Edge.proposed_budgets


