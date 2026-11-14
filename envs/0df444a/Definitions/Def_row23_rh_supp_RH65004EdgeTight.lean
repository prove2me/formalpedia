-- Prove2me | Definitions.Def_row23_rh_supp_RH65004EdgeTight
-- name    : row23_rh_supp_RH65004EdgeTight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:22:13.980195+00:00
-- url     : https://prove2.me/theorems/d4c7de45-671b-4f1e-b130-1d8b7275f69f
-- title:
--   Row 23 RH support: RH65004EdgeTight
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65004EdgeCandidate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH65004Edge

/-- Candidate with a tight remainder enlargement to retain the original budgets. -/
def tight : EdgeD := { proposed with
  pc := fun j => { proposed.pc j with
    E := Q.mul (Q.frac 1001 1000) (H65K.Edge.E.pc j).E } }

/-- All forty-one candidate remainder inequalities hold. -/
theorem tight_remainders :
    (List.range tight.m).all (fun j => Arb4.remOK tight.tn tight.tq tight.N (tight.pc j)) = true := by
  decide +kernel

/-- All forty-one candidate error budgets hold. -/
theorem tight_budgets :
    (List.range tight.m).all (fun j => Arb4.budgetOK tight.N tight.L (tight.pc j)) = true := by
  decide +kernel

end RH65004Edge
#print axioms RH65004Edge.tight_remainders
#print axioms RH65004Edge.tight_budgets


