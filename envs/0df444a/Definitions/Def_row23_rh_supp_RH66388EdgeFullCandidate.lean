-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgeFullCandidate
-- name    : row23_rh_supp_RH66388EdgeFullCandidate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:26:08.313458+00:00
-- url     : https://prove2.me/theorems/183bb62c-917b-4f77-b266-169c1042bd2d
-- title:
--   Row 23 RH support: RH66388EdgeFullCandidate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeBoxes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH66388Edge
def withBoxes : EdgeD := { proposed with
  D0 := 1000000000
  reLo0 := 1052300000
  reHi0 := 1053200000
  imLo0 := 286500000
  imHi0 := 287500000
  Qp0 := H65K.Edge.E.Qp0 * 1460 / 1000
  Rn0 := H65K.Edge.E.Rn0 * 2
  Rd0 := H65K.Edge.E.Rd0
  qlo0 := qlo0
  qhi0 := qhi0
  D1 := 1000000000
  reLo1 := 800000000000000
  reHi1 := 1100000000000000
  imLo1 := 600000000000000
  imHi1 := 850000000000000
  Qp1 := H65K.Edge.E.Qp1 * 1460 / 1000
  Rn1 := H65K.Edge.E.Rn1 * 2
  Rd1 := H65K.Edge.E.Rd1
  qlo1 := qlo1
  qhi1 := qhi1
  Lo := Q.frac 0 1
  Hi := Q.frac 1 1 }
theorem edge_endpoints :
    Nat.ble 1 withBoxes.m = true ∧ Nat.ble 1 withBoxes.tn = true ∧
    Arb4.eqB (withBoxes.x 0) (Q.ofNat 2) = true ∧
    Arb4.eqB (withBoxes.x withBoxes.m) (Q.ofInt (-1)) = true ∧
    Arb4.eqB (withBoxes.pc 0).σQ (Q.ofNat 2) = true ∧
    Arb4.eqB (withBoxes.pc (withBoxes.m - 1)).σQ (Q.ofInt (-1)) = true := by
  decide +kernel
end RH66388Edge
#print axioms RH66388Edge.edge_endpoints


