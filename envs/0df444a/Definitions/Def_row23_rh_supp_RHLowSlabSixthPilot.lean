-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabSixthPilot
-- name    : row23_rh_supp_RHLowSlabSixthPilot
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:22:38.262729+00:00
-- url     : https://prove2.me/theorems/22199d41-9e6e-4244-a76d-d9e1c3e38869
-- title:
--   Row 23 RH support: RHLowSlabSixthPilot
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabBudgetProbe2
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000
noncomputable section
open Arb4 Arb4.Q
namespace RHLowSlabSixthPilot
def slab : SlabD := { candidate2 50 7 32 with
  L := Q.ofNat 5
  lo := Q.frac 103 16
  FD := 2
  U := Q.ofNat 14
  hi := Q.add (Q.frac 103 16) (Q.frac 1 32)
  m := 16
  xs := fun j => Q.frac ((16+j : Nat) : Int) 32
  cell := fun j => { H65K.Slab.S.cell j with
    a := 33 + 2*j, b := 0, q := 64, tn := 105728, rn := 1, rd := 32,
    w := Q.frac 1 64, hh := Q.frac 1 64 } }
theorem head_checked : slabHeadOK slab = true := by
  decide +kernel
theorem cell0_checked : cellOK slab 0 = true := by
  decide +kernel
end RHLowSlabSixthPilot
#print axioms RHLowSlabSixthPilot.head_checked
#print axioms RHLowSlabSixthPilot.cell0_checked


