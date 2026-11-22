-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabNineteenthPilot
-- name    : row23_rh_supp_RHLowSlabNineteenthPilot
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:13:02.923043+00:00
-- url     : https://prove2.me/theorems/7ba19048-2ebc-4ed5-9453-0a9c79ed0e52
-- title:
--   Row 23 RH support: RHLowSlabNineteenthPilot
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
namespace RHLowSlabNineteenthPilot
def slab : SlabD := { candidate2 50 7 32 with
  L := Q.ofNat 5
  lo := Q.frac 219 32
  FD := 2
  U := Q.ofNat 14
  hi := Q.add (Q.frac 219 32) (Q.frac 1 32)
  m := 16
  xs := fun j => Q.frac ((16+j : Nat) : Int) 32
  cell := fun j => { H65K.Slab.S.cell j with
    a := 33 + 2*j, b := 0, q := 64, tn := 112384, rn := 1, rd := 32,
    w := Q.frac 1 64, hh := Q.frac 1 64 } }
theorem head_checked : slabHeadOK slab = true := by
  decide +kernel
theorem cell0_checked : cellOK slab 0 = true := by
  decide +kernel
end RHLowSlabNineteenthPilot
#print axioms RHLowSlabNineteenthPilot.head_checked
#print axioms RHLowSlabNineteenthPilot.cell0_checked


