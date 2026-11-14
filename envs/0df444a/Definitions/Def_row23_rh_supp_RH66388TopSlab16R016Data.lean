-- Prove2me | Definitions.Def_row23_rh_supp_RH66388TopSlab16R016Data
-- name    : row23_rh_supp_RH66388TopSlab16R016Data
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:48.118901+00:00
-- url     : https://prove2.me/theorems/c2a60ba0-2ae3-450d-a3fe-4d94d962996f
-- title:
--   Row 23 RH support: RH66388TopSlab16R016Data
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH66388TopSlab16R016

def slab : SlabD := { H65K.Slab.S with
  lo := Q.ofNat 66388
  hi := Q.add (Q.ofNat 66388) (Q.frac 25 8192)
  U := Q.ofNat 66389
  Qr := H65K.Slab.S.Qr * 1460 / 1000
  R := Q.frac 2 125
  FN := 1
  FD := 14
  m := 16
  xs := fun j => Q.frac ((16+j : Nat) : Int) 32
  cell := fun j => { H65K.Slab.S.cell j with
    a := 33 + 2*j, b := 0, q := 64, tn := 1087701017, rn := 2, rd := 125,
    w := Q.frac 1 64, hh := Q.frac 25 16384 } }

theorem head_checked : slabHeadOK slab = true := by
  decide +kernel

theorem cell_height_checked (j : Nat) (hj : j < 16) :
    Q.le (Q.qabs (Q.sub slab.lo (tQ (slab.cell j).tn slab.tq))) (slab.cell j).hh = true ∧
    Q.le (Q.qabs (Q.sub slab.hi (tQ (slab.cell j).tn slab.tq))) (slab.cell j).hh = true := by
  interval_cases j <;> decide
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.head_checked
#print axioms RH66388TopSlab16R016.cell_height_checked


