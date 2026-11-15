-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabBudgetProbe
-- name    : row23_rh_supp_RHLowSlabBudgetProbe
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:49:17.350495+00:00
-- url     : https://prove2.me/theorems/a5bc2b29-6c8d-4d74-94e6-dd555daec412
-- title:
--   Row 23 RH support: RHLowSlabBudgetProbe
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
def candidate (n : ℕ) (r : ℕ) : SlabD := { H65K.Slab.S with
  N := n, r0 := r, lo := Q.ofNat 6, hi := Q.add (Q.ofNat 6) (Q.frac 1 64),
  U := Q.ofNat 14, Qr := 10^20, L := Q.ofNat 8, R := Q.frac 1 32, FN := 1, FD := 14,
  m := 16, xs := fun j => Q.frac ((16+j : Nat) : Int) 32,
  cell := fun j => { H65K.Slab.S.cell j with
    a := 33 + 2*j, b := 0, q := 64, tn := 98432, rn := 1, rd := 32,
    w := Q.frac 1 64, hh := Q.frac 1 128 } }


