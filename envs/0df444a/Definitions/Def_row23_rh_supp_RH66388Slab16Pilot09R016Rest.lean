-- Prove2me | Definitions.Def_row23_rh_supp_RH66388Slab16Pilot09R016Rest
-- name    : row23_rh_supp_RH66388Slab16Pilot09R016Rest
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:46:40.0512+00:00
-- url     : https://prove2.me/theorems/b789ae07-6a0f-46a5-9c38-dcbe8ec800e8
-- title:
--   Row 23 RH support: RH66388Slab16Pilot09R016Rest
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388TopSlab16R016Data
import Definitions.Def_row23_rh_supp_RH66388Slab16Pilot09Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open ArbEcon ArbEcon.Off Arb4 Arb4.Q
namespace RH66388TopSlab16R016

theorem pilot09_rest :
  let S := slab
  let C := S.cell 9
  let c := ArbEcon.OrderK.cfg64 C.tn S.tq
  let s1 := RH66388Slab16Pilot09.state39
  let sN := RH66388Slab16Pilot09.state40
  Nat.ble 2 S.N && Nat.ble 1 C.q && Nat.ble 1 C.rd && Nat.ble C.b C.a &&
    ArbEcon.Off.checkCell c C.oc 6 S.N 5 s1.acc sN.acc C.rn C.rd S.FN S.FD &&
    Q.le (Q.frac (C.rn : ℤ) C.rd) S.R && Q.le (Q.ofNat sN.lhi) (Q.mul S.L (Q.ofNat (2 ^ 64))) &&
    Q.le S.lo (Arb4.tQ C.tn S.tq) &&
    Q.le (Q.add (Q.npow (Q.add C.σQ (Q.ofNat 11)) 2) (Q.npow (Arb4.tQ C.tn S.tq) 2)) (Q.npow S.U 2) &&
    Q.le (Q.qabs (Q.sub (S.xs 9) C.σQ)) C.w && Q.le (Q.qabs (Q.sub (S.xs (9+1)) C.σQ)) C.w &&
    Q.le (Q.qabs (Q.sub S.lo (Arb4.tQ C.tn S.tq))) C.hh && Q.le (Q.qabs (Q.sub S.hi (Arb4.tQ C.tn S.tq))) C.hh &&
    Q.le (Q.add (Q.npow C.w 2) (Q.npow C.hh 2)) (Q.npow (Q.frac (C.rn : ℤ) C.rd) 2) = true := by
  decide +kernel
end RH66388TopSlab16R016
#print axioms RH66388TopSlab16R016.pilot09_rest


