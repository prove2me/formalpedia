-- Prove2me | Definitions.Def_row23_rh_supp_RH67156CountScalar
-- name    : row23_rh_supp_RH67156CountScalar
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:32:45.349573+00:00
-- url     : https://prove2.me/theorems/d58e114a-f0fe-428c-baf1-52d92a1d9938
-- title:
--   Row 23 RH support: RH67156CountScalar
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_ArdaRH65K_Count121Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH67156Count

def G1 : GamD := ⟨Q.ofNat 67156, 31, 30, 31, 30, 1, 1, 1, 1⟩
def enclosure : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250,
  Q.frac (-1) 1, Q.frac 1 2, Arb4.H1000.E_T121.Lo, Arb4.H1000.E_T121.Hi,
  Q.frac 27780300 100, Q.frac 27780340 100,
  Q.frac 27780300 100, Q.frac 27780340 100⟩

theorem scalar_check :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 67156) (Q.frac 67277 2)
      (Q.frac 4493691241 4) 88428 enclosure &&
      Arb4.k6sideB H65K.Count121.G0 G1 enclosure) = true := by
  decide +kernel
end RH67156Count
#print axioms RH67156Count.scalar_check


