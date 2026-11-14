-- Prove2me | Definitions.Def_row23_rh_supp_RH66388CountScalar
-- name    : row23_rh_supp_RH66388CountScalar
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:35.126196+00:00
-- url     : https://prove2.me/theorems/fdad745d-0f52-4cf0-a624-bdad2ab2143b
-- title:
--   Row 23 RH support: RH66388CountScalar
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
namespace RH66388Count

def G1 : GamD := ⟨Q.ofNat 66388, 31, 30, 31, 30, 1, 1, 1, 1⟩
def enclosure : EnclQ := ⟨Q.frac (-249) 250, Q.frac 249 250,
  Q.frac 0 1, Q.frac 1 1, Arb4.H1000.E_T121.Lo, Arb4.H1000.E_T121.Hi,
  Q.frac 27424300 100, Q.frac 27424310 100,
  Q.frac 27424300 100, Q.frac 27424310 100⟩

theorem scalar_check :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 66388) (Q.frac 66509 2)
      (Q.frac 4391315305 4) 87295 enclosure &&
      Arb4.k6sideB H65K.Count121.G0 G1 enclosure) = true := by
  decide +kernel
end RH66388Count
#print axioms RH66388Count.scalar_check


