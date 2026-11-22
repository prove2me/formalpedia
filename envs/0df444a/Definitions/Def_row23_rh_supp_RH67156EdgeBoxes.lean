-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EdgeBoxes
-- name    : row23_rh_supp_RH67156EdgeBoxes
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:42:20.137611+00:00
-- url     : https://prove2.me/theorems/3830a24a-c123-418e-ada1-53107a859701
-- title:
--   Row 23 RH support: RH67156EdgeBoxes
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeCandidate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH67156Edge
def rlo0 : Q := Q.frac 848000000 1000000000
def rhi0 : Q := Q.frac 852000000 1000000000
def ilo0 : Q := Q.frac (-112000000) 1000000000
def ihi0 : Q := Q.frac (-108000000) 1000000000
def rlo1 : Q := Q.frac 800000000000000 1000000000
def rhi1 : Q := Q.frac 975000000000000 1000000000
def ilo1 : Q := Q.frac (-420000000000000) 1000000000
def ihi1 : Q := Q.frac (-250000000000000) 1000000000
def qlo0 : Q := Q.frac (-14) 100
def qhi0 : Q := Q.frac (-12) 100
def qlo1 : Q := Q.frac (-53) 100
def qhi1 : Q := Q.frac (-25) 100
theorem endpoint0_corners :
    cornerOK 1 0 rlo0 ilo0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rlo0 ihi0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rhi0 ilo0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rhi0 ihi0 qlo0 qhi0 = true := by decide +kernel
theorem endpoint1_corners :
    cornerOK 1 0 rlo1 ilo1 qlo1 qhi1 = true ∧
    cornerOK 1 0 rlo1 ihi1 qlo1 qhi1 = true ∧
    cornerOK 1 0 rhi1 ilo1 qlo1 qhi1 = true ∧
    cornerOK 1 0 rhi1 ihi1 qlo1 qhi1 = true := by decide +kernel
theorem argument_budget :
    finalLoOK 0 qhi0 qlo1 (Q.frac (-1) 1) = true ∧
    finalHiOK 0 qlo0 qhi1 (Q.frac 1 2) = true := by decide +kernel
end RH67156Edge
#print axioms RH67156Edge.endpoint0_corners
#print axioms RH67156Edge.endpoint1_corners
#print axioms RH67156Edge.argument_budget


