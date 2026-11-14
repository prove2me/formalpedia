-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgeBoxes
-- name    : row23_rh_supp_RH66388EdgeBoxes
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:24:33.008717+00:00
-- url     : https://prove2.me/theorems/d40d5f8f-af15-49e1-aca7-ce022e29719c
-- title:
--   Row 23 RH support: RH66388EdgeBoxes
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeCandidate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
namespace RH66388Edge
def rlo0 : Q := Q.frac 1052300000 1000000000
def rhi0 : Q := Q.frac 1053200000 1000000000
def ilo0 : Q := Q.frac 286500000 1000000000
def ihi0 : Q := Q.frac 287500000 1000000000
def rlo1 : Q := Q.frac 800000000000000 1000000000
def rhi1 : Q := Q.frac 1100000000000000 1000000000
def ilo1 : Q := Q.frac 600000000000000 1000000000
def ihi1 : Q := Q.frac 850000000000000 1000000000
def qlo0 : Q := Q.frac 26 100
def qhi0 : Q := Q.frac 28 100
def qlo1 : Q := Q.frac (-35) 100
def qhi1 : Q := Q.frac 5 100
theorem endpoint0_corners :
    cornerOK 1 0 rlo0 ilo0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rlo0 ihi0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rhi0 ilo0 qlo0 qhi0 = true ∧
    cornerOK 1 0 rhi0 ihi0 qlo0 qhi0 = true := by decide +kernel
theorem endpoint1_corners :
    cornerOK 1 1 rlo1 ilo1 qlo1 qhi1 = true ∧
    cornerOK 1 1 rlo1 ihi1 qlo1 qhi1 = true ∧
    cornerOK 1 1 rhi1 ilo1 qlo1 qhi1 = true ∧
    cornerOK 1 1 rhi1 ihi1 qlo1 qhi1 = true := by decide +kernel
theorem argument_budget :
    finalLoOK 1 qhi0 qlo1 (Q.frac 0 1) = true ∧
    finalHiOK 1 qlo0 qhi1 (Q.frac 1 1) = true := by decide +kernel
end RH66388Edge
#print axioms RH66388Edge.endpoint0_corners
#print axioms RH66388Edge.endpoint1_corners
#print axioms RH66388Edge.argument_budget


