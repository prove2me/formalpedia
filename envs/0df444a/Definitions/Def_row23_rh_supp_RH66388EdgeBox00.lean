-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgeBox00
-- name    : row23_rh_supp_RH66388EdgeBox00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:27:31.145924+00:00
-- url     : https://prove2.me/theorems/0041f230-c8d9-4fbb-a631-2f073f363901
-- title:
--   Row 23 RH support: RH66388EdgeBox00
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeFullCandidate
import Definitions.Def_row23_rh_supp_RH66388FastPiece00Prefixes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Edge

theorem endpoint0_checked :
    Arb4.boxOK withBoxes.tn withBoxes.tq withBoxes.N (withBoxes.pc 0)
      withBoxes.D0 withBoxes.reLo0 withBoxes.reHi0 withBoxes.imLo0 withBoxes.imHi0
      withBoxes.Qp0 withBoxes.Rn0 withBoxes.Rd0 withBoxes.qlo0 withBoxes.qhi0 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) (withBoxes.pc 0).oc
      (withBoxes.N - 2) (StO.init (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) 5) =
      RH66388FastPiece00.state39 := by
    change runO RH66388FastPiece00.cfg RH66388FastPiece00.oc 19498
      RH66388FastPiece00.state00 = RH66388FastPiece00.state39
    exact RH66388FastPiece00.prefix06
  have h2 : runO (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) (withBoxes.pc 0).oc 1
      RH66388FastPiece00.state39 = RH66388FastPiece00.state40 := by
    change runO RH66388FastPiece00.cfg RH66388FastPiece00.oc 1
      RH66388FastPiece00.state39 = RH66388FastPiece00.state40
    exact RH66388FastPiece00.transition07
  unfold Arb4.boxOK
  dsimp only
  rw [h1, h2]
  decide +kernel
end RH66388Edge
#print axioms RH66388Edge.endpoint0_checked


