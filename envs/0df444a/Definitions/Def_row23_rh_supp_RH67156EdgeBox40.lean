-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EdgeBox40
-- name    : row23_rh_supp_RH67156EdgeBox40
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:52:26.845339+00:00
-- url     : https://prove2.me/theorems/a88b53d7-0972-4ad2-bb55-13d162df5a49
-- title:
--   Row 23 RH support: RH67156EdgeBox40
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeFullCandidate
import Definitions.Def_row23_rh_supp_RH67156FastPiece40Prefixes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Edge

theorem endpoint1_checked :
    Arb4.boxOK withBoxes.tn withBoxes.tq withBoxes.N (withBoxes.pc 40)
      withBoxes.D1 withBoxes.reLo1 withBoxes.reHi1 withBoxes.imLo1 withBoxes.imHi1
      withBoxes.Qp1 withBoxes.Rn1 withBoxes.Rd1 withBoxes.qlo1 withBoxes.qhi1 = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) (withBoxes.pc 40).oc
      (withBoxes.N - 2) (StO.init (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) 5) =
      RH67156FastPiece40.state39 := by
    change runO RH67156FastPiece40.cfg RH67156FastPiece40.oc 19498
      RH67156FastPiece40.state00 = RH67156FastPiece40.state39
    exact RH67156FastPiece40.prefix06
  have h2 : runO (ArbEcon.OrderK.cfg64 withBoxes.tn withBoxes.tq) (withBoxes.pc 40).oc 1
      RH67156FastPiece40.state39 = RH67156FastPiece40.state40 := by
    change runO RH67156FastPiece40.cfg RH67156FastPiece40.oc 1
      RH67156FastPiece40.state39 = RH67156FastPiece40.state40
    exact RH67156FastPiece40.transition07
  unfold Arb4.boxOK
  dsimp only
  rw [h1, h2]
  decide +kernel
end RH67156Edge
#print axioms RH67156Edge.endpoint1_checked


