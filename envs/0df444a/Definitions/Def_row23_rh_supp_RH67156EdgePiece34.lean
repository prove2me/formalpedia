-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EdgePiece34
-- name    : row23_rh_supp_RH67156EdgePiece34
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:44:47.057138+00:00
-- url     : https://prove2.me/theorems/a2d3ceed-6219-41c6-911d-e76ee57f27e8
-- title:
--   Row 23 RH support: RH67156EdgePiece34
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeCandidate
import Definitions.Def_row23_rh_supp_RH67156FastPiece34Prefixes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH67156Edge

/-- The nineteenth contour piece, checked through short evaluator transitions. -/
theorem piece34_checked :
    Arb4.pieceOK proposed.tn proposed.tq proposed.N proposed.L (proposed.pc 34) = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 34).oc
      (proposed.N - 2) (StO.init (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) 5) =
      RH67156FastPiece34.state39 := by
    change runO RH67156FastPiece34.cfg RH67156FastPiece34.oc 19498
      RH67156FastPiece34.state00 = RH67156FastPiece34.state39
    exact RH67156FastPiece34.prefix06
  have h2 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 34).oc 1
      RH67156FastPiece34.state39 = RH67156FastPiece34.state40 := by
    change runO RH67156FastPiece34.cfg RH67156FastPiece34.oc 1
      RH67156FastPiece34.state39 = RH67156FastPiece34.state40
    exact RH67156FastPiece34.transition07
  unfold Arb4.pieceOK
  dsimp only
  rw [h1, h2]
  decide +kernel

end RH67156Edge
#print axioms RH67156Edge.piece34_checked


