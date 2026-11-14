-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgePiece31
-- name    : row23_rh_supp_RH66388EdgePiece31
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:37:45.703736+00:00
-- url     : https://prove2.me/theorems/0e15fc4a-7207-4e7d-86f4-6af7eeb40256
-- title:
--   Row 23 RH support: RH66388EdgePiece31
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeCandidate
import Definitions.Def_row23_rh_supp_RH66388FastPiece31Prefixes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Edge

/-- The nineteenth contour piece, checked through short evaluator transitions. -/
theorem piece31_checked :
    Arb4.pieceOK proposed.tn proposed.tq proposed.N proposed.L (proposed.pc 31) = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 31).oc
      (proposed.N - 2) (StO.init (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) 5) =
      RH66388FastPiece31.state39 := by
    change runO RH66388FastPiece31.cfg RH66388FastPiece31.oc 19498
      RH66388FastPiece31.state00 = RH66388FastPiece31.state39
    exact RH66388FastPiece31.prefix06
  have h2 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 31).oc 1
      RH66388FastPiece31.state39 = RH66388FastPiece31.state40 := by
    change runO RH66388FastPiece31.cfg RH66388FastPiece31.oc 1
      RH66388FastPiece31.state39 = RH66388FastPiece31.state40
    exact RH66388FastPiece31.transition07
  unfold Arb4.pieceOK
  dsimp only
  rw [h1, h2]
  decide +kernel

end RH66388Edge
#print axioms RH66388Edge.piece31_checked


