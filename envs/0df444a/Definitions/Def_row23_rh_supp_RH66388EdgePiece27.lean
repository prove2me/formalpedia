-- Prove2me | Definitions.Def_row23_rh_supp_RH66388EdgePiece27
-- name    : row23_rh_supp_RH66388EdgePiece27
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:36:17.705465+00:00
-- url     : https://prove2.me/theorems/f2e7f78a-4c3d-4254-b38b-4de62ea64136
-- title:
--   Row 23 RH support: RH66388EdgePiece27
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeCandidate
import Definitions.Def_row23_rh_supp_RH66388FastPiece27Prefixes
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 20000000
noncomputable section
open ArbEcon ArbEcon.Off
namespace RH66388Edge

/-- The nineteenth contour piece, checked through short evaluator transitions. -/
theorem piece27_checked :
    Arb4.pieceOK proposed.tn proposed.tq proposed.N proposed.L (proposed.pc 27) = true := by
  have h1 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 27).oc
      (proposed.N - 2) (StO.init (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) 5) =
      RH66388FastPiece27.state39 := by
    change runO RH66388FastPiece27.cfg RH66388FastPiece27.oc 19498
      RH66388FastPiece27.state00 = RH66388FastPiece27.state39
    exact RH66388FastPiece27.prefix06
  have h2 : runO (ArbEcon.OrderK.cfg64 proposed.tn proposed.tq) (proposed.pc 27).oc 1
      RH66388FastPiece27.state39 = RH66388FastPiece27.state40 := by
    change runO RH66388FastPiece27.cfg RH66388FastPiece27.oc 1
      RH66388FastPiece27.state39 = RH66388FastPiece27.state40
    exact RH66388FastPiece27.transition07
  unfold Arb4.pieceOK
  dsimp only
  rw [h1, h2]
  decide +kernel

end RH66388Edge
#print axioms RH66388Edge.piece27_checked


