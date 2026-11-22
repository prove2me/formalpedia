-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
-- name    : row23_rh_supp_RH67156EdgePieceTransfer
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:54:09.96387+00:00
-- url     : https://prove2.me/theorems/2501b3f2-6968-4ddc-86fd-e6f055d5eb2d
-- title:
--   Row 23 RH support: RH67156EdgePieceTransfer
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeRest
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156Edge

/-- A checked piece and the verified interval cover give the split edge input. -/
theorem pieceJ_of_checked (j : Nat) (hj : j < 41)
    (hp : Arb4.pieceOK proposed.tn proposed.tq proposed.N proposed.L (proposed.pc j) = true) :
    H11K.pieceJ withBoxes j = true := by
  have hm : proposed.m = 41 := rfl
  have hc := (List.all_eq_true.mp proposed_cover) j (by simpa [hm] using hj)
  simp only [Bool.and_eq_true] at hc
  unfold H11K.pieceJ
  simp only [Bool.and_eq_true]
  exact ⟨⟨hp, hc.1⟩, hc.2⟩

end RH67156Edge
#print axioms RH67156Edge.pieceJ_of_checked


