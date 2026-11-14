-- Prove2me | Definitions.Def_row23_rh_supp_RH66388UpperEdgeConditional
-- name    : row23_rh_supp_RH66388UpperEdgeConditional
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:30:32.32009+00:00
-- url     : https://prove2.me/theorems/929a028e-b8b3-49e9-8a92-e13c626875fa
-- title:
--   Row 23 RH support: RH66388UpperEdgeConditional
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeRest
import Definitions.Def_row23_rh_supp_RH66388CountScalar
import Theorems.Thm_H11K_edge_sound_of_split
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388Edge

/-- The top argument enclosure follows from the explicitly supplied piece checks. -/
theorem upper_edge_of_pieces
    (hp : ∀ j, j < withBoxes.m → H11K.pieceJ withBoxes j = true) :
    DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L2.val RH66388Count.enclosure.H2.val := by
  have ht : withBoxes.T = (66388 : ℝ) := by
    norm_num [Arb4.EdgeD.T, withBoxes, proposed, RH65004Edge.tight, RH65004Edge.proposed, H65K.Edge.E]
  have hlo : withBoxes.Lo.val = RH66388Count.enclosure.L2.val := rfl
  have hhi : withBoxes.Hi.val = RH66388Count.enclosure.H2.val := rfl
  have h := H11K.edge_sound_of_split withBoxes edge_rest_checked hp
  simpa only [ht, hlo, hhi] using h

end RH66388Edge
#print axioms RH66388Edge.upper_edge_of_pieces


