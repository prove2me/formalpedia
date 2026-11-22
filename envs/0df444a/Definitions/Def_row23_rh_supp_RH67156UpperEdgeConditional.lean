-- Prove2me | Definitions.Def_row23_rh_supp_RH67156UpperEdgeConditional
-- name    : row23_rh_supp_RH67156UpperEdgeConditional
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:55:42.567198+00:00
-- url     : https://prove2.me/theorems/dd889801-b06b-4812-88ff-ae01a4e368ef
-- title:
--   Row 23 RH support: RH67156UpperEdgeConditional
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeRest
import Definitions.Def_row23_rh_supp_RH67156CountScalar
import Theorems.Thm_H11K_edge_sound_of_split
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156Edge

/-- The top argument enclosure follows from the explicitly supplied piece checks. -/
theorem upper_edge_of_pieces
    (hp : ∀ j, j < withBoxes.m → H11K.pieceJ withBoxes j = true) :
    DiffractionCore.argChangeHoriz riemannZeta (67156 : ℝ) 2 (-1) ∈
      Set.Icc RH67156Count.enclosure.L2.val RH67156Count.enclosure.H2.val := by
  have ht : withBoxes.T = (67156 : ℝ) := by
    norm_num [Arb4.EdgeD.T, withBoxes, proposed, RH65004Edge.tight, RH65004Edge.proposed, H65K.Edge.E]
  have hlo : withBoxes.Lo.val = RH67156Count.enclosure.L2.val := rfl
  have hhi : withBoxes.Hi.val = RH67156Count.enclosure.H2.val := rfl
  have h := H11K.edge_sound_of_split withBoxes edge_rest_checked hp
  simpa only [ht, hlo, hhi] using h

end RH67156Edge
#print axioms RH67156Edge.upper_edge_of_pieces


