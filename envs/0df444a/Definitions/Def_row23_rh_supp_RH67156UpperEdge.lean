-- Prove2me | Definitions.Def_row23_rh_supp_RH67156UpperEdge
-- name    : row23_rh_supp_RH67156UpperEdge
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:45:28.399916+00:00
-- url     : https://prove2.me/theorems/4803671d-fcfe-4b24-91be-78960eb36a0f
-- title:
--   Row 23 RH support: RH67156UpperEdge
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156UpperEdgeConditional
import Theorems.Thm_TaoFivePrimes_rh67156_all_edge_pieces_cut_20261122
set_option autoImplicit false
noncomputable section
namespace RH67156Edge

/-- Kernel-checked horizontal argument enclosure at height 67156. -/
theorem upper_edge :
    DiffractionCore.argChangeHoriz riemannZeta (67156 : ℝ) 2 (-1) ∈
      Set.Icc RH67156Count.enclosure.L2.val RH67156Count.enclosure.H2.val :=
  upper_edge_of_pieces TaoFivePrimes.rh67156_all_edge_pieces_cut_20261122

end RH67156Edge
#print axioms RH67156Edge.upper_edge


