-- Prove2me | Definitions.Def_row23_rh_supp_RH66388UpperEdge
-- name    : row23_rh_supp_RH66388UpperEdge
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:11:54.133238+00:00
-- url     : https://prove2.me/theorems/ce7cea70-5f87-4ff6-b74a-520fd88133ef
-- title:
--   Row 23 RH support: RH66388UpperEdge
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388UpperEdgeConditional
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_00_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_01_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_02_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_03_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_04_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_05_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_06_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_07_20261115
import Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_08_20261115
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace RH66388Edge

theorem upper_edge :
    DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L2.val RH66388Count.enclosure.H2.val := by
  apply upper_edge_of_pieces
  intro j hj
  have hj41 : j < 41 := by simpa only [show withBoxes.m = 41 from rfl] using hj
  by_cases h0 : j < 5
  · exact TaoFivePrimes.rh66388_edge_piece_group_00_20261115 j (by omega) h0
  by_cases h1 : j < 10
  · exact TaoFivePrimes.rh66388_edge_piece_group_01_20261115 j (by omega) h1
  by_cases h2 : j < 15
  · exact TaoFivePrimes.rh66388_edge_piece_group_02_20261115 j (by omega) h2
  by_cases h3 : j < 20
  · exact TaoFivePrimes.rh66388_edge_piece_group_03_20261115 j (by omega) h3
  by_cases h4 : j < 25
  · exact TaoFivePrimes.rh66388_edge_piece_group_04_20261115 j (by omega) h4
  by_cases h5 : j < 30
  · exact TaoFivePrimes.rh66388_edge_piece_group_05_20261115 j (by omega) h5
  by_cases h6 : j < 35
  · exact TaoFivePrimes.rh66388_edge_piece_group_06_20261115 j (by omega) h6
  by_cases h7 : j < 40
  · exact TaoFivePrimes.rh66388_edge_piece_group_07_20261115 j (by omega) h7
  exact TaoFivePrimes.rh66388_edge_piece_group_08_20261115 j (by omega) hj41
end RH66388Edge
#print axioms RH66388Edge.upper_edge


