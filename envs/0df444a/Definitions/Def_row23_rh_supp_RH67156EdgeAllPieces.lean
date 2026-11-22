-- Prove2me | Definitions.Def_row23_rh_supp_RH67156EdgeAllPieces
-- name    : row23_rh_supp_RH67156EdgeAllPieces
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T21:57:52.980577+00:00
-- url     : https://prove2.me/theorems/55adb305-b3c7-4b64-982d-c61831a70241
-- title:
--   Row 23 RH support: RH67156EdgeAllPieces
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece00
import Definitions.Def_row23_rh_supp_RH67156EdgePiece01
import Definitions.Def_row23_rh_supp_RH67156EdgePiece02
import Definitions.Def_row23_rh_supp_RH67156EdgePiece03
import Definitions.Def_row23_rh_supp_RH67156EdgePiece04
import Definitions.Def_row23_rh_supp_RH67156EdgePiece05
import Definitions.Def_row23_rh_supp_RH67156EdgePiece06
import Definitions.Def_row23_rh_supp_RH67156EdgePiece07
import Definitions.Def_row23_rh_supp_RH67156EdgePiece08
import Definitions.Def_row23_rh_supp_RH67156EdgePiece09
import Definitions.Def_row23_rh_supp_RH67156EdgePiece10
import Definitions.Def_row23_rh_supp_RH67156EdgePiece11
import Definitions.Def_row23_rh_supp_RH67156EdgePiece12
import Definitions.Def_row23_rh_supp_RH67156EdgePiece13
import Definitions.Def_row23_rh_supp_RH67156EdgePiece14
import Definitions.Def_row23_rh_supp_RH67156EdgePiece15
import Definitions.Def_row23_rh_supp_RH67156EdgePiece16
import Definitions.Def_row23_rh_supp_RH67156EdgePiece17
import Definitions.Def_row23_rh_supp_RH67156EdgePiece18
import Definitions.Def_row23_rh_supp_RH67156EdgePiece19
import Definitions.Def_row23_rh_supp_RH67156EdgePiece20
import Definitions.Def_row23_rh_supp_RH67156EdgePiece21
import Definitions.Def_row23_rh_supp_RH67156EdgePiece22
import Definitions.Def_row23_rh_supp_RH67156EdgePiece23
import Definitions.Def_row23_rh_supp_RH67156EdgePiece24
import Definitions.Def_row23_rh_supp_RH67156EdgePiece25
import Definitions.Def_row23_rh_supp_RH67156EdgePiece26
import Definitions.Def_row23_rh_supp_RH67156EdgePiece27
import Definitions.Def_row23_rh_supp_RH67156EdgePiece28
import Definitions.Def_row23_rh_supp_RH67156EdgePiece29
import Definitions.Def_row23_rh_supp_RH67156EdgePiece30
import Definitions.Def_row23_rh_supp_RH67156EdgePiece31
import Definitions.Def_row23_rh_supp_RH67156EdgePiece32
import Definitions.Def_row23_rh_supp_RH67156EdgePiece33
import Definitions.Def_row23_rh_supp_RH67156EdgePiece34
import Definitions.Def_row23_rh_supp_RH67156EdgePiece35
import Definitions.Def_row23_rh_supp_RH67156EdgePiece36
import Definitions.Def_row23_rh_supp_RH67156EdgePiece37
import Definitions.Def_row23_rh_supp_RH67156EdgePiece38
import Definitions.Def_row23_rh_supp_RH67156EdgePiece39
import Definitions.Def_row23_rh_supp_RH67156EdgePiece40
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH67156Edge

theorem all_pieces_checked (j : Nat) (hj : j < withBoxes.m) :
    H11K.pieceJ withBoxes j = true := by
  have hm : withBoxes.m = 41 := rfl
  rw [hm] at hj
  apply pieceJ_of_checked j hj
  interval_cases j
  · exact piece00_checked
  · exact piece01_checked
  · exact piece02_checked
  · exact piece03_checked
  · exact piece04_checked
  · exact piece05_checked
  · exact piece06_checked
  · exact piece07_checked
  · exact piece08_checked
  · exact piece09_checked
  · exact piece10_checked
  · exact piece11_checked
  · exact piece12_checked
  · exact piece13_checked
  · exact piece14_checked
  · exact piece15_checked
  · exact piece16_checked
  · exact piece17_checked
  · exact piece18_checked
  · exact piece19_checked
  · exact piece20_checked
  · exact piece21_checked
  · exact piece22_checked
  · exact piece23_checked
  · exact piece24_checked
  · exact piece25_checked
  · exact piece26_checked
  · exact piece27_checked
  · exact piece28_checked
  · exact piece29_checked
  · exact piece30_checked
  · exact piece31_checked
  · exact piece32_checked
  · exact piece33_checked
  · exact piece34_checked
  · exact piece35_checked
  · exact piece36_checked
  · exact piece37_checked
  · exact piece38_checked
  · exact piece39_checked
  · exact piece40_checked
end RH67156Edge
#print axioms RH67156Edge.all_pieces_checked


