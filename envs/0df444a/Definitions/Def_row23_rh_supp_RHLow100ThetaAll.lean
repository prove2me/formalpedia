-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaAll
-- name    : row23_rh_supp_RHLow100ThetaAll
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:18.972042+00:00
-- url     : https://prove2.me/theorems/7d187ad5-232a-46c2-ae4b-202f2a46e07b
-- title:
--   Row 23 RH support: RHLow100ThetaAll
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Tactic.FinCases
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch00
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch01
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch02
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch03
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch04
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch05
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch06
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch07
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch08
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch09
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch10
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch11
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch12
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch13
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch14
import Definitions.Def_row23_rh_supp_RHLow100ThetaBatch15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RHLow100Theta
theorem all_records (i : Fin 16) (n : Fin 8) (ha : CertifiedThetaPoints.active i n) :
    CertifiedJetRecords.checkRecord i n (CertifiedJetRecords.recordAt i n) = true := by
  fin_cases i <;> fin_cases n
  · exact row00point0 ha
  · exact row00point1 ha
  · exact row00point2 ha
  · exact row00point3 ha
  · exact row00point4 ha
  · exact row00point5 ha
  · exact row00point6 ha
  · exact row00point7 ha
  · exact row01point0 ha
  · exact row01point1 ha
  · exact row01point2 ha
  · exact row01point3 ha
  · exact row01point4 ha
  · exact row01point5 ha
  · exact row01point6 ha
  · exact row01point7 ha
  · exact row02point0 ha
  · exact row02point1 ha
  · exact row02point2 ha
  · exact row02point3 ha
  · exact row02point4 ha
  · exact row02point5 ha
  · exact row02point6 ha
  · exact row02point7 ha
  · exact row03point0 ha
  · exact row03point1 ha
  · exact row03point2 ha
  · exact row03point3 ha
  · exact row03point4 ha
  · exact row03point5 ha
  · exact row03point6 ha
  · exact row03point7 ha
  · exact row04point0 ha
  · exact row04point1 ha
  · exact row04point2 ha
  · exact row04point3 ha
  · exact row04point4 ha
  · exact row04point5 ha
  · exact row04point6 ha
  · exact row04point7 ha
  · exact row05point0 ha
  · exact row05point1 ha
  · exact row05point2 ha
  · exact row05point3 ha
  · exact row05point4 ha
  · exact row05point5 ha
  · exact row05point6 ha
  · exact row05point7 ha
  · exact row06point0 ha
  · exact row06point1 ha
  · exact row06point2 ha
  · exact row06point3 ha
  · exact row06point4 ha
  · exact row06point5 ha
  · exact row06point6 ha
  · exact row06point7 ha
  · exact row07point0 ha
  · exact row07point1 ha
  · exact row07point2 ha
  · exact row07point3 ha
  · exact row07point4 ha
  · exact row07point5 ha
  · exact row07point6 ha
  · exact row07point7 ha
  · exact row08point0 ha
  · exact row08point1 ha
  · exact row08point2 ha
  · exact row08point3 ha
  · exact row08point4 ha
  · exact row08point5 ha
  · exact row08point6 ha
  · exact row08point7 ha
  · exact row09point0 ha
  · exact row09point1 ha
  · exact row09point2 ha
  · exact row09point3 ha
  · exact row09point4 ha
  · exact row09point5 ha
  · exact row09point6 ha
  · exact row09point7 ha
  · exact row10point0 ha
  · exact row10point1 ha
  · exact row10point2 ha
  · exact row10point3 ha
  · exact row10point4 ha
  · exact row10point5 ha
  · exact row10point6 ha
  · exact row10point7 ha
  · exact row11point0 ha
  · exact row11point1 ha
  · exact row11point2 ha
  · exact row11point3 ha
  · exact row11point4 ha
  · exact row11point5 ha
  · exact row11point6 ha
  · exact row11point7 ha
  · exact row12point0 ha
  · exact row12point1 ha
  · exact row12point2 ha
  · exact row12point3 ha
  · exact row12point4 ha
  · exact row12point5 ha
  · exact row12point6 ha
  · exact row12point7 ha
  · exact row13point0 ha
  · exact row13point1 ha
  · exact row13point2 ha
  · exact row13point3 ha
  · exact row13point4 ha
  · exact row13point5 ha
  · exact row13point6 ha
  · exact row13point7 ha
  · exact row14point0 ha
  · exact row14point1 ha
  · exact row14point2 ha
  · exact row14point3 ha
  · exact row14point4 ha
  · exact row14point5 ha
  · exact row14point6 ha
  · exact row14point7 ha
  · exact row15point0 ha
  · exact row15point1 ha
  · exact row15point2 ha
  · exact row15point3 ha
  · exact row15point4 ha
  · exact row15point5 ha
  · exact row15point6 ha
  · exact row15point7 ha
end RHLow100Theta
#print axioms RHLow100Theta.all_records


