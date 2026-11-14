-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch00
-- name    : row23_rh_supp_RHLow100ThetaBatch00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:35.764584+00:00
-- url     : https://prove2.me/theorems/790d0332-f550-41fc-9187-a8caa16795b5
-- title:
--   Row 23 RH support: RHLow100ThetaBatch00
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_TaoFivePrimes_RH14To100ThetaInterface
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace RHLow100Theta
theorem row00point0 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row00point1 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row00point2 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨2, by decide⟩) = true := by
  decide +kernel
theorem row00point3 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨3, by decide⟩) = true := by
  decide +kernel
theorem row00point4 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨4, by decide⟩) = true := by
  decide +kernel
theorem row00point5 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨5, by decide⟩) = true := by
  decide +kernel
theorem row00point6 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨6, by decide⟩) = true := by
  decide +kernel
theorem row00point7 (ha : CertifiedThetaPoints.active ⟨0, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨0, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨0, by decide⟩ ⟨7, by decide⟩) = true := by
  decide +kernel
end RHLow100Theta
#print axioms RHLow100Theta.row00point0
#print axioms RHLow100Theta.row00point1
#print axioms RHLow100Theta.row00point2
#print axioms RHLow100Theta.row00point3
#print axioms RHLow100Theta.row00point4
#print axioms RHLow100Theta.row00point5
#print axioms RHLow100Theta.row00point6
#print axioms RHLow100Theta.row00point7


