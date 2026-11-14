-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch03
-- name    : row23_rh_supp_RHLow100ThetaBatch03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:05.321013+00:00
-- url     : https://prove2.me/theorems/4aac82f8-0e03-43e0-a61b-66b5b499083e
-- title:
--   Row 23 RH support: RHLow100ThetaBatch03
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
theorem row03point0 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row03point1 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row03point2 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨2, by decide⟩) = true := by
  decide +kernel
theorem row03point3 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨3, by decide⟩) = true := by
  decide +kernel
theorem row03point4 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨4, by decide⟩) = true := by
  decide +kernel
theorem row03point5 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨5, by decide⟩) = true := by
  decide +kernel
theorem row03point6 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨6, by decide⟩) = true := by
  decide +kernel
theorem row03point7 (ha : CertifiedThetaPoints.active ⟨3, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨3, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨3, by decide⟩ ⟨7, by decide⟩) = true := by
  decide +kernel
end RHLow100Theta
#print axioms RHLow100Theta.row03point0
#print axioms RHLow100Theta.row03point1
#print axioms RHLow100Theta.row03point2
#print axioms RHLow100Theta.row03point3
#print axioms RHLow100Theta.row03point4
#print axioms RHLow100Theta.row03point5
#print axioms RHLow100Theta.row03point6
#print axioms RHLow100Theta.row03point7


