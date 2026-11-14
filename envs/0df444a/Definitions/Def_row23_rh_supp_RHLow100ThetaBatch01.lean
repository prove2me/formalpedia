-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch01
-- name    : row23_rh_supp_RHLow100ThetaBatch01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:50:54.655361+00:00
-- url     : https://prove2.me/theorems/ca979829-9875-445b-8b20-aa2911d22559
-- title:
--   Row 23 RH support: RHLow100ThetaBatch01
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
theorem row01point0 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row01point1 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row01point2 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨2, by decide⟩) = true := by
  decide +kernel
theorem row01point3 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨3, by decide⟩) = true := by
  decide +kernel
theorem row01point4 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨4, by decide⟩) = true := by
  decide +kernel
theorem row01point5 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨5, by decide⟩) = true := by
  decide +kernel
theorem row01point6 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨6, by decide⟩) = true := by
  decide +kernel
theorem row01point7 (ha : CertifiedThetaPoints.active ⟨1, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨1, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨1, by decide⟩ ⟨7, by decide⟩) = true := by
  decide +kernel
end RHLow100Theta
#print axioms RHLow100Theta.row01point0
#print axioms RHLow100Theta.row01point1
#print axioms RHLow100Theta.row01point2
#print axioms RHLow100Theta.row01point3
#print axioms RHLow100Theta.row01point4
#print axioms RHLow100Theta.row01point5
#print axioms RHLow100Theta.row01point6
#print axioms RHLow100Theta.row01point7


