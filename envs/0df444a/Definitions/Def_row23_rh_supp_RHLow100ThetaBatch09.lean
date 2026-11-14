-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch09
-- name    : row23_rh_supp_RHLow100ThetaBatch09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:23.81614+00:00
-- url     : https://prove2.me/theorems/c1c25e3c-cc3f-4a8a-be77-37656a0da983
-- title:
--   Row 23 RH support: RHLow100ThetaBatch09
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
theorem row09point0 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row09point1 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row09point2 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨2, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨2, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row09point3 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨3, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨3, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row09point4 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨4, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨4, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row09point5 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨5, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨5, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row09point6 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨6, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨6, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row09point7 (ha : CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨9, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨9, by decide⟩ ⟨7, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨9, by decide⟩ ⟨7, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
end RHLow100Theta
#print axioms RHLow100Theta.row09point0
#print axioms RHLow100Theta.row09point1
#print axioms RHLow100Theta.row09point2
#print axioms RHLow100Theta.row09point3
#print axioms RHLow100Theta.row09point4
#print axioms RHLow100Theta.row09point5
#print axioms RHLow100Theta.row09point6
#print axioms RHLow100Theta.row09point7


