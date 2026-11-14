-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaBatch05
-- name    : row23_rh_supp_RHLow100ThetaBatch05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:51:09.031335+00:00
-- url     : https://prove2.me/theorems/11367dcb-1811-420c-937b-aa448bde2668
-- title:
--   Row 23 RH support: RHLow100ThetaBatch05
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
theorem row05point0 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨0, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨0, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨0, by decide⟩) = true := by
  decide +kernel
theorem row05point1 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨1, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨1, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨1, by decide⟩) = true := by
  decide +kernel
theorem row05point2 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨2, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨2, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨2, by decide⟩) = true := by
  decide +kernel
theorem row05point3 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨3, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨3, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨3, by decide⟩) = true := by
  decide +kernel
theorem row05point4 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨4, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨4, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨4, by decide⟩) = true := by
  decide +kernel
theorem row05point5 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨5, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨5, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨5, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨5, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row05point6 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨6, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨6, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨6, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨6, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
theorem row05point7 (ha : CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨7, by decide⟩) :
    CertifiedJetRecords.checkRecord ⟨5, by decide⟩ ⟨7, by decide⟩
      (CertifiedJetRecords.recordAt ⟨5, by decide⟩ ⟨7, by decide⟩) = true := by
  have hn : ¬ CertifiedThetaPoints.active ⟨5, by decide⟩ ⟨7, by decide⟩ := by
    unfold CertifiedThetaPoints.active
    decide +kernel
  exact False.elim (hn ha)
end RHLow100Theta
#print axioms RHLow100Theta.row05point0
#print axioms RHLow100Theta.row05point1
#print axioms RHLow100Theta.row05point2
#print axioms RHLow100Theta.row05point3
#print axioms RHLow100Theta.row05point4
#print axioms RHLow100Theta.row05point5
#print axioms RHLow100Theta.row05point6
#print axioms RHLow100Theta.row05point7


