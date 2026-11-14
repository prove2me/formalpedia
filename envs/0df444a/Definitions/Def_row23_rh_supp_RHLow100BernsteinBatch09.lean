-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch09
-- name    : row23_rh_supp_RHLow100BernsteinBatch09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:07.780126+00:00
-- url     : https://prove2.me/theorems/6e2adb5d-ba13-41d2-b435-cb8c834f6612
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch09
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_TaoFivePrimes_RH14To100BernsteinInterface
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace RHLow100Bernstein
theorem row36box0 : CertifiedStreamingLocalBoxes.valid ⟨36, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨36, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row37box0 : CertifiedStreamingLocalBoxes.valid ⟨37, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨37, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row38box0 : CertifiedStreamingLocalBoxes.valid ⟨38, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨38, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row39box0 : CertifiedStreamingLocalBoxes.valid ⟨39, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨39, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row36box0
#print axioms RHLow100Bernstein.row37box0
#print axioms RHLow100Bernstein.row38box0
#print axioms RHLow100Bernstein.row39box0


