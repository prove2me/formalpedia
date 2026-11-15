-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch19
-- name    : row23_rh_supp_RHLow100BernsteinBatch19
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:45:55.424841+00:00
-- url     : https://prove2.me/theorems/6600d55b-b9ec-4d7a-aba7-db8632b916f1
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch19
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
theorem row76box0 : CertifiedStreamingLocalBoxes.valid ⟨76, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨76, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row77box0 : CertifiedStreamingLocalBoxes.valid ⟨77, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨77, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row78box0 : CertifiedStreamingLocalBoxes.valid ⟨78, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨78, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row79box0 : CertifiedStreamingLocalBoxes.valid ⟨79, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨79, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row76box0
#print axioms RHLow100Bernstein.row77box0
#print axioms RHLow100Bernstein.row78box0
#print axioms RHLow100Bernstein.row79box0


