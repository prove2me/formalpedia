-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch18
-- name    : row23_rh_supp_RHLow100BernsteinBatch18
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:45:32.147076+00:00
-- url     : https://prove2.me/theorems/3f7c81ef-e160-43b7-9e37-135830d95ff2
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch18
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
theorem row72box0 : CertifiedStreamingLocalBoxes.valid ⟨72, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨72, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row73box0 : CertifiedStreamingLocalBoxes.valid ⟨73, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨73, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row73box1 : CertifiedStreamingLocalBoxes.valid ⟨73, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨73, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row74box0 : CertifiedStreamingLocalBoxes.valid ⟨74, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨74, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row75box0 : CertifiedStreamingLocalBoxes.valid ⟨75, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨75, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row72box0
#print axioms RHLow100Bernstein.row73box0
#print axioms RHLow100Bernstein.row73box1
#print axioms RHLow100Bernstein.row74box0
#print axioms RHLow100Bernstein.row75box0


