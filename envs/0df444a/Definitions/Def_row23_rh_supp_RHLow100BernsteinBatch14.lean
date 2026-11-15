-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch14
-- name    : row23_rh_supp_RHLow100BernsteinBatch14
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:44:07.737306+00:00
-- url     : https://prove2.me/theorems/5b7c23d3-34cd-43e2-8eb1-c9c4bb0ead51
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch14
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
theorem row56box0 : CertifiedStreamingLocalBoxes.valid ⟨56, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨56, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row57box0 : CertifiedStreamingLocalBoxes.valid ⟨57, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨57, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row58box0 : CertifiedStreamingLocalBoxes.valid ⟨58, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨58, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row59box0 : CertifiedStreamingLocalBoxes.valid ⟨59, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨59, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row56box0
#print axioms RHLow100Bernstein.row57box0
#print axioms RHLow100Bernstein.row58box0
#print axioms RHLow100Bernstein.row59box0


