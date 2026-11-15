-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch11
-- name    : row23_rh_supp_RHLow100BernsteinBatch11
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:42:13.943628+00:00
-- url     : https://prove2.me/theorems/b52a1d65-9b5c-4a9a-82d3-6b0aa08cfd6a
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch11
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
theorem row44box0 : CertifiedStreamingLocalBoxes.valid ⟨44, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨44, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row45box0 : CertifiedStreamingLocalBoxes.valid ⟨45, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨45, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row45box1 : CertifiedStreamingLocalBoxes.valid ⟨45, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨45, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row46box0 : CertifiedStreamingLocalBoxes.valid ⟨46, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨46, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row47box0 : CertifiedStreamingLocalBoxes.valid ⟨47, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨47, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row44box0
#print axioms RHLow100Bernstein.row45box0
#print axioms RHLow100Bernstein.row45box1
#print axioms RHLow100Bernstein.row46box0
#print axioms RHLow100Bernstein.row47box0


