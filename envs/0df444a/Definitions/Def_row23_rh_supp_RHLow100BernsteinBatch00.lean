-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch00
-- name    : row23_rh_supp_RHLow100BernsteinBatch00
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:05.060377+00:00
-- url     : https://prove2.me/theorems/90901308-e5e0-45c8-8c80-4915f5ddb3c5
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch00
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
theorem row00box0 : CertifiedStreamingLocalBoxes.valid ⟨0, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨0, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row01box0 : CertifiedStreamingLocalBoxes.valid ⟨1, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨1, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row02box0 : CertifiedStreamingLocalBoxes.valid ⟨2, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨2, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row03box0 : CertifiedStreamingLocalBoxes.valid ⟨3, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨3, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row00box0
#print axioms RHLow100Bernstein.row01box0
#print axioms RHLow100Bernstein.row02box0
#print axioms RHLow100Bernstein.row03box0


