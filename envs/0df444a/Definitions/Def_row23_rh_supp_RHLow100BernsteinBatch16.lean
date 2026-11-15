-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch16
-- name    : row23_rh_supp_RHLow100BernsteinBatch16
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:44:47.586843+00:00
-- url     : https://prove2.me/theorems/bc2a0372-64be-4b0c-8b90-29ccb4469d10
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch16
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
theorem row64box0 : CertifiedStreamingLocalBoxes.valid ⟨64, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨64, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row65box0 : CertifiedStreamingLocalBoxes.valid ⟨65, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨65, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row66box0 : CertifiedStreamingLocalBoxes.valid ⟨66, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨66, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row67box0 : CertifiedStreamingLocalBoxes.valid ⟨67, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨67, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row64box0
#print axioms RHLow100Bernstein.row65box0
#print axioms RHLow100Bernstein.row66box0
#print axioms RHLow100Bernstein.row67box0


