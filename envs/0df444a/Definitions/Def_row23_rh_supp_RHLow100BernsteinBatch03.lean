-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch03
-- name    : row23_rh_supp_RHLow100BernsteinBatch03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:07.944799+00:00
-- url     : https://prove2.me/theorems/3386be41-c160-4e96-a779-464c6d0d02ba
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch03
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
theorem row12box0 : CertifiedStreamingLocalBoxes.valid ⟨12, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨12, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row13box0 : CertifiedStreamingLocalBoxes.valid ⟨13, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨13, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row14box0 : CertifiedStreamingLocalBoxes.valid ⟨14, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨14, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row15box0 : CertifiedStreamingLocalBoxes.valid ⟨15, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨15, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row12box0
#print axioms RHLow100Bernstein.row13box0
#print axioms RHLow100Bernstein.row14box0
#print axioms RHLow100Bernstein.row15box0


