-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch13
-- name    : row23_rh_supp_RHLow100BernsteinBatch13
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:43:42.314695+00:00
-- url     : https://prove2.me/theorems/fd5fe0ef-753e-4ec4-8581-5a078f903735
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch13
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
theorem row52box0 : CertifiedStreamingLocalBoxes.valid ⟨52, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨52, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row53box0 : CertifiedStreamingLocalBoxes.valid ⟨53, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨53, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row53box1 : CertifiedStreamingLocalBoxes.valid ⟨53, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨53, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row54box0 : CertifiedStreamingLocalBoxes.valid ⟨54, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨54, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row55box0 : CertifiedStreamingLocalBoxes.valid ⟨55, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨55, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row52box0
#print axioms RHLow100Bernstein.row53box0
#print axioms RHLow100Bernstein.row53box1
#print axioms RHLow100Bernstein.row54box0
#print axioms RHLow100Bernstein.row55box0


