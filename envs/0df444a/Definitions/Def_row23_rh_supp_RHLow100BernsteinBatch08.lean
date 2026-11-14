-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch08
-- name    : row23_rh_supp_RHLow100BernsteinBatch08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:39.525784+00:00
-- url     : https://prove2.me/theorems/5df77a26-c3d6-457d-98d5-927a86a55d55
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch08
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
theorem row32box0 : CertifiedStreamingLocalBoxes.valid ⟨32, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨32, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row33box0 : CertifiedStreamingLocalBoxes.valid ⟨33, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨33, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row34box0 : CertifiedStreamingLocalBoxes.valid ⟨34, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨34, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row34box1 : CertifiedStreamingLocalBoxes.valid ⟨34, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨34, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row35box0 : CertifiedStreamingLocalBoxes.valid ⟨35, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨35, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row32box0
#print axioms RHLow100Bernstein.row33box0
#print axioms RHLow100Bernstein.row34box0
#print axioms RHLow100Bernstein.row34box1
#print axioms RHLow100Bernstein.row35box0


