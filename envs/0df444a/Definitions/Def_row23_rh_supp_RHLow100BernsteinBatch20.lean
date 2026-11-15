-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch20
-- name    : row23_rh_supp_RHLow100BernsteinBatch20
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:46:12.007757+00:00
-- url     : https://prove2.me/theorems/a3936343-658b-44d9-a4a8-d35b1ca46da0
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch20
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
theorem row80box0 : CertifiedStreamingLocalBoxes.valid ⟨80, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨80, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row81box0 : CertifiedStreamingLocalBoxes.valid ⟨81, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨81, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row81box1 : CertifiedStreamingLocalBoxes.valid ⟨81, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨81, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row82box0 : CertifiedStreamingLocalBoxes.valid ⟨82, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨82, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row83box0 : CertifiedStreamingLocalBoxes.valid ⟨83, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨83, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row80box0
#print axioms RHLow100Bernstein.row81box0
#print axioms RHLow100Bernstein.row81box1
#print axioms RHLow100Bernstein.row82box0
#print axioms RHLow100Bernstein.row83box0


