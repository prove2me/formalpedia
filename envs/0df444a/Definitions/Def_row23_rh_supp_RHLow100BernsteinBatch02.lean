-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch02
-- name    : row23_rh_supp_RHLow100BernsteinBatch02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:04.970791+00:00
-- url     : https://prove2.me/theorems/aaa8dc43-7192-414b-b8fc-3d70fe3086ee
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch02
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
theorem row08box0 : CertifiedStreamingLocalBoxes.valid ⟨8, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨8, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row09box0 : CertifiedStreamingLocalBoxes.valid ⟨9, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨9, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row10box0 : CertifiedStreamingLocalBoxes.valid ⟨10, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨10, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row11box0 : CertifiedStreamingLocalBoxes.valid ⟨11, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨11, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row08box0
#print axioms RHLow100Bernstein.row09box0
#print axioms RHLow100Bernstein.row10box0
#print axioms RHLow100Bernstein.row11box0


