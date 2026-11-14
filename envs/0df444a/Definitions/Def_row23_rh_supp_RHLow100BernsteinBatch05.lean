-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch05
-- name    : row23_rh_supp_RHLow100BernsteinBatch05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:43.020523+00:00
-- url     : https://prove2.me/theorems/85d54fca-3f30-4192-8ab3-0615f2d88c95
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch05
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
theorem row20box0 : CertifiedStreamingLocalBoxes.valid ⟨20, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨20, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row21box0 : CertifiedStreamingLocalBoxes.valid ⟨21, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨21, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row22box0 : CertifiedStreamingLocalBoxes.valid ⟨22, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨22, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row23box0 : CertifiedStreamingLocalBoxes.valid ⟨23, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨23, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row20box0
#print axioms RHLow100Bernstein.row21box0
#print axioms RHLow100Bernstein.row22box0
#print axioms RHLow100Bernstein.row23box0


