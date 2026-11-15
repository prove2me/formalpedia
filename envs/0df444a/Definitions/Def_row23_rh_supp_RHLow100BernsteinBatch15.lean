-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch15
-- name    : row23_rh_supp_RHLow100BernsteinBatch15
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:44:23.615625+00:00
-- url     : https://prove2.me/theorems/6283f177-c307-4fb6-a50c-3557de835ffc
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch15
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
theorem row60box0 : CertifiedStreamingLocalBoxes.valid ⟨60, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨60, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row61box0 : CertifiedStreamingLocalBoxes.valid ⟨61, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨61, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row62box0 : CertifiedStreamingLocalBoxes.valid ⟨62, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨62, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row63box0 : CertifiedStreamingLocalBoxes.valid ⟨63, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨63, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row63box1 : CertifiedStreamingLocalBoxes.valid ⟨63, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨63, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row60box0
#print axioms RHLow100Bernstein.row61box0
#print axioms RHLow100Bernstein.row62box0
#print axioms RHLow100Bernstein.row63box0
#print axioms RHLow100Bernstein.row63box1


