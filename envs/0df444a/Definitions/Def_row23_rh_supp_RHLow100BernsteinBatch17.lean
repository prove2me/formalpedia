-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch17
-- name    : row23_rh_supp_RHLow100BernsteinBatch17
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:45:06.918165+00:00
-- url     : https://prove2.me/theorems/20b691ea-0c33-408e-a36d-0e70826029ac
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch17
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
theorem row68box0 : CertifiedStreamingLocalBoxes.valid ⟨68, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨68, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row69box0 : CertifiedStreamingLocalBoxes.valid ⟨69, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨69, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row70box0 : CertifiedStreamingLocalBoxes.valid ⟨70, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨70, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row71box0 : CertifiedStreamingLocalBoxes.valid ⟨71, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨71, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row68box0
#print axioms RHLow100Bernstein.row69box0
#print axioms RHLow100Bernstein.row70box0
#print axioms RHLow100Bernstein.row71box0


