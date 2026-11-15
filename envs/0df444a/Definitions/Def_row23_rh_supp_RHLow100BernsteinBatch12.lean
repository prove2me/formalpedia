-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch12
-- name    : row23_rh_supp_RHLow100BernsteinBatch12
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:43:17.863165+00:00
-- url     : https://prove2.me/theorems/d32dd539-a152-4774-bac3-c2a79711ec5d
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch12
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
theorem row48box0 : CertifiedStreamingLocalBoxes.valid ⟨48, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨48, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row49box0 : CertifiedStreamingLocalBoxes.valid ⟨49, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨49, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row50box0 : CertifiedStreamingLocalBoxes.valid ⟨50, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨50, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row51box0 : CertifiedStreamingLocalBoxes.valid ⟨51, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨51, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row51box1 : CertifiedStreamingLocalBoxes.valid ⟨51, by decide⟩ 1
    (CertifiedStreamingLocalBoxes.certificateAt ⟨51, by decide⟩ 1) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row48box0
#print axioms RHLow100Bernstein.row49box0
#print axioms RHLow100Bernstein.row50box0
#print axioms RHLow100Bernstein.row51box0
#print axioms RHLow100Bernstein.row51box1


