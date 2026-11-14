-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch07
-- name    : row23_rh_supp_RHLow100BernsteinBatch07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:02.506276+00:00
-- url     : https://prove2.me/theorems/eeb0d192-4706-4331-a60c-d464e7a3b497
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch07
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
theorem row28box0 : CertifiedStreamingLocalBoxes.valid ⟨28, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨28, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row29box0 : CertifiedStreamingLocalBoxes.valid ⟨29, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨29, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row30box0 : CertifiedStreamingLocalBoxes.valid ⟨30, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨30, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row31box0 : CertifiedStreamingLocalBoxes.valid ⟨31, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨31, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row28box0
#print axioms RHLow100Bernstein.row29box0
#print axioms RHLow100Bernstein.row30box0
#print axioms RHLow100Bernstein.row31box0


