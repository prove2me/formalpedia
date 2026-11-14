-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch04
-- name    : row23_rh_supp_RHLow100BernsteinBatch04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:09.786501+00:00
-- url     : https://prove2.me/theorems/5f634824-4c64-4d1c-8824-163af0216a2b
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch04
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
theorem row16box0 : CertifiedStreamingLocalBoxes.valid ⟨16, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨16, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row17box0 : CertifiedStreamingLocalBoxes.valid ⟨17, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨17, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row18box0 : CertifiedStreamingLocalBoxes.valid ⟨18, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨18, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row19box0 : CertifiedStreamingLocalBoxes.valid ⟨19, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨19, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row16box0
#print axioms RHLow100Bernstein.row17box0
#print axioms RHLow100Bernstein.row18box0
#print axioms RHLow100Bernstein.row19box0


