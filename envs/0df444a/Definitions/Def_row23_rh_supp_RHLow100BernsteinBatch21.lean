-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch21
-- name    : row23_rh_supp_RHLow100BernsteinBatch21
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:48:56.173186+00:00
-- url     : https://prove2.me/theorems/da7ec6cf-aac9-4e91-be39-de0826f6ed5c
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch21
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
theorem row84box0 : CertifiedStreamingLocalBoxes.valid ⟨84, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨84, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row85box0 : CertifiedStreamingLocalBoxes.valid ⟨85, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨85, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row84box0
#print axioms RHLow100Bernstein.row85box0


