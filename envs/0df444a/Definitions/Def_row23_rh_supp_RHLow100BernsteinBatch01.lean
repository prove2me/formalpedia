-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch01
-- name    : row23_rh_supp_RHLow100BernsteinBatch01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:30.983356+00:00
-- url     : https://prove2.me/theorems/1f77fb21-6609-4bb2-a0a5-f4afb49ccab5
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch01
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
theorem row04box0 : CertifiedStreamingLocalBoxes.valid ⟨4, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨4, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row05box0 : CertifiedStreamingLocalBoxes.valid ⟨5, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨5, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row06box0 : CertifiedStreamingLocalBoxes.valid ⟨6, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨6, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row07box0 : CertifiedStreamingLocalBoxes.valid ⟨7, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨7, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row04box0
#print axioms RHLow100Bernstein.row05box0
#print axioms RHLow100Bernstein.row06box0
#print axioms RHLow100Bernstein.row07box0


