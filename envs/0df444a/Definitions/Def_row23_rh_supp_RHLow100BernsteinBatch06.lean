-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinBatch06
-- name    : row23_rh_supp_RHLow100BernsteinBatch06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:53:35.812091+00:00
-- url     : https://prove2.me/theorems/d4958922-ca58-4544-b362-f1cdd4204333
-- title:
--   Row 23 RH support: RHLow100BernsteinBatch06
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
theorem row24box0 : CertifiedStreamingLocalBoxes.valid ⟨24, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨24, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row25box0 : CertifiedStreamingLocalBoxes.valid ⟨25, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨25, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row26box0 : CertifiedStreamingLocalBoxes.valid ⟨26, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨26, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
theorem row27box0 : CertifiedStreamingLocalBoxes.valid ⟨27, by decide⟩ 0
    (CertifiedStreamingLocalBoxes.certificateAt ⟨27, by decide⟩ 0) := by
  unfold CertifiedStreamingLocalBoxes.valid
  decide +kernel
end RHLow100Bernstein
#print axioms RHLow100Bernstein.row24box0
#print axioms RHLow100Bernstein.row25box0
#print axioms RHLow100Bernstein.row26box0
#print axioms RHLow100Bernstein.row27box0


