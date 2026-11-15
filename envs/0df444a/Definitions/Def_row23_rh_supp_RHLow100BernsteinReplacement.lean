-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100BernsteinReplacement
-- name    : row23_rh_supp_RHLow100BernsteinReplacement
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:51:42.563197+00:00
-- url     : https://prove2.me/theorems/5cc1fc98-f3c8-415b-92bc-815a459570c9
-- title:
--   Row 23 RH support: RHLow100BernsteinReplacement
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100BernsteinAll
set_option autoImplicit false

theorem TaoFivePrimes.rh14to100_bernstein_checks :
    (∀ (i : Fin 86) (j : ℕ), j < (CertifiedLocalBoxes.rowSpecs i).length →
      CertifiedStreamingLocalBoxes.valid i j (CertifiedStreamingLocalBoxes.certificateAt i j)) ∧
    (∀ i : Fin 86, (CertifiedLocalBoxes.rowSpecs i).length ≤ 2) :=
  RHLow100Bernstein.all_boxes

#print axioms TaoFivePrimes.rh14to100_bernstein_checks


