-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePerronTotalSharp
-- name    : row23_rh_supp_RHLegendrePerronTotalSharp
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:24:02.100402+00:00
-- url     : https://prove2.me/theorems/af280e6b-88ca-4d74-91b3-ffa74e6cb6e7
-- title:
--   Row 23 RH support: RHLegendrePerronTotalSharp
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendrePerronSharp
import Definitions.Def_dusart_psi_433_20261014_ZetaZeroConstant
set_option autoImplicit false
namespace DusartLegendreSmoothing
 theorem norm_total_legendre_remainder_sharp (m : ℕ) (hm : 2 ≤ m) (x δ : ℝ)
    (hx : 0 < x) (hd : 0 < δ) (hd1 : δ ≤ 1) :
    ‖-logDeriv riemannZeta 0+legendrePerronRemainder m x δ‖ ≤
      2+(4096/Real.pi+32*(m:ℝ)/δ)*x^(-1/2:ℝ) := by
  calc
    _ ≤ ‖logDeriv riemannZeta 0‖+‖legendrePerronRemainder m x δ‖ := by
      simpa only [norm_neg] using norm_add_le (-logDeriv riemannZeta 0) (legendrePerronRemainder m x δ)
    _ ≤ _ := add_le_add DusartSmoothing.norm_logDeriv_zeta_zero_lt_two.le
      (norm_legendrePerronRemainder_sharp m hm x δ hx hd hd1)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.norm_total_legendre_remainder_sharp


