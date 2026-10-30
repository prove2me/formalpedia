-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_transfer
-- name    : HRRPIncentives_SchemeI_transfer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:14:28.799134+00:00
-- url     : https://prove2.me/theorems/9ea5f36e-827c-41c3-a418-b81663296257
-- title:
--   HRRP-I transfer payment $T_i$
-- statement:
--   Under HRRP-I (HRRP with the penalty cap removed and bonuses allowed), the regulator pays hospital $i$ (display (9))
--
--   $$T_i=\bar c_i\lambda(1+r_i)-\frac{1}{\bar r_i}(r_i-\bar r_i)(1+r_i)\bar c_i\lambda+\bar R_i,$$
--
--   where $\bar c_i,\bar r_i,\bar R_i$ are the yardsticks of (6). The first term reimburses each of the $(1+r_i)\lambda$ visits at the yardstick cost; the second is a penalty when $r_i>\bar r_i$ and a bonus when $r_i<\bar r_i$, scaled by the multiplier $(1+r_i)/\bar r_i$; the last reimburses the yardstick investment cost.
--
--   **Formalization Note** Whenever the other hospitals' readmission rates lie in $[r_{\min},r_{\max}]$ with $r_{\min}>0$, $\bar r_i>0$, so there is no division by zero.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (9), p. 14 (the transfer (7) of p. 11 with P_cap = ∞ and bonuses allowed)

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_cbar
import Definitions.Def_HRRPIncentives_SchemeI_rbar
import Definitions.Def_HRRPIncentives_SchemeI_investmentBar

namespace HRRPIncentives.SchemeI

/-- The HRRP-I transfer payment (9) to hospital `i`:
`T_i = c̄_i λ (1 + r_i) − (1/r̄_i)(r_i − r̄_i)(1 + r_i) c̄_i λ + R̄_i`,
the HRRP transfer (7) with no penalty cap (`P_cap = ∞`) and bonuses allowed (no positive part).

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (9), p. 14.

**Formalization Note.** The yardsticks are `cbar`, `rbar`, `investmentBar` of (6). Under the
standing assumptions `r̄_i ≥ rmin > 0` for any profile in the box, so the division is never by zero. -/
noncomputable def transfer (lam : ℝ) (R : ℝ × ℝ → ℝ) {N : ℕ} (x : Fin N → ℝ × ℝ)
    (i : Fin N) : ℝ :=
  cbar x i * lam * (1 + (x i).1)
    - (1 / rbar x i) * ((x i).1 - rbar x i) * (1 + (x i).1) * cbar x i * lam
    + investmentBar R x i

end HRRPIncentives.SchemeI


