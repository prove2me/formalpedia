-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourUnit
-- name    : TaoFivePrimes_RHHighContourUnit
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T04:30:26.847002+00:00
-- url     : https://prove2.me/theorems/f9d082cd-7511-4c0b-ad20-5937c72dd789
-- title:
--   Dyadic eighth-root unit data for Fourier contour evaluation
-- statement:
--   Transparent128-bit rational unit-table data, with an ordinary kernel proof that twice the proposed square-root-half numerator lies in the appropriate integer square interval. Analytic unit-table accuracy is proved separately. No sign, count or RH assertion is made.
-- source:
--   Elementary eighth roots of unity used in the Platt Fourier evaluation. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham; Platt DOI10.1090/mcom/3198.

import Mathlib
set_option autoImplicit false
namespace RHHighContourUnit
noncomputable def D : Nat := 2^128
noncomputable def H : Nat := 240615969168004511545033772477625056927
theorem root_checked : (2*H)^2≤2*D^2 ∧ 2*D^2≤(2*(H+1))^2 := by decide +kernel
noncomputable def pair (j : Nat) : Int×Int := match j%8 with
  | 0 => (D,0)
  | 1 => (H,H)
  | 2 => (0,D)
  | 3 => (-(H:Int),H)
  | 4 => (-(D:Int),0)
  | 5 => (-(H:Int),-(H:Int))
  | 6 => (0,-(D:Int))
  | _ => (H,-(H:Int))
end RHHighContourUnit
noncomputable def TaoFivePrimes_RHHighContourUnit : Nat := 8


