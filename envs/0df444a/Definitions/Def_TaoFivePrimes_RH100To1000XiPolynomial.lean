-- Prove2me | Definitions.Def_TaoFivePrimes_RH100To1000XiPolynomial
-- name    : TaoFivePrimes_RH100To1000XiPolynomial
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T05:57:26.59616+00:00
-- url     : https://prove2.me/theorems/f48cf69d-17d1-47c2-83dd-baa20f1808de
-- title:
--   Direct Mellin 272-term local xi polynomial
-- statement:
--   The finite 272-term local polynomial at center 1/2+iT using the exact Mellin-derived xi coefficient proposals. No approximation, rational evaluation or RH conclusion is asserted.
-- source:
--   Transparent mathematical definitions from the local xi/Taylor method of sometik179 (original c9908072-d99a-4431-aad8-a72c6352619a; ordinary-syntax accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a), with theta/Mellin foundations attributed to Gabewhigham. This definition asserts no analytic accuracy or RH conclusion.

/- Finite local xi polynomial from the exact Mellin-derived coefficient rule.
Original method: sometik179; theta/Mellin foundations: Gabewhigham.
This mathematical expression alone asserts no approximation or RH. -/
import Definitions.Def_TaoFivePrimes_RH100To1000XiCoefficient
open Finset
noncomputable def TaoFivePrimes_RH100To1000XiPolynomial (T : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ range 272, TaoFivePrimes_RH100To1000XiCoefficient T n*
    (z-RH1000Analytic.CertifiedLocalXi.center T)^n


