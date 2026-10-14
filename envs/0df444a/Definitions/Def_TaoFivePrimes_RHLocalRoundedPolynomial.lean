-- Prove2me | Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
-- name    : TaoFivePrimes_RHLocalRoundedPolynomial
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T04:38:19.011526+00:00
-- url     : https://prove2.me/theorems/1b72ec2a-d3d7-43da-a116-e90c3a57911d
-- title:
--   Rounded local xi polynomial model
-- statement:
--   The ordinary finite local polynomial with coefficients from an integer list divided by 10^8, in the rotated variable -i*(s-(1/2+iT)). The term count and height are parameters. This transparent mathematical function asserts no accuracy or RH conclusion.
-- source:
--   Transparent mathematical definitions from the local xi/Taylor method of sometik179 (original c9908072-d99a-4431-aad8-a72c6352619a; ordinary-syntax accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a), with theta/Mellin foundations attributed to Gabewhigham. This definition asserts no analytic accuracy or RH conclusion.

/- Transparent local polynomial model for certified zeta-height slices.
Original xi/Taylor method: sometik179; theta/Mellin foundations: Gabewhigham.
This mathematical function asserts no coefficient accuracy or RH theorem. -/
import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
open Complex Finset
noncomputable def TaoFivePrimes_RHLocalRoundedPolynomial
    (v : List ℤ) (N : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)*
    (-Complex.I*(s-RH1000Analytic.CertifiedLocalXi.center T))^n


