-- Prove2me | Definitions.Def_TaoFivePrimes_RH100To1000PhaseApproximation
-- name    : TaoFivePrimes_RH100To1000PhaseApproximation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T06:10:07.110508+00:00
-- url     : https://prove2.me/theorems/660954fe-74d4-453d-ac8c-502ccfe36246
-- title:
--   TaoFivePrimes_RH100To1000PhaseApproximation
-- statement:
--   The finite 1024-term exponential series at the scaled imaginary panel argument, raised to the 4096th power. Rational parameters give a rational complex expression. This definition asserts no approximation or RH result.
-- source:
--   Transparent mathematical definitions from the local xi/Taylor method of sometik179 (original c9908072-d99a-4431-aad8-a72c6352619a; ordinary-syntax accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a), with theta/Mellin foundations attributed to Gabewhigham. This definition asserts no analytic accuracy or RH conclusion.

/- Finite arithmetic phase formula for the logarithmic Mellin panel centers.
Original method: sometik179; theta/Mellin foundations: Gabewhigham.
No error assertion is part of this definition. -/
import Definitions.Def_TaoFivePrimes_RH100To1000MellinModel
open Complex Finset
noncomputable def TaoFivePrimes_RH100To1000PhaseApproximation (τ : ℝ) (i : ℕ) : ℂ :=
  (∑ n ∈ range 1024, (Complex.I*(τ:ℂ)*(RH1000Mellin.center i:ℂ)/4096)^n/(n.factorial:ℂ))^4096


