-- Prove2me | Definitions.Def_TaoFivePrimes_RH100To1000NegativeExpApproximation
-- name    : TaoFivePrimes_RH100To1000NegativeExpApproximation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T06:12:53.421196+00:00
-- url     : https://prove2.me/theorems/6060ced5-db4e-4fee-9022-33d22b25d227
-- title:
--   TaoFivePrimes_RH100To1000NegativeExpApproximation
-- statement:
--   The finite rational decreasing exponential candidate: a 1024-term series at -x/4096 raised to the 4096th power, or zero for x>4096. The definition alone asserts no accuracy or RH.
-- source:
--   Transparent mathematical definitions from the local xi/Taylor method of sometik179 (original c9908072-d99a-4431-aad8-a72c6352619a; ordinary-syntax accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a), with theta/Mellin foundations attributed to Gabewhigham. This definition asserts no analytic accuracy or RH conclusion.

/- Finite rational formula for the decreasing real exponential.
Original method: sometik179; theta/Mellin foundations: Gabewhigham.
This definition supplies no accuracy assertion. -/
import Mathlib
open Finset
noncomputable def TaoFivePrimes_RH100To1000NegativeExpApproximation (x : ℝ) : ℝ :=
  if x ≤ 4096 then (∑ n ∈ range 1024, (-x/4096)^n/(n.factorial:ℝ))^4096 else 0


