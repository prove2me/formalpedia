-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04
-- name    : QAlgorithms_Papers_Independent_Bridge50_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:54:02.515692+00:00
-- url     : https://prove2.me/theorems/48c6171e-d4ed-43c0-93f9-a0515d4c0593
-- title:
--   Definitions for Quantum cryptography with an ideal local relay
-- statement:
--   The objects the formalized statements of *Quantum cryptography with an ideal local relay* (arXiv:1509.01113) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `lossNoise`: Loss contribution to equivalent noise, arXiv:1509.01113v1, PDF p.2, paragraph following Eq. (2); physical domain `0 < tau < 1`.
--   - `equivalentNoise`: Equivalent noise including nonnegative excess noise, arXiv:1509.01113v1, PDF p.2, paragraph following Eq. (2).
--   - `analyticRate`: The explicit signed real expression printed as Eq. (1) in arXiv:1509.01113v1, PDF p.2, with `chi = equivalentNoise tau excess`. Its intended parameters are `0 < tau < 1` and `0 ≤ excess`. Ideal reconciliation and large modulation specify the source of this expression; this definition makes no operational identification.
--   - `pureLossRate`: The pure-loss expression in arXiv:1509.01113v1, PDF p.2, Eq. (3), for `0 < tau < 1`. The compact printed denominator `(1 - tau)e` means `(1 - tau) * exp(1)`, as forced by substitution into Eq. (1).
--   - `fiberTransmissivity`: Transmissivity after `distance` km at 0.2 dB/km, as specified in arXiv:1509.01113v1, PDF pp.1–2: `10 ^ (-(0.2 * distance) / 10)`. Distance in the applications is positive.
-- source:
--   Quantum cryptography with an ideal local relay, arXiv:1509.01113v1, https://arxiv.org/abs/1509.01113v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24

/-!
Analytic consequences of arXiv:1509.01113v1, PDF p.2, Eqs. (1)–(3).
The paper-local definitions below describe the printed signed real expression only.
The base-two logarithm and thermal entropy are imported from pinned accepted modules.
For the variance parameter x of Eq. (2), h(x) = bosonicEntropy ((x - 1) / 2).
They do not define an operational secret-key rate or a channel capacity.
The physical interpretation and approximate experimental claims are deferred.
-/

namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)
open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

/-- Loss contribution to equivalent noise, arXiv:1509.01113v1, PDF p.2,
paragraph following Eq. (2); physical domain `0 < tau < 1`. -/
noncomputable def lossNoise (tau : ℝ) : ℝ :=
  2 * (1 + tau) / tau

/-- Equivalent noise including nonnegative excess noise, arXiv:1509.01113v1,
PDF p.2, paragraph following Eq. (2). -/
noncomputable def equivalentNoise (tau excess : ℝ) : ℝ :=
  lossNoise tau + excess

/-- The explicit signed real expression printed as Eq. (1) in
arXiv:1509.01113v1, PDF p.2, with `chi = equivalentNoise tau excess`.
Its intended parameters are `0 < tau < 1` and `0 ≤ excess`.
Ideal reconciliation and large modulation specify the source of this expression;
this definition makes no operational identification. -/
noncomputable def analyticRate (tau excess : ℝ) : ℝ :=
  let chi := equivalentNoise tau excess
  bosonicEntropy (((chi / (1 + tau) - 1) - 1) / 2) -
    bosonicEntropy ((((tau * chi - (1 + tau) ^ 2) / (1 - tau ^ 2)) - 1) / 2) +
    logTwo (2 * (1 + tau) / (Real.exp 1 * (1 - tau) * chi))

/-- The pure-loss expression in arXiv:1509.01113v1, PDF p.2, Eq. (3),
for `0 < tau < 1`. The compact printed denominator `(1 - tau)e` means
`(1 - tau) * exp(1)`, as forced by substitution into Eq. (1). -/
noncomputable def pureLossRate (tau : ℝ) : ℝ :=
  bosonicEntropy ((((2 - tau) / tau) - 1) / 2) +
    logTwo (tau / ((1 - tau) * Real.exp 1))

/-- Transmissivity after `distance` km at 0.2 dB/km, as specified in
arXiv:1509.01113v1, PDF pp.1–2: `10 ^ (-(0.2 * distance) / 10)`.
Distance in the applications is positive. -/
noncomputable def fiberTransmissivity (distance : ℝ) : ℝ :=
  Real.rpow 10 (-(distance / 50))

/-- Sanity check for the base-two logarithm at one. -/
example : logTwo 1 = 0 := by
  simp [logTwo]

/-- The entropy endpoint needed for the paper's zero-excess-noise case. -/
example : bosonicEntropy ((1 - 1) / 2) = 0 := by
  norm_num [bosonicEntropy]

/-- Half transmission has loss noise six, using the paper's normalization. -/
example : lossNoise (1 / 2) = 6 := by
  norm_num [lossNoise]

/-- Zero excess noise retains exactly the loss contribution. -/
example (tau : ℝ) : equivalentNoise tau 0 = lossNoise tau := by
  simp [equivalentNoise]

/-- Zero fibre distance means unit transmission. -/
example : fiberTransmissivity 0 = 1 := by
  simp [fiberTransmissivity]

end QAlgorithms.Papers.Independent.Bridge50.P04


