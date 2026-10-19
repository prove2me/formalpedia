-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24
-- name    : QAlgorithms_Papers_Independent_Frontier30_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:37:45.858016+00:00
-- url     : https://prove2.me/theorems/e5f78a6d-64e4-4a48-a0d9-b35626f7a729
-- title:
--   Definitions for The squashed entanglement of a quantum channel
-- statement:
--   The objects the formalized statements of *The squashed entanglement of a quantum channel* (arXiv:1310.0129) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bosonicEntropy`: PDF p.16, after Eq.(26): thermal entropy g in bits, with 0 log 0 = 0. Only nonnegative arguments are physically used. The total formula on negative arguments has no asserted entropy interpretation.
--   - `pureLossSquashingBound`: PDF p.16, Eq.(26): the scalar test-squashing expression, including its half. The physical domain is 0 <= eta,s <= 1 and finite photonNumber >= 0. This definition makes no assumption about which input or squasher optimizes actual channel squashed entanglement.
--   - `pureLossSymmetricBound`: PDF pp.16,20, Eq.(42): the value of Eq.(26) at symmetric squashing. It remains finite at eta=1 for every finite photonNumber >= 0.
-- source:
--   The squashed entanglement of a quantum channel, arXiv:1310.0129v3, https://arxiv.org/abs/1310.0129v3

import Mathlib

/-!
Scalar optimization results from Takeoka--Guha--Wilde, arXiv:1310.0129v3.
The physical channel, unrestricted squashing and operational capacity results
are explicitly deferred in the assigned unit's HARD.md and GAPS.json.
The functions below are the displayed numerical expressions, not definitions
of a channel capacity or of squashed entanglement.
Compilation is pending the separately requested batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P24

open Filter

/-- PDF p.16, after Eq.(26): thermal entropy g in bits, with 0 log 0 = 0.
Only nonnegative arguments are physically used. The total formula on negative
arguments has no asserted entropy interpretation. -/
def bosonicEntropy (x : ℝ) : ℝ :=
  ((x + 1) * Real.log (x + 1) - x * Real.log x) / Real.log 2

/-- PDF p.16, Eq.(26): the scalar test-squashing expression, including its half.
The physical domain is 0 <= eta,s <= 1 and finite photonNumber >= 0.
This definition makes no assumption about which input or squasher optimizes
actual channel squashed entanglement. -/
def pureLossSquashingBound (eta photonNumber s : ℝ) : ℝ :=
  (bosonicEntropy ((1 - s + eta * s) * photonNumber) +
    bosonicEntropy ((s + eta * (1 - s)) * photonNumber) -
    bosonicEntropy (s * (1 - eta) * photonNumber) -
    bosonicEntropy ((1 - s) * (1 - eta) * photonNumber)) / 2

/-- PDF pp.16,20, Eq.(42): the value of Eq.(26) at symmetric squashing.
It remains finite at eta=1 for every finite photonNumber >= 0. -/
def pureLossSymmetricBound (eta photonNumber : ℝ) : ℝ :=
  bosonicEntropy ((1 + eta) * photonNumber / 2) -
    bosonicEntropy ((1 - eta) * photonNumber / 2)

example : bosonicEntropy 0 = 0 := by
  simp [bosonicEntropy]

example (eta s : ℝ) : pureLossSquashingBound eta 0 s = 0 := by
  simp [pureLossSquashingBound, bosonicEntropy]

example (eta : ℝ) : pureLossSymmetricBound eta 0 = 0 := by
  simp [pureLossSymmetricBound]

example (photonNumber : ℝ) : pureLossSymmetricBound 0 photonNumber = 0 := by
  simp [pureLossSymmetricBound]

end QAlgorithms.Papers.Independent.Frontier30.P24


