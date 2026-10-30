-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P24
-- name    : QAlgorithms_Papers_Independent_Bridge50_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:33:59.667604+00:00
-- url     : https://prove2.me/theorems/1fe601eb-0b0f-40ee-99d5-1775b715e071
-- title:
--   Definitions for Fundamental rate-loss tradeoff for the quantum internet
-- statement:
--   The objects the formalized statements of *Fundamental rate-loss tradeoff for the quantum internet* (arXiv:1601.02933) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pulseRateEnvelope`: arXiv:1601.02933v1, PDF p.4, paragraph after Eq.(4): the displayed vanishing-error upper-bound curve for a chain with n intermediate nodes. One pulse has two polarization modes. This scalar curve is distinct from operational capacity or achievable yield. Its physical domain is 0 < eta < 1; the value at eta = 0 is its continuous extension, used in the sanity test.
-- source:
--   Fundamental rate-loss tradeoff for the quantum internet, arXiv:1601.02933v1, https://arxiv.org/abs/1601.02933v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14

/-!
arXiv:1601.02933v1, Fundamental rate-loss tradeoff for the quantum internet.
Only the scalar high-loss envelope is stated here. The operational network,
private-state, and repeater nodes are individually deferred in HARD.md:
finite-dimensional channels or arbitrary numerical budgets do not model them.
The accepted Gap20.P14 module supplies the exact one-mode bit-valued curve;
it is an approved frozen library module, not a sibling draft.
Compilation and independent moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P24

open Filter
open QAlgorithms.Papers.Independent.Gap20.P14 (rateLossCurve)

/-- arXiv:1601.02933v1, PDF p.4, paragraph after Eq.(4): the displayed
vanishing-error upper-bound curve for a chain with n intermediate nodes.
One pulse has two polarization modes. This scalar curve is distinct from
operational capacity or achievable yield. Its physical domain is 0 < eta < 1;
the value at eta = 0 is its continuous extension, used in the sanity test. -/
def pulseRateEnvelope (n : ℕ) (eta : ℝ) : ℝ :=
  (2 / ((n : ℝ) + 1)) * rateLossCurve eta

/-- Sanity: complete loss gives the continuous endpoint value zero. -/
example (n : ℕ) : pulseRateEnvelope n 0 = 0 := by
  simp [pulseRateEnvelope, rateLossCurve]

/-- Sanity: n = 0 retains both polarization modes of the single link. -/
example (eta : ℝ) : pulseRateEnvelope 0 eta = 2 * rateLossCurve eta := by
  simp [pulseRateEnvelope]

end QAlgorithms.Papers.Independent.Bridge50.P24


