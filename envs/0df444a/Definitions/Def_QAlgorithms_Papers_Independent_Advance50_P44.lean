-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44
-- name    : QAlgorithms_Papers_Independent_Advance50_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:14:57.985995+00:00
-- url     : https://prove2.me/theorems/b80a2b09-71ac-4576-bdbb-bf10bb479fba
-- title:
--   Definitions for End-to-end capacities of a quantum communication network
-- statement:
--   The objects the formalized statements of *End-to-end capacities of a quantum communication network* (arXiv:1905.12674) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `equalSpacingLossExpression`: PDF p.19, Eq.(113): the explicit equal-spacing lossy-chain rate expression, in bits per chain use, for N repeaters and total transmissivity eta. Only 0 < eta < 1 is used in the asymptotic statements. This expression does not replace the independently defined operational capacity.
--   - `multibandLossExpression`: PDF p.20, Eq.(122): the explicit multiband lossy-chain expression in bits. The N+1 link labels are retained inside the minimum: M_i and eta_i belong to the same link. The range is finite and nonempty, so real sInf is an attained minimum for every argument, including off-domain real transmissivities. Physical parameters and positive band counts are required in the theorem.
-- source:
--   End-to-end capacities of a quantum communication network, arXiv:1905.12674v1, https://arxiv.org/abs/1905.12674v1

import Mathlib

/-!
Pirandola, arXiv:1905.12674v1, PDF pp.19–20.

This module states the analytic asymptotics of the explicit expressions in
Eqs.(113) and (122). These functions are expressions, not definitions of an
operational capacity. The separate operational identification theorems are
deferred in HARD.md: their adaptive LOCC and bosonic interfaces are missing.
Proposition 8 is reused from the pinned Support50.P47 module in items.json.
Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Advance50.P44

noncomputable section

open Filter

/-- PDF p.19, Eq.(113): the explicit equal-spacing lossy-chain rate expression,
in bits per chain use, for N repeaters and total transmissivity eta.
Only 0 < eta < 1 is used in the asymptotic statements. This expression does
not replace the independently defined operational capacity. -/
def equalSpacingLossExpression (eta : ℝ) (N : ℕ) : ℝ :=
  -Real.logb 2 (1 - eta ^ (1 / ((N : ℝ) + 1)))

/-- With no repeater, the expression reduces to the single-link logarithm. -/
example (eta : ℝ) :
    equalSpacingLossExpression eta 0 = -Real.logb 2 (1 - eta) := by
  simp [equalSpacingLossExpression]

/-- PDF p.20, Eq.(122): the explicit multiband lossy-chain expression in bits.
The N+1 link labels are retained inside the minimum: M_i and eta_i belong to
the same link. The range is finite and nonempty, so real sInf is an attained
minimum for every argument, including off-domain real transmissivities.
Physical parameters and positive band counts are required in the theorem. -/
def multibandLossExpression (N : ℕ) (M : Fin (N + 1) → ℕ)
    (eta : Fin (N + 1) → ℝ) : ℝ :=
  sInf (Set.range (fun i : Fin (N + 1) =>
    -(M i : ℝ) * Real.logb 2 (1 - eta i)))

/-- Equal single-band links have the single-link expression, for any N. -/
example (N : ℕ) (eta : ℝ) :
    multibandLossExpression N (fun _ => 1) (fun _ => eta) =
      -Real.logb 2 (1 - eta) := by
  simp [multibandLossExpression]

end

end QAlgorithms.Papers.Independent.Advance50.P44


