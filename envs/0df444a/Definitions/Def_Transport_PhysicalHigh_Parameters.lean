-- Prove2me | Definitions.Def_Transport_PhysicalHigh_Parameters
-- name    : Transport_PhysicalHigh_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:26:28.273622+00:00
-- url     : https://prove2.me/theorems/fc06541b-4047-4371-b9f5-c8e3afef6756
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/Parameters.lean

import Definitions.Def_Transport_PhysicalHigh_DistinctSlots
import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
set_option autoImplicit false
namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
structure DetectorScales (t : ℝ) (K : ℕ) (rmin ellMin allowance : ℝ) where
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1 / 1000
  epsilon_gap : ε < rmin * t
  epsilon_allowance : ε ≤ allowance
  e_pos : 0 < e
  e_small : e < 1 / 1000
  e_slot : e ≤ ellMin / 4
  e_allowance : e ≤ allowance
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  eps_allowance : eps ≤ allowance
  sigma_pos : 0 < sigma
  sigma_t : sigma ≤ t / 2
  sigma_slot : sigma ≤ ellMin / 4
  sigma_allowance : sigma ≤ allowance
  detector_budget : 288 * e + 8 * κ + 2 * cost ≤ ε / 2
  phase_budget : 8 * e * t + κ ≤ ε
  central_budget : (159 * ε + t + t + 7 * t) + 2 * t +
    (26 * e + (K + 8) * eps + t + t * TunedCandidate.ell) +
    (t + t + t) + t ≤ 18 * t
  height_choice : ∀ J : ℝ, 0 ≤ J → ∃ τ : ℝ,
    0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧
    4 * τ < (1 / 200 : ℝ) * cost ∧ τ < t ∧
    2 * τ * (1 + J) ≤ t ∧ τ * (2 + 4 * eps) < t
end
end RH.Transport.PhysicalHigh


