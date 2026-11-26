-- Prove2me | Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
-- name    : FirstPassageLinearTransport_MovingEndpointParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:27.840201+00:00
-- url     : https://prove2.me/theorems/fbdf3953-fbcb-5146-bdd0-9cc18af5136b
-- title:
--   Moving Endpoint Parameters
-- statement:
--   Definitions and structural lemmas for Moving Endpoint Parameters, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointParameters.lean

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
structure MovingEndpointParameterPackage (Amax c beta : ℝ) where
  run : ShrinkingBarrierRunData
  Cswitch : ℝ
  epsilon : ℝ
  K₀ : ℝ
  K₁ : ℝ
  Amax_pos : 0 < Amax
  Cswitch_pos : 0 < Cswitch
  terminal_below_switch : Amax / Real.log 2 < Cswitch
  high_cap : run.D / Real.sqrt Cswitch ≤ run.tau
  high_rate_margin : epsilon <
    min (Cswitch * Real.log 2) (maximalBarrierC0 * run.D ^ 2) - 5 / 2
  clock_pressure : 1 / driftGap < c * Real.log 2
  high_height_contraction :
    (run.rHi : ℝ) * (1 + run.tau) < 1
  tau_lt_beta : run.tau < beta
  epsilon_pos : 0 < epsilon
  K₀_gt_six : 6 < K₀
  K₁_pos : 0 < K₁
  K₁_reserve : 8 ≤ K₁ * driftGap
end
end FirstPassageLinearTransport


