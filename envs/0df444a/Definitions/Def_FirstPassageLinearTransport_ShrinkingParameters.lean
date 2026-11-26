-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
-- name    : FirstPassageLinearTransport_ShrinkingParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:14:49.644388+00:00
-- url     : https://prove2.me/theorems/c0bd7a1e-48ae-4121-b461-0011cc658f35
-- title:
--   Shrinking Parameters
-- statement:
--   Definitions and structural lemmas for Shrinking Parameters, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingParameters.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingHighDensity
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def timeSupportCriticalExponent : ℝ :=
  fixedPolylogCriticalExponent / 2
structure ShrinkingPolylogParameterPackage (A c beta : ℝ) where
  run : ShrinkingBarrierRunData
  lambdaLo : ℝ
  bLo : ℝ
  cDyadic : ℝ
  Cswitch : ℝ
  kappa : ℝ
  lambdaLo_nonneg : 0 ≤ lambdaLo
  lambdaLo_lt_one : lambdaLo < 1
  bLo_pos : 0 < bLo
  bLo_lt_rate : bLo < adjustableEntropyRate lambdaLo run.etaLo
  cDyadic_pos : 0 < cDyadic
  cDyadic_lt_logTwo : cDyadic < Real.log 2
  Cswitch_pos : 0 < Cswitch
  terminal_below_switch : A / Real.log 2 < Cswitch
  high_cap : run.D / Real.sqrt Cswitch ≤ run.tau
  high_rate_margin : kappa <
    min (Cswitch * Real.log 2) (maximalBarrierC0 * run.D ^ 2) - 5 / 2
  low_rate_margin : kappa <
    A * min bLo cDyadic / Real.log 2 - 1 / 2
  clock_pressure : 1 / (1 - (run.rHi : ℝ)) < c * Real.log 2
  high_height_contraction :
    (run.rHi : ℝ) * (1 + run.tau) < 1
  tau_lt_beta : run.tau < beta
  kappa_pos : 0 < kappa
end
end FirstPassageLinearTransport


