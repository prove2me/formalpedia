-- Prove2me | Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
-- name    : FirstPassageLinearTransport_BootstrapSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:10.08875+00:00
-- url     : https://prove2.me/theorems/362f6d56-fa2a-53bc-bc1d-45f3fd1196a4
-- title:
--   Bootstrap Schedule
-- statement:
--   Definitions and structural lemmas for Bootstrap Schedule, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
def bootstrapLogBound {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) (R : ℕ) : ℝ :=
  Real.log (quadraticWindowGlobalConstant eta + 2) +
    (R : ℝ) * Real.log (bootstrapStageK p chi Dc) +
    2 * (R : ℝ) * Real.log Dc⁻¹ +
    2 * (R : ℝ) ^ 2 * Real.log chi⁻¹
def densityGamma (omega chi : ℝ) : ℝ :=
  omega * Real.log (1 / chi)
def bootstrapScheduleA {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc omega : ℝ) : ℝ :=
  Real.log (quadraticWindowGlobalConstant eta + 2) +
    omega * Real.log (bootstrapStageK p chi Dc) +
    2 * omega * Real.log Dc⁻¹ +
    2 * omega ^ 2 * Real.log chi⁻¹
end
end FirstPassageLinearTransport


