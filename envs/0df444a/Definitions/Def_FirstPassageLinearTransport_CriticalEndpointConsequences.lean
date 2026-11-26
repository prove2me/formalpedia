-- Prove2me | Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
-- name    : FirstPassageLinearTransport_CriticalEndpointConsequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:07.46587+00:00
-- url     : https://prove2.me/theorems/c3c099e5-bb09-4464-a96c-f58e45b09b6b
-- title:
--   Critical Endpoint Consequences
-- statement:
--   Definitions and structural lemmas for Critical Endpoint Consequences, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell


set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
theorem dyadicShell_nonempty (M : ℕ) : (dyadicShell M).Nonempty := by
  refine ⟨2 ^ M, mem_dyadicShell.mpr ⟨le_rfl, ?_⟩⟩
  rw [pow_succ]
  have hpos : 0 < 2 ^ M := pow_pos (by omega) _
  omega
def dyadicShellMinimum (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  ((dyadicShell M).image U).min' ((dyadicShell_nonempty M).image U)
def clippedCriticalMultiplier (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  min (Real.sqrt (dyadicShellMinimum U M)) ((M : ℝ) + 2)
def clippedShellHeight (R : ℕ → ℝ) (M : ℕ) : ℝ :=
  min (dyadicShellMinimum R M) ((M : ℝ) + 2)
def criticalMultiplierTerminalRank (U : ℕ → ℝ) (M : ℕ) : ℕ :=
  ⌈timeSupportCriticalExponent * Real.logb 2 ((M : ℝ) + 2) +
    Real.logb 2 (clippedCriticalMultiplier U M)⌉₊
def criticalMultiplierExponent (U : ℕ → ℝ) (M : ℕ) : ℝ :=
  (criticalMultiplierTerminalRank U M : ℝ) /
    Real.logb 2 ((M : ℝ) + 2)
def fixedSharpEndpointMargin (A : ℝ) : ℝ :=
  firstPassageEntropyGap * A - 1 / 2
end
end FirstPassageLinearTransport


