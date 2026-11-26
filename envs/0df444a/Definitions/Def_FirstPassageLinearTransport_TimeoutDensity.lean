-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
-- name    : FirstPassageLinearTransport_TimeoutDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:36.571025+00:00
-- url     : https://prove2.me/theorems/05ce8499-6edb-5d43-b2fb-fa14f25096fb
-- title:
--   Timeout Density
-- statement:
--   Definitions and structural lemmas for Timeout Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
noncomputable def collatzTerminalBinIndex
    {m : ℕ} (B : ℝ) (v : Fin m → Bool) : ℕ :=
  ⌊B + wordIncrementSum collatzLogIncrement v⌋₊
noncomputable def collatzSurvivalWords (m : ℕ) (B : ℝ) :
    Finset (Fin m → Bool) := by
  classical
  exact Finset.univ.filter
    (wordSurvivesFrom (-B) collatzLogIncrement m 0)
noncomputable def collatzSurvivalResidues (m : ℕ) (B : ℝ) :
    Finset (Fin (2 ^ m)) := by
  classical
  exact Finset.univ.filter (fun x =>
    wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x))
noncomputable def collatzSurvivalResidueEquiv (m : ℕ) (B : ℝ) :
    {x : Fin (2 ^ m) //
      wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x)} ≃
      {v : Fin m → Bool //
        wordSurvivesFrom (-B) collatzLogIncrement m 0 v} :=
  (boolParityEquiv m).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])
noncomputable def collatzSurvivalShell (m : ℕ) (B : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter (fun x =>
    wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityWord m x))
noncomputable def terminalOddUpperResidues (m k : ℕ) :
    Finset (Fin (2 ^ m)) := by
  classical
  exact Finset.univ.filter fun x => k ≤ oddCount x m
noncomputable def terminalOddUpperShell (m k : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter fun x => k ≤ oddCount x m
theorem exists_two_pow_lt_three_pow_succ (q : ℕ) :
    ∃ s : ℕ, 2 ^ q < 3 ^ (s + 1) := by
  refine ⟨q, ?_⟩
  calc
    2 ^ q ≤ 3 ^ q := Nat.pow_le_pow_left (by omega) q
    _ < 3 ^ (q + 1) := by
      rw [pow_succ]
      have hpos : 0 < 3 ^ q := pow_pos (by omega) _
      nlinarith
noncomputable def timeoutOddThreshold (q : ℕ) : ℕ :=
  Nat.find (exists_two_pow_lt_three_pow_succ q)
def timeoutOddDisplacement (K₀ : ℝ) (L m : ℕ) : ℝ :=
  (timeoutOddThreshold (timeoutTargetRank K₀ L m) : ℝ) / (m : ℝ) - 1 / 2
def timeoutDisplacementLoss (K₀ : ℝ) : ℝ :=
  logThreeTwo * K₀ / 2 + logThreeTwo + 1
def timeoutOddEntropyRate (K₀ : ℝ) (L m : ℕ) : ℝ :=
  binaryBarrierRate (timeoutOddDisplacement K₀ L m)
noncomputable def timeoutShellBad (K₀ : ℝ) (L m : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell m).filter (LowStageTimeout K₀ L m)
def timeoutEndpointT₀ : ℝ :=
  firstPassageEndpointDisplacement / 4
end
end FirstPassageLinearTransport


