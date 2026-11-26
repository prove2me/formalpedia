-- Prove2me | Definitions.Def_O3_AboveTwo
-- name    : O3_AboveTwo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:01:44.07269+00:00
-- url     : https://prove2.me/theorems/58615cbd-d54f-4171-9717-ea916c7b15d3
-- title:
--   Above Two
-- statement:
--   Definitions and structural lemmas for Above Two, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean

import Definitions.Def_O3_Foundation
set_option autoImplicit true
open scoped BigOperators
namespace O3
def AboveTwoRegime (p : ℝ) : Prop := 2 < p
noncomputable def aboveAlpha (p : ℝ) : ℝ := 2 * (p - 1) / (p + 2)
noncomputable def aboveAP (p : ℝ) : ℝ := 2 ^ (2 - p) / p
noncomputable def aboveEta (p : ℝ) : ℝ := 2 ^ (-p - 2)
noncomputable def aboveTheta (p : ℝ) : ℝ := aboveAP p * aboveEta p
noncomputable def aboveGamma (p : ℝ) (n : ℕ) (B : ℝ) : ℝ :=
  (n : ℝ) ^ ((p - 2) / p) * B ^ (2 - p)
noncomputable def aboveStepWeight (M : ℝ) (t : ℕ) : ℝ := (t : ℝ) / M
noncomputable def aboveAccumulatedWeight (M : ℝ) (t : ℕ) : ℝ :=
  (t : ℝ) * (t + 1 : ℕ) / (2 * M)
noncomputable def aboveMu (p eps D : ℝ) : ℝ :=
  aboveEta p * eps / D ^ (p - 1)
noncomputable def aboveRho (p eps : ℝ) : ℝ := aboveTheta p * eps
noncomputable def aboveInitialLevel (M D : ℝ) : ℝ := M * D ^ 2
noncomputable def aboveLevel (Delta0 : ℝ) (s : ℕ) : ℝ :=
  Delta0 / (2 : ℝ) ^ s
noncomputable def aboveTerminalLevel (rho M : ℝ) : ℝ :=
  rho ^ 2 / (8 * M)
noncomputable def aboveRestartCount (Delta0 delta : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (Delta0 / delta))
noncomputable def aboveKappa (M D eps : ℝ) : ℝ := M * D / eps
def abovePhaseTrace {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) : List (Observation d) :=
  (List.finRange N).flatMap fun i =>
    [oracle.observe (y i), oracle.observe (accelerated i)]
def AboveObservationTraceExact {d : ℕ} (oracle : PairOracle d)
    (trace : List (Observation d)) : Prop :=
  ∀ observation ∈ trace, observation = oracle.observe observation.point
def aboveRestartTrace {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    List (Observation d) :=
  (List.finRange S).flatMap fun s =>
    abovePhaseTrace oracle (y s) (accelerated s)
def aboveTrialTrace {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) : List (Observation d) :=
  aboveRestartTrace oracle horizons y accelerated ++
    [oracle.observe extraction]
end O3


