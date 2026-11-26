-- Prove2me | Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
-- name    : FirstPassageLinearTransport_SharpJointExceptionalOrders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:19:10.254593+00:00
-- url     : https://prove2.me/theorems/f0d996ea-c7af-575c-b165-c346ae1bc485
-- title:
--   Sharp Joint Exceptional Orders
-- statement:
--   Definitions and structural lemmas for Sharp Joint Exceptional Orders, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
def HasVariableTargetHeightWitness
    (f u : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u n * (n : ℝ)
noncomputable def shellVariableTargetHeightFailure
    (M : ℕ) (f u : ℕ → ℝ) :
    Finset {n : ℕ // n ∈ dyadicShell M} := by
  classical
  exact Finset.univ.filter fun n =>
    ¬HasVariableTargetHeightWitness f u n.1
noncomputable def variableTargetHeightFailureCount
    (f u : ℕ → ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n =>
    ¬HasVariableTargetHeightWitness f u n).card
def lastCompleteDyadicShell (X : ℕ) : ℕ := Nat.log 2 X - 1
end
end FirstPassageLinearTransport


