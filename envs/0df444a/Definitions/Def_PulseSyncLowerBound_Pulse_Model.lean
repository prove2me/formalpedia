-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Model
-- name    : PulseSyncLowerBound_Pulse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:49.614803+00:00
-- url     : https://prove2.me/theorems/ea64113b-1e56-4725-94c5-303bad44ce1d
-- title:
--   Finite-state synchronous protocols and infinite crash executions
-- statement:
--   There are $n$ permanent process identities. Each process chooses an arbitrary finite nonempty state space, a deterministic time-independent transition on identity-tagged received states, and a state output. Initial configurations include every choice of one state per process. In each round survivors receive all survivors' previous states, including their own; newly crashing senders may omit messages to independently chosen recipients, and crashed processes stay absent forever.
--
--   An execution is an infinite sequence of configurations and permitted message deliveries. A process is non-faulty exactly when it is never absent. The total crash budget counts the identities ever absent. For every full initial state tuple, `cleanExecution` constructs its unique trajectory without crashes. Thus the execution model is inhabited independently of task correctness.
--
--   These general operational objects are separate from the pulse and counting specifications. Nonempty local state spaces express the operational convention that every process has a state, used explicitly in the source's Lemma 12 proof.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; §2 model and §5.3, Configurations and protocols / Views and executions; PDF p.5,18–19 / printed p.3,16–17; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Mathlib

noncomputable section

namespace PulseSyncLowerBound.Pulse

/-- §2 and §5.3 (PDF 5,18): finite nonempty local states, permanent identities,
and a deterministic transition with no time argument. Messages contain at most one
state per identity. No correctness condition is part of a protocol. -/
structure Protocol (n : ℕ) (O : Type) where
  State : Fin n → Type
  finiteState : ∀ i, Fintype (State i)
  nonemptyState : ∀ i, Nonempty (State i)
  transition : (i : Fin n) → ((j : Fin n) → Option (State j)) → State i
  output : (i : Fin n) → State i → O

attribute [instance] Protocol.finiteState Protocol.nonemptyState
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {O : Type}

abbrev Configuration (P : Protocol n O) := (i : Fin n) → Option (P.State i)

/-- Survivors receive every survivor's old state, including their own.
Only processes crashing in this round can omit their messages selectively. -/
def Round (P : Protocol n O) (a b : Configuration P)
    (M : (i : Fin n) → Configuration P) : Prop :=
  ∀ i s', b i = some s' →
    (∃ s, a i = some s) ∧
    (∀ j, M i j = none ∨ M i j = a j) ∧
    (∀ j, b j ≠ none → M i j = a j) ∧
    s' = P.transition i (M i)

/-- Infinite operational executions; every full initial configuration is admitted. -/
structure Execution (P : Protocol n O) where
  config : ℕ → Configuration P
  messages : ℕ → (i : Fin n) → Configuration P
  initial : ∀ i, ∃ s, config 0 i = some s
  step : ∀ t, Round P (config t) (config (t + 1)) (messages t)

def Nonfaulty {P : Protocol n O} (e : Execution P) (i : Fin n) : Prop :=
  ∀ t, e.config t i ≠ none

/-- Counts identities ever absent, rather than summing a per-round fault budget. -/
def AtMostCrashes {P : Protocol n O} (e : Execution P) (f : ℕ) : Prop :=
  (Finset.univ.filter (fun i => ∃ t, e.config t i = none)).card ≤ f

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The unrestricted crash-free trajectory from arbitrary initial local states. -/
def cleanStates (P : Protocol n O) (s : (i : Fin n) → P.State i) :
    ℕ → (i : Fin n) → P.State i
  | 0 => s
  | t + 1 => fun i => P.transition i (fun j => some (cleanStates P s t j))

/-- A constructive witness that the execution type is inhabited for every protocol
and every full initial configuration. -/
def cleanExecution (P : Protocol n O) (s : (i : Fin n) → P.State i) : Execution P where
  config t i := some (cleanStates P s t i)
  messages t _ j := some (cleanStates P s t j)
  initial i := ⟨s i, rfl⟩
  step t i s' h := by
    refine ⟨⟨cleanStates P s t i, rfl⟩, ?_, ?_, ?_⟩
    · intro j; exact Or.inr rfl
    · intro j _; rfl
    · exact (Option.some.inj h).symm

end PulseSyncLowerBound.Pulse


