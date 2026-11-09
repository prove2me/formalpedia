-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Counter
-- name    : PulseSyncLowerBound_Pulse_Counter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:34.969888+00:00
-- url     : https://prove2.me/theorems/70cb08bb-9708-4c7b-9158-120d180e4fa0
-- title:
--   The augmented pulse-to-counting protocol
-- statement:
--   For a pulse protocol and a natural skew $\sigma$, set $q=2\sigma+1$ and augment each local state with a counter in $\{0,\ldots,2\sigma\}$. All augmented states are allowed except that a state whose pulse output is one must have counter zero. Every underlying pulse state has at least one such augmented state.
--
--   First simulate the original pulse transition using the projected received states. If its new state pulses, set the new counter to zero; otherwise set it to $\min\{2\sigma,c+1\}$. The counting output is the counter. The state constraint is preserved by this update.
--
--   This is the actual finite-state construction in the reduction. Its transition has no access to global time. A default counter of zero on a missing self-message only totalizes the function on inputs that a surviving process can never receive.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; §2.3, Non-trivial counting reduces to pulse synchronisation; PDF p.8–9 / printed p.6–7; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Tasks

noncomputable section

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ}

/-- §2.3, PDF 8 / printed 6: all counters are initially allowed except that
a pulse state must carry zero. The same condition is preserved by each update. -/
def CounterState (P : Protocol n Bool) (σ : ℕ) (i : Fin n) :=
  {p : P.State i × Fin (2 * σ + 1) // P.output i p.1 = true → p.2.val = 0}

instance (P : Protocol n Bool) (σ : ℕ) (i : Fin n) : Fintype (CounterState P σ i) :=
  by unfold CounterState; infer_instance

instance (P : Protocol n Bool) (σ : ℕ) (i : Fin n) : Nonempty (CounterState P σ i) :=
  ⟨⟨⟨Classical.choice (P.nonemptyState i), ⟨0, by omega⟩⟩, fun _ => rfl⟩⟩

/-- First simulate the original pulse transition; then reset or saturate.
On a missing own message the default zero is irrelevant to every operational run. -/
def counterTransition (P : Protocol n Bool) (σ : ℕ) (i : Fin n)
    (M : (j : Fin n) → Option (CounterState P σ j)) : CounterState P σ i := by
  let s := P.transition i (fun j => (M j).map (fun x => x.val.1))
  let c := ((M i).map (fun x => x.val.2.val)).getD 0
  refine ⟨⟨s, ⟨if P.output i s = true then 0 else min (2 * σ) (c + 1), ?_⟩⟩, ?_⟩
  · split_ifs <;> omega
  · intro h
    simp [h]

/-- The actual augmented protocol of §2.3, with modulus q = 2σ+1. -/
def counterProtocol (P : Protocol n Bool) (σ : ℕ) : Protocol n (Fin (2 * σ + 1)) where
  State := CounterState P σ
  finiteState := fun _ => inferInstance
  nonemptyState := fun _ => inferInstance
  transition := counterTransition P σ
  output := fun _ x => x.val.2

end PulseSyncLowerBound.Pulse


