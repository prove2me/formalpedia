-- Prove2me | Definitions.Def_HighUncertHT_Game_Priority
-- name    : HighUncertHT_Game_Priority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:03.274296+00:00
-- url     : https://prove2.me/theorems/f45b1402-2d3f-4636-be14-182bc009e14f
-- title:
--   §2.2, p. 9 — the nonpreemptive cµ strategy β*ⁿ (priority to the largest hµ)
-- statement:
--   The **nonpreemptive cµ policy** is the non-preemptive fixed priority policy for the labelling (14): service is noninterruptible, and whenever the server becomes available (or the system is empty and a new arrival occurs) it admits into service the head-of-line job of the highest-priority type among those waiting (or arriving) at that moment; within a type jobs are served first in, first out. Priority is decreasing in the index from type $L$ (largest $h\mu$) down to type 1 (smallest $h\mu$, ties broken by index).
--
--   The strategy $\beta^{*n}$ is defined by an event recursion over service decisions. The $m$-th decision is taken at time $\tau_m=\max(\text{time the server becomes free},\ \text{earliest arrival time of a next job})$; it starts the next job of the highest-priority type whose next job has arrived by $\tau_m$; a job of size $x$ keeps the server busy for $x/n$ time units. Then
--   $$
--   B^{*\ell n}_t=\mathrm{Leb}\{s\in[0,t]:\text{a type-}\ell\text{ job is in service at time }s\}.
--   $$
--
--   **Formalization Note** The page says the policy admits "a job of the type that has lowest index"; with the labelling $h^1\mu^1\le\dots\le h^L\mu^L$ this contradicts the cµ rule named in the same paragraph and Lemma 5 (the workload concentrates on "the lowest-priority type", type 1). The corrected rule, priority to the **highest** index, is formalized. Types are 0-based (`Fin L`). The policy reads only the job sizes of the control path, and is meant for $n\ge1$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 9, §2.2, first paragraph (non-preemptive fixed priority policy, nonpreemptive cµ policy β*ⁿ)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System

namespace HighUncertHT.Game

open MeasureTheory

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.2, p. 9: the nonpreemptive cµ strategy `β^{*n}`.

"Service is noninterruptible and whenever the server becomes available (or the system is empty and
a new arrival occurs) it admits into service a job of the type that has [highest] index waiting in
the queue (or arriving) at that moment." The page prints "lowest index"; with the labelling (14),
`h¹µ¹ ≤ ⋯ ≤ h^Lµ^L`, the cµ rule named in the same paragraph, Lemma 5 ("the workload is
concentrated on the lowest-priority type", type 1) and its proof all require priority to the
**highest** index (largest `hµ`), which is what is formalized. Ties in `hµ` are broken by index.

The policy is an event recursion over service decisions. The state after `m` decisions holds the
time `free` at which the server becomes free and, for each type `ℓ`, the (paper, 1-based) index
`next ℓ` of the next unserved type-`ℓ` job; within a type jobs are served FIFO. Job `k` of every
type arrives at time `k/n`. At a decision the server waits, if necessary, until the earliest
arrival of a next job, `τ = max(free, min_ℓ next ℓ / n)`, then starts the next job of the
highest-index type whose next job has arrived by `τ` (arrivals exactly at `τ` included). A job of
size `x` occupies the server, at rate `n`, for `x/n` time units (size `0`: zero time). `B^ℓ_t` is
the Lebesgue measure of the set of times in `[0, t]` during which a type-`ℓ` job is in service.
The policy uses only the job sizes of the control path. It is meant for `n ≥ 1`.
-/

variable {L : ℕ}

/-- State of the priority recursion: the time the server becomes free and, per type, the
1-based index of the next unserved job. -/
structure PriorityState (L : ℕ) where
  free : ℝ
  next : Fin L → ℕ

/-- The size of the paper's `k`-th type-`ℓ` job (`k ≥ 1`) in a 0-based control path. -/
def jobSize (a : ControlPath L) (k : ℕ) (ℓ : Fin L) : ℝ := (a (k - 1)).2 ℓ

namespace PriorityState

/-- The time of the next service decision: the server is free and some next job has arrived. -/
noncomputable def decisionTime (S : Setting L) (n : ℕ) (σ : PriorityState L) : ℝ :=
  max σ.free (Finset.univ.inf' ⟨S.first, Finset.mem_univ _⟩ (fun ℓ => (σ.next ℓ : ℝ) / n))

/-- The type served at the decision: the highest-index type whose next job has arrived by the
decision time (nonempty: a type attaining `min_ℓ next ℓ / n` qualifies). -/
noncomputable def chosen (S : Setting L) (n : ℕ) (σ : PriorityState L) : Fin L :=
  (Finset.univ.filter (fun ℓ => (σ.next ℓ : ℝ) / n ≤ σ.decisionTime S n)).max' (by
    obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
      ⟨S.first, Finset.mem_univ _⟩ (fun ℓ => (σ.next ℓ : ℝ) / n)
    exact ⟨ℓ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hℓ.symm.le.trans (le_max_right _ _)⟩⟩)

/-- One service decision: serve the next job of the chosen type from the decision time on. -/
noncomputable def step (S : Setting L) (n : ℕ) (a : ControlPath L) (σ : PriorityState L) :
    PriorityState L :=
  { free := σ.decisionTime S n + jobSize a (σ.next (σ.chosen S n)) (σ.chosen S n) / n
    next := Function.update σ.next (σ.chosen S n) (σ.next (σ.chosen S n) + 1) }

/-- The initial state: the system is empty at time `0`; every type's next job is its first. -/
def init (L : ℕ) : PriorityState L := { free := 0, next := fun _ => 1 }

end PriorityState

/-- The state after `m` service decisions under the priority policy. -/
noncomputable def priorityState (S : Setting L) (n : ℕ) (a : ControlPath L) :
    ℕ → PriorityState L
  | 0 => PriorityState.init L
  | m + 1 => (priorityState S n a m).step S n a

/-- The service interval `[start, end)` of the `m`-th service decision (0-based). -/
noncomputable def serviceInterval (S : Setting L) (n : ℕ) (a : ControlPath L) (m : ℕ) : Set ℝ :=
  Set.Ico ((priorityState S n a m).decisionTime S n) (priorityState S n a (m + 1)).free

/-- The nonpreemptive cµ strategy `β^{*n}` (p. 9, priority to the highest index): `B^ℓ_t` is the
Lebesgue measure of the times in `[0, t]` during which a type-`ℓ` job is in service. -/
noncomputable def betaStar (S : Setting L) (n : ℕ) (a : ControlPath L) : EffortPath L :=
  fun t ℓ => (volume (Set.Icc 0 t ∩
    ⋃ m ∈ {m : ℕ | (priorityState S n a m).chosen S n = ℓ}, serviceInterval S n a m)).toReal

end HighUncertHT.Game


