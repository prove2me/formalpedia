-- Prove2me | Definitions.Def_RedundancyStab_IID_ROSChain
-- name    : RedundancyStab_IID_ROSChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:07.29698+00:00
-- url     : https://prove2.me/theorems/967f161a-b93c-4241-b936-5748b6fb5a4b
-- title:
--   §3, p. 5 — the Random Order of Service chain of the redundancy-d model with i.i.d. copies
-- statement:
--   Under **Random Order of Service (ROS)** each server serves one copy at a time at full capacity, and a server that becomes idle chooses uniformly at random a new copy from its queue. Copies are i.i.d. $\mathrm{Exp}(\mu)$ and a job leaves (all copies removed) as soon as one of its copies completes.
--
--   To obtain a Markov chain one must record which jobs are in service. Jobs of the same type in service at the same set of servers are exchangeable, so the state is a family of counts
--   $$k_{c,A}\in\mathbb N,\qquad c\in C,\ A\subseteq c,$$
--   the number of type-$c$ jobs whose copies are in service exactly at the servers of $A$ ($A=\varnothing$: waiting everywhere). The number of type-$c$ jobs is $N_c=\sum_A k_{c,A}$. The empty state is $k=0$. In every state reachable from the empty state each server serves at most one copy, a server that serves nothing has an empty queue, and $k_{c,A}=0$ unless $A\subseteq c$ (`RosValid`).
--
--   The transitions are:
--   1. **Arrival** of a type-$c$ job, at rate $\lambda/\binom{K}{d}$: its copies at the idle servers of $c$ enter service at once, so the job joins the class $(c,\{s\in c: s\text{ idle}\})$.
--   2. **Completion** of a copy: every copy in service completes at rate $\mu$, so a job of class $(c,A)$ leaves at rate $\mu|A|k_{c,A}$. The job and its copies are removed, and every server $s\in A$, now idle, picks a copy uniformly at random among the copies waiting in its queue (that job moves from class $(c',A')$ to $(c',A'\cup\{s\})$); with an empty queue it stays idle. The picks of the freed servers are independent.
--
--   The exit rate is $\lambda+\mu\cdot(\text{number of copies in service})$.
--
--   This is the ROS half of the state space and dynamics that Proposition 3 is about.
--
--   **Formalization Note** The state type is `JobType K d → Finset (Fin K) → ℕ`, unconstrained; the constraints above are recorded as `RosValid` and hold on the class reachable from `rosEmpty`, which is where Proposition 3 is stated. The independent picks of the freed servers are implemented as successive `PMF.bind`s over the servers of $A$ in increasing order (`rosRefill`); this gives the same law because a pick does not change the set of jobs with a copy waiting at another server. A pick at server $s$ weighs the class $(c',A')$ by $k_{c',A'}$ when $s\in c'$, $s\notin A'$ (`rosWaitWeight`), normalised with `PMF.normalize`. The next event is drawn with the same `clockStep` as for PS (junk self-loop only if a rate is negative or all rates vanish, impossible under $\lambda>0$, $\mu>0$, $d\le K$).
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 5, §3 (ROS discipline, i.i.d. copies, cancel-on-complete, Markovian descriptor)

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

namespace RedundancyStab.IID

open Finset
open scoped ENNReal

/-- A state of the ROS chain with i.i.d. copies: `k c A` is the number of type-`c` jobs whose
copies are in service exactly at the servers of `A ⊆ c` (`A = ∅`: no copy of the job is in
service). Jobs of one type served at the same set of servers are exchangeable, so these counts
are a Markovian descriptor of the system (§3, p. 5). -/
abbrev RosState (K d : ℕ) := JobType K d → Finset (Fin K) → ℕ

/-- The empty ROS state. -/
def rosEmpty (K d : ℕ) : RosState K d := 0

/-- `N_c = Σ_A k c A`, the number of type-`c` jobs in the ROS state `k`. -/
def rosJobs (K d : ℕ) (k : RosState K d) (c : JobType K d) : ℕ :=
  ∑ A, k c A

/-- The number of jobs in service at server `s` (`0` or `1` in a valid state). -/
def rosBusy (K d : ℕ) (k : RosState K d) (s : Fin K) : ℕ :=
  ∑ c, ∑ A ∈ univ.filter (fun A : Finset (Fin K) => s ∈ A), k c A

/-- The constraints a configuration of the ROS system satisfies: each server serves at most
one copy; a server serving nothing has an empty queue (an idle server immediately picks a copy
from its queue); a job is in service only at servers among its own `d` servers. Every state
reachable from `rosEmpty` satisfies them. -/
def RosValid (K d : ℕ) (k : RosState K d) : Prop :=
  (∀ s, rosBusy K d k s ≤ 1) ∧
  (∀ s, rosBusy K d k s = 0 → ∀ c ∈ typesAt K d s, rosJobs K d k c = 0) ∧
  (∀ c A, ¬ A ⊆ c.1 → k c A = 0)

/-- Add one job to the class `(c, A)`. -/
def rosAdd (K d : ℕ) (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) :
    RosState K d :=
  Function.update k c (Function.update (k c) A (k c A + 1))

/-- Remove one job from the class `(c, A)`. -/
def rosRemove (K d : ℕ) (k : RosState K d) (c : JobType K d) (A : Finset (Fin K)) :
    RosState K d :=
  Function.update k c (Function.update (k c) A (k c A - 1))

/-- Arrival of a type-`c` job: its copies at the idle servers of `c` enter service at once (an
idle server has an empty queue, so the new copy is the only one it can choose); the job joins
the class `(c, {s ∈ c : s idle})`. -/
def rosArrive (K d : ℕ) (k : RosState K d) (c : JobType K d) : RosState K d :=
  rosAdd K d k c (c.1.filter (fun s => rosBusy K d k s = 0))

/-- The idle server `s` starts serving a copy of a job of the class `(c, A)` (`s ∈ c`, `s ∉ A`):
that job moves to the class `(c, A ∪ {s})`. -/
def rosStartAt (K d : ℕ) (k : RosState K d) (s : Fin K) (c : JobType K d)
    (A : Finset (Fin K)) : RosState K d :=
  rosAdd K d (rosRemove K d k c A) c (insert s A)

/-- Weight of the class `(c, A)` in the choice of an idle server `s`: the number of jobs of that
class that have a copy waiting at `s`, i.e. `k c A` if `s ∈ c` and `s ∉ A`, else `0`. -/
def rosWaitWeight (K d : ℕ) (k : RosState K d) (s : Fin K)
    (p : JobType K d × Finset (Fin K)) : ℝ≥0∞ :=
  if s ∈ p.1.1 ∧ s ∉ p.2 then (k p.1 p.2 : ℝ≥0∞) else 0

open Classical in
/-- Random Order of Service at an idle server `s`: it picks a copy uniformly at random among the
copies waiting in its queue, i.e. a class `(c, A)` with probability proportional to the number
of its jobs waiting at `s`; with an empty queue it stays idle. -/
noncomputable def rosPick (K d : ℕ) (k : RosState K d) (s : Fin K) : PMF (RosState K d) :=
  if h : ∑ p, rosWaitWeight K d k s p ≠ 0 ∧ ∑ p, rosWaitWeight K d k s p ≠ ⊤ then
    (PMF.normalize (rosWaitWeight K d k s) (by rw [tsum_fintype]; exact h.1)
      (by rw [tsum_fintype]; exact h.2)).map (fun p => rosStartAt K d k s p.1 p.2)
  else PMF.pure k

/-- The servers of a list, freed by a departure, each choose a new copy in turn (in the order of
the list); the choices are independent because a choice does not change the set of jobs with a
copy waiting at another server. -/
noncomputable def rosRefill (K d : ℕ) : List (Fin K) → RosState K d → PMF (RosState K d)
  | [], k => PMF.pure k
  | s :: l, k => (rosPick K d k s).bind (rosRefill K d l)

/-- Events of the ROS chain: `Sum.inl c` = arrival of a type-`c` job; `Sum.inr (c, A)` =
completion of a copy of a job of the class `(c, A)`. -/
abbrev RosEvent (K d : ℕ) := JobType K d ⊕ (JobType K d × Finset (Fin K))

/-- Rates of the ROS chain with i.i.d. `Exp(μ)` copies: a type-`c` arrival at rate
`λ / C(K,d)`; every copy in service completes at rate `μ` (a server serves one copy at a time
at full capacity), so a job of the class `(c, A)` leaves at rate `μ |A| k c A`. -/
noncomputable def rosEventRate (K d : ℕ) (lam μ : ℝ) (k : RosState K d) : RosEvent K d → ℝ
  | Sum.inl _ => lam / (K.choose d : ℝ)
  | Sum.inr p => μ * (p.2.card : ℝ) * (k p.1 p.2 : ℝ)

/-- What happens after an event: an arrival as in `rosArrive`; after a completion in the class
`(c, A)` the job leaves, all its copies are removed, and the servers of `A` (now idle) each pick
a new copy from their queues. -/
noncomputable def rosNext (K d : ℕ) (k : RosState K d) : RosEvent K d → PMF (RosState K d)
  | Sum.inl c => PMF.pure (rosArrive K d k c)
  | Sum.inr p => rosRefill K d (p.2.sort (· ≤ ·)) (rosRemove K d k p.1 p.2)

/-- The exit rate of the ROS chain: `λ + μ ·` (number of copies in service) when `d ≤ K`. -/
noncomputable def rosRate (K d : ℕ) (lam μ : ℝ) (k : RosState K d) : ℝ :=
  ∑ e, rosEventRate K d lam μ k e

/-- The jump matrix of the ROS chain with i.i.d. copies. -/
noncomputable def rosJump (K d : ℕ) (lam μ : ℝ) (k : RosState K d) : PMF (RosState K d) :=
  clockStep (rosEventRate K d lam μ k) (rosNext K d k) k

end RedundancyStab.IID


