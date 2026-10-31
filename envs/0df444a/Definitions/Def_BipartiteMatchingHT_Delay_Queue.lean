-- Prove2me | Definitions.Def_BipartiteMatchingHT_Delay_Queue
-- name    : BipartiteMatchingHT_Delay_Queue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:12:35.302814+00:00
-- url     : https://prove2.me/theorems/aa0f2e3a-74ba-46b3-91ea-464a61f5ca6a
-- title:
--   Concrete FCFS-ALIS queue, equilibrium, and tagged waiting time
-- statement:
--   The raw countable state consists of an unbounded ordered list of present customers, each carrying its class and optional service-server identity, and a longest-idle-first list of idle servers. A Boolean mark is reserved for the tagged-arrival experiment. An arrival takes the first compatible idle server, or appends to the waiting population. A busy-server completion removes its customer, then assigns that server to the oldest compatible waiting customer; if none exists, it appends the server to the idle list. Potential completion events at idle servers do nothing. Ordinary arrivals have no tag.
--
--   The queue instantiates the general Poisson event chain with class arrival rates $\rho\widetilde\lambda_i$ and server-clock rates $\mu_j$. Reachability from empty queues with arbitrary initial idle-server ordering excludes malformed states and preserves distinct server use, compatibility, and nonpreemption. A stationary probability vector is supported on these reachable states and invariant under the event kernel. Stability means existence of such a vector. Heavy-traffic admissibility means stability for every real load sufficiently close to one from below.
--
--   Equilibrium selects a stationary vector when one exists. The tagged class-$i$ arrival is inserted into this equilibrium state independently of future Poisson events. Its waiting time ends at service start, not completion; its mean is the extended hitting-time mean averaged over equilibrium. It is infinity if stability fails. A selected equilibrium vector has the harmless zero extension outside stability, but no waiting-time conclusion uses that extension. Initial idle ties are ordered by the supplied permutation; at positive times independent clocks have no simultaneous events. No product form, Little-law formula, integrability, or heavy-traffic limit is assumed.
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; printed/PDF pp. 2, 7–11, Definition 1

import Definitions.Def_BipartiteMatchingHT_Delay_EventChain
import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

open scoped BigOperators ENNReal
noncomputable section

namespace BipartiteMatchingHT.Delay

/-- Customers stay in arrival order, including customers in service. The mark is
used only for the single tagged arrival in the waiting-time experiment. -/
structure Job (n m : ℕ) where
  kind : Fin n
  server : Option (Fin m)
  tagged : Bool
  deriving DecidableEq

structure QueueState (n m : ℕ) where
  jobs : List (Job n m)
  idle : List (Fin m)
  deriving DecidableEq

variable {n m : ℕ}

def serverList (s : Equiv.Perm (Fin m)) : List (Fin m) := List.ofFn s

def emptyQueue (s : Equiv.Perm (Fin m)) : QueueState n m := ⟨[], serverList s⟩

/-- ALIS chooses the first compatible entry of the longest-idle-first list. -/
def arrival (D : Model n m) (q : QueueState n m) (i : Fin n) (tag : Bool := false) :
    QueueState n m :=
  match q.idle.find? (D.compatible i) with
  | none => ⟨q.jobs ++ [⟨i, none, tag⟩], q.idle⟩
  | some j => ⟨q.jobs ++ [⟨i, some j, tag⟩], q.idle.erase j⟩

/-- Give j to the earliest compatible waiting customer, preserving arrival order. -/
def allocate (D : Model n m) (j : Fin m) : List (Job n m) → List (Job n m)
  | [] => []
  | x :: xs => if x.server.isNone && D.compatible x.kind j then
      { x with server := some j } :: xs else x :: allocate D j xs

def completion (D : Model n m) (q : QueueState n m) (j : Fin m) : QueueState n m :=
  if q.jobs.any (fun x => x.server == some j) then
    let rest := q.jobs.filter (fun x => x.server != some j)
    if rest.any (fun x => x.server.isNone && D.compatible x.kind j) then
      ⟨allocate D j rest, q.idle⟩
    else ⟨rest, q.idle ++ [j]⟩
  else q

/-- An arrival mark or a potential service-completion mark. Idle-server marks
are null events, allowing a constant total rate and no explosion. -/
abbrev Event (n m : ℕ) := Fin n ⊕ Fin m

def queueStep (D : Model n m) (q : QueueState n m) : Event n m → QueueState n m
  | .inl i => arrival D q i
  | .inr j => completion D q j

/-- Reachability from an empty queue excludes malformed raw states without
assuming any equilibrium law or stochastic performance identity. -/
def Reachable (D : Model n m) (q : QueueState n m) : Prop :=
  ∃ s : Equiv.Perm (Fin m), ∃ events : List (Event n m),
    events.foldl (queueStep D) (emptyQueue s) = q

def queueChain (D : Model n m) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    EventChain (QueueState n m) (Event n m) where
  rate := Sum.elim (fun i => ρ * D.nominal i) D.service
  nonneg := by
    intro e
    cases e with
    | inl i => exact mul_nonneg hρ (le_of_lt (D.nominal_pos i))
    | inr j => exact le_of_lt (D.service_pos j)
  total_pos := by
    rw [Fintype.sum_sum_type]
    have ha : 0 ≤ ∑ i, ρ * D.nominal i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg hρ (le_of_lt (D.nominal_pos i)))
    have hb : 0 < ∑ j, D.service j :=
      Finset.sum_pos' (fun j _ => le_of_lt (D.service_pos j))
        ⟨⟨0, D.servers_pos⟩, Finset.mem_univ _, D.service_pos _⟩
    exact add_pos_of_nonneg_of_pos ha hb
  step := queueStep D

def stationary (D : Model n m) (ρ : ℝ) (p : QueueState n m → ℝ≥0∞) : Prop :=
  ∃ hρ : 0 ≤ ρ, (queueChain D ρ hρ).IsStationary p ∧
    ∀ q, ¬ Reachable D q → p q = 0

def Stable (D : Model n m) (ρ : ℝ) : Prop := ∃ p, stationary D ρ p

/-- Definition 1 and its limiting family: eventual operational stationarity as
real rho approaches 1 from below; no Hall/slack or CRP result is assumed. -/
def Admissible (D : Model n m) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ ρ, r < ρ → ρ < 1 → Stable D ρ

def equilibrium (D : Model n m) (ρ : ℝ) : QueueState n m → ℝ≥0∞ := by
  classical
  exact if h : Stable D ρ then Classical.choose h else fun _ => 0

def tagStarted (q : QueueState n m) : Prop :=
  ¬ ∃ x ∈ q.jobs, x.tagged = true ∧ x.server = none

/-- Stationary tagged-arrival experiment. Poisson arrivals see equilibrium;
insert a tagged class-i customer and wait until its service starts. The extended
mean is infinity if no stationary law exists (never silently zero). -/
def meanWait (D : Model n m) (ρ : ℝ) (i : Fin n) : ℝ≥0∞ := by
  classical
  exact if h : 0 ≤ ρ ∧ Stable D ρ then
    ∑' q, equilibrium D ρ q *
      (queueChain D ρ h.1).meanHitting tagStarted (arrival D q i true)
  else ⊤

end BipartiteMatchingHT.Delay


