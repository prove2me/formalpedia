-- Prove2me | Definitions.Def_FairGuarantees_DivideChoose_DCRule
-- name    : FairGuarantees_DivideChoose_DCRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:36.68685+00:00
-- url     : https://prove2.me/theorems/a5e72ba8-ef21-42e0-90f8-ef8cfe1a611f
-- title:
--   §4, pp. 14–15 — proper matchings, plays of the D&C_n rule (Definition 4) and the minMax strategy of Theorem 1 i)
-- statement:
--   The Divide & Choose$_n$ rule (Definition 4) as a set of admissible plays.
--
--   1. **Proper matching** (p. 14). In a bipartite "likes" relation between a set $M$ of agents and a set $R$ of shares, $\widetilde M\subseteq M$ is properly matched to $\widetilde R\subseteq R$ when $\widetilde M$ is matched one-to-one onto $\widetilde R$ with every agent getting a share it likes, and no agent of $M\setminus\widetilde M$ likes any share of $\widetilde R$.
--   2. **A step.** A step records the remaining agents $N^k$ ($m=|N^k|$), the remaining manna $S$, the partition $\Pi^k\in\mathcal P_m(S)$ proposed by the Divider (the first remaining agent in the order $1<2<\dots<n$), the shares each agent reports to like, and the assignment of shares. A step is admissible when every remaining agent likes at least one share, the Divider likes all of them, the served agents $N^k_*$ are properly matched to the shares they receive, the Divider is served, and $N^k_*$ is the largest properly matchable set of agents (Lemma 2).
--   3. **Plays.** A play is a finite sequence of admissible steps; the first starts from all $n$ agents and the manna $\Omega$, and each next step starts from the unserved agents and the manna minus the shares just assigned (unassigned shares return to the manna). A play is complete when every agent is served; the share of agent $i$ is the part assigned to $i$.
--   4. **The minMax strategy** of agent $i$ with utility $u$: whenever $i$ is the Divider of a step, $\Pi^k\in\mathcal{EP}_m(S;u)$; otherwise $i$ likes exactly the shares $r$ of $\Pi^k$ with $u(r)\ge\mathrm{minMax}(u;n)$, the minMax level of the **initial** problem.
--
--   The other agents' partitions, reports and the choice among proper matchings are unconstrained beyond admissibility, which is what "guarantee" requires.
--
--   **Formalization Note** Agents are `Fin n` (agent $1$ of the paper is `0`). The parts of a step are indexed by `Fin m`. The assignment is an `Option`-valued map; `Matched s` is the set of served agents and `assignedPart s a` the share of `a` (`∅` if unserved). `IsValidPrefix` is a possibly incomplete play, `IsValidRun` a complete one; `share run i` is the part given to `i` at the step where `i` is served.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 14, §4 (proper matching) and Definition 4; p. 15, Definition 4 Step 2 and the following paragraph; p. 15, Theorem 1 i) (strategy)

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

namespace FairGuarantees.DivideChoose

open MeasureTheory

/-- §4, p. 14: in the bipartite "likes" graph between the agents `M` and the shares `R`, the
agents `M'` are *properly matched* to the shares `R'` by `f`: `M' ⊆ M`, `R' ⊆ R`, `f` maps
`M'` one-to-one onto `R'` (so `|M'| = |R'|`), every agent of `M'` likes the share it is
matched to, and no agent of `M` outside `M'` likes any share in `R'`. -/
def IsProperMatch {α β : Type*} [DecidableEq α] (M : Finset α) (R : Finset β) (likes : α → β → Prop)
    (M' : Finset α) (R' : Finset β) (f : α → β) : Prop :=
  M' ⊆ M ∧ R' ⊆ R ∧ Set.BijOn f (M' : Set α) (R' : Set β) ∧ (∀ a ∈ M', likes a (f a)) ∧
    ∀ a ∈ M \ M', ∀ r ∈ R', ¬ likes a r

/-- One step of the D&C_n rule (Definition 4, pp. 14–15), as recorded in a play of the
rule: the remaining agents, the remaining manna `S`, the partition `Π^k` proposed by the
Divider (indexed by `Fin m`, `m` = number of remaining agents), the reported "likes" of every
agent, and the assignment (`some r` for an agent matched to share `r` at this step). -/
structure DCStep (d n : ℕ) where
  agents : Finset (Fin n)
  manna : Set (E d)
  parts : Fin agents.card → Set (E d)
  likes : Fin n → Fin agents.card → Prop
  assign : Fin n → Option (Fin agents.card)

variable {d n : ℕ}

/-- The Divider of a step: the first remaining agent in the exogenous ordering. -/
def IsDivider (s : DCStep d n) (a : Fin n) : Prop :=
  a ∈ s.agents ∧ ∀ b ∈ s.agents, a ≤ b

/-- The agents served at a step. -/
def Matched (s : DCStep d n) : Finset (Fin n) :=
  s.agents.filter (fun a => (s.assign a).isSome)

/-- The share assigned to agent `a` at step `s` (`∅` if `a` is not served at this step). -/
def assignedPart (s : DCStep d n) (a : Fin n) : Set (E d) :=
  match s.assign a with
  | some r => s.parts r
  | none => ∅

/-- A step is admissible under Definition 4 when: the remaining agents are nonempty, the
remaining manna is a share, the Divider proposes an `m`-partition of it, every remaining
agent likes at least one part, the Divider likes every part, only remaining agents are
assigned, the served agents are properly matched to the shares they receive, the Divider is
served, and the served set is the *largest* properly matchable set of agents. The other
agents' partitions, reports and the choice among proper matchings are otherwise arbitrary. -/
def IsValidStep (Ω : Set (E d)) (s : DCStep d n) : Prop :=
  s.agents.Nonempty ∧ IsShare Ω s.manna ∧ IsPartition Ω s.manna s.agents.card s.parts ∧
  (∀ a ∈ s.agents, ∃ r, s.likes a r) ∧
  (∀ a, IsDivider s a → ∀ r, s.likes a r) ∧
  (∀ a, a ∉ s.agents → s.assign a = none) ∧
  (∃ f : Fin n → Fin s.agents.card, (∀ a ∈ Matched s, s.assign a = some (f a)) ∧
    IsProperMatch s.agents Finset.univ s.likes (Matched s) ((Matched s).image f) f) ∧
  (∀ a, IsDivider s a → a ∈ Matched s) ∧
  (∀ (M' : Finset (Fin n)) (R' : Finset (Fin s.agents.card)) (g : Fin n → Fin s.agents.card),
    IsProperMatch s.agents Finset.univ s.likes M' R' g → M' ⊆ Matched s)

/-- The agents still unserved after a sequence of steps (all agents before the first step). -/
def nextAgents (run : List (DCStep d n)) : Finset (Fin n) :=
  match run.getLast? with
  | none => Finset.univ
  | some s => s.agents \ Matched s

/-- The manna remaining after a sequence of steps (`Ω` before the first step): the shares
assigned at the last step are removed; unassigned parts return to the manna. -/
def nextManna (Ω : Set (E d)) (run : List (DCStep d n)) : Set (E d) :=
  match run.getLast? with
  | none => Ω
  | some s => s.manna \ ⋃ a ∈ Matched s, assignedPart s a

/-- A valid (possibly incomplete) play of the D&C_n rule: each step starts from the agents
and the manna left by the previous steps and is admissible. -/
def IsValidPrefix (Ω : Set (E d)) (run : List (DCStep d n)) : Prop :=
  ∀ (k : ℕ) (hk : k < run.length),
    run[k].agents = nextAgents (run.take k) ∧ run[k].manna = nextManna Ω (run.take k) ∧
      IsValidStep Ω run[k]

/-- A valid complete play of the D&C_n rule: a valid play after which every agent is served. -/
def IsValidRun (Ω : Set (E d)) (run : List (DCStep d n)) : Prop :=
  IsValidPrefix Ω run ∧ nextAgents run = ∅

/-- The share agent `i` receives in a play: the part assigned to `i` at the (first) step at
which `i` is served (`∅` if `i` is never served). -/
def share (run : List (DCStep d n)) (i : Fin n) : Set (E d) :=
  match run.find? (fun s => decide (i ∈ Matched s)) with
  | some s => assignedPart s i
  | none => ∅

/-- The strategy of Theorem 1 i), p. 15, for agent `i` with utility `u`, in the play `run`:
at every step where `i` is still present, (1) if `i` is the Divider, the proposed partition is
an `m`-equipartition of the remaining manna for `u`; (2) otherwise `i` likes exactly the parts
worth at least `minMax(u; n)` of the *initial* problem. -/
def FollowsMinMaxStrategy (Ω : Set (E d)) (u : Set (E d) → ℝ) (i : Fin n)
    (run : List (DCStep d n)) : Prop :=
  ∀ s ∈ run, i ∈ s.agents →
    (IsDivider s i → IsEquipartition Ω u s.manna s.agents.card s.parts) ∧
    (¬ IsDivider s i → ∀ r, s.likes i r ↔ minMax Ω u n ≤ u (s.parts r))

end FairGuarantees.DivideChoose


