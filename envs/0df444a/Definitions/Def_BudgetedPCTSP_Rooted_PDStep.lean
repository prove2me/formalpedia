-- Prove2me | Definitions.Def_BudgetedPCTSP_Rooted_PDStep
-- name    : BudgetedPCTSP_Rooted_PDStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:28:41.80587+00:00
-- url     : https://prove2.me/theorems/8a68233f-9290-4ad4-b61a-e32848a3efee
-- title:
--   Algorithm 1 — the primal-dual subroutine PD(λ₁) as an event-driven process with arbitrary tie-breaking
-- statement:
--   Fix an instance $(G, c, D, r)$ and a value $\lambda_1 \ge 0$. The **primal-dual subroutine** PD($\lambda_1$) maintains dual variables $y_S \ge 0$ for all $S \subseteq V$, a set $T$ of tight edges, and a partition of $V$ into **components** (the vertex sets of the connected components of $(V, T)$), each of which is **active** or **inactive**. For an edge $e$ and a set $S$ write $e \in \delta(S)$ if $e$ has exactly one endpoint in $S$.
--
--   At the start $y \equiv 0$, $T = \emptyset$, and every singleton $\{i\}$ is an active component. The duals $y_S$ of all active components $S$ are then raised simultaneously at unit rate until an **event** happens:
--
--   - an active set $S$ becomes **neutral**, i.e. $2\sum_{T \subseteq S} y_T = |S|$; this happens after time $\tfrac12|S| - \sum_{T \subseteq S} y_T$. Then $S$ is marked inactive.
--   - the dual constraint $\sum_{S : e \in \delta(S)} y_S \le \lambda_1 c_e$ of an edge $e = \{u, v\}$ between two different components $S_1 \ni u$ and $S_2 \ni v$, at least one of them active, becomes tight; this happens after time $\lambda_1 c_e - \sum_{S : e \in \delta(S)} y_S$ if one of $S_1, S_2$ is active and half that time if both are. Then $e$ is added to $T$, and $S_1, S_2$ are replaced by the active component $S_1 \cup S_2$.
--
--   The process stops when no component is active. The family $\mathcal S$ collects every set that is active at some moment, including for a period of length zero, and $\mathcal S^+ = \mathcal S \cup \{V\}$.
--
--   Formally, one step of the process goes from a state to the next: with $\Delta$ the minimum over all possible events of the time until that event, every active $y_S$ is increased by $\Delta$, and one event whose time equals $\Delta$ is processed. A **complete run** is a finite sequence of steps from the start to a state with no active set.
--
--   **Formalization Note.** The continuous process is discretized into its events, and event times are recomputed after every event. When several events are due at the same time, any one of them may be processed first; this is how the paper's "we break ties in some order" (p. 8) is represented, so `IsCompleteRun` covers every tie-breaking order and statements quantified over complete runs hold for all of them. The pruning phase of Algorithm 1 (which produces the tree $T'$) is not modelled, because no statement of this mission uses $T'$. The step relation does not itself require $\Delta \ge 0$; nonnegativity of all event times in reachable states is a consequence of the invariants stated in the milestones.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript pp. 4-6, Section 3, Algorithm 1; event times p. 8

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance

namespace BudgetedPCTSP.Rooted

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `Crosses S e` means `e ∈ δ(S)`: the unordered pair `e` has exactly one endpoint in `S`. -/
def Crosses (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ u ∈ S, ∃ v ∉ S, e = s(u, v)

open Classical in
/-- The left-hand side `∑_{S : e ∈ δ(S)} y_S` of the dual constraint of the edge `e` (p. 4),
the sum running over all vertex sets `S ⊆ V` that `e` crosses. -/
noncomputable def edgeLoad (y : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S => Crosses S e), y S

/-- The state of the primal-dual subroutine PD(λ₁) (Algorithm 1, p. 5) between two events. -/
structure PDState (V : Type) where
  /-- The current components: the vertex sets of the connected components of `(V, T)`. -/
  comps : Finset (Finset V)
  /-- The components currently in the collection of active sets. -/
  active : Finset (Finset V)
  /-- The dual variables `y_S`, one for every vertex set `S ⊆ V`. -/
  y : Finset V → ℝ
  /-- The set `T` of tight edges added so far. -/
  T : Finset (Sym2 V)
  /-- The collection `𝒮` of all sets that have been active at some moment so far, including
  sets active for a period of length zero (p. 6). -/
  everActive : Finset (Finset V)

/-- The start of PD(λ₁) (Algorithm 1): `y_S = 0` for all `S`, `T = ∅`, and every singleton
`{i}`, `i ∈ V`, is a component and is active. -/
def PDState.init : PDState V where
  comps := Finset.univ.image (fun i => {i})
  active := Finset.univ.image (fun i => {i})
  y := fun _ => 0
  T := ∅
  everActive := Finset.univ.image (fun i => {i})

/-- The time, measured from the current state, at which the active set `S` becomes neutral if
nothing else happens first: `½|S| - ∑_{T ⊆ S} y_T` (p. 8). -/
noncomputable def neutralTime (s : PDState V) (S : Finset V) : ℝ :=
  (S.card : ℝ) / 2 - ∑ T ∈ S.powerset, s.y T

/-- The number of active sets among the two components `S₁`, `S₂`. -/
def activeCount (s : PDState V) (S₁ S₂ : Finset V) : ℕ :=
  (if S₁ ∈ s.active then 1 else 0) + (if S₂ ∈ s.active then 1 else 0)

/-- The edge `s(u, v)` of `G` joins two different current components `S₁ ∋ u` and `S₂ ∋ v`, at
least one of which is active: its dual constraint is being raised and it may become tight. -/
def IsEdgeCandidate (I : Instance V) (s : PDState V) (S₁ S₂ : Finset V) (u v : V) : Prop :=
  I.G.Adj u v ∧ S₁ ∈ s.comps ∧ S₂ ∈ s.comps ∧ u ∈ S₁ ∧ v ∈ S₂ ∧ S₁ ≠ S₂ ∧
    (S₁ ∈ s.active ∨ S₂ ∈ s.active)

/-- The time, measured from the current state, at which the dual constraint
`∑_{S : e ∈ δ(S)} y_S ≤ λ₁ c_e` of the candidate edge `e = s(u, v)` between the components
`S₁ ∋ u` and `S₂ ∋ v` becomes tight if nothing else happens first (p. 8):
`λ₁ c_e - ∑_{T : e ∈ δ(T)} y_T` when exactly one of `S₁`, `S₂` is active, and half that amount
when both are active. -/
noncomputable def edgeTime (I : Instance V) (lam : ℝ) (s : PDState V) (S₁ S₂ : Finset V)
    (u v : V) : ℝ :=
  (lam * I.c s(u, v) - edgeLoad s.y s(u, v)) / (activeCount s S₁ S₂ : ℝ)

/-- `Δ` is the time until the next event: no active set becomes neutral and no candidate edge
becomes tight strictly before time `Δ`. -/
def IsNextEventTime (I : Instance V) (lam : ℝ) (s : PDState V) (Δ : ℝ) : Prop :=
  (∀ S ∈ s.active, Δ ≤ neutralTime s S) ∧
    (∀ (S₁ S₂ : Finset V) (u v : V), IsEdgeCandidate I s S₁ S₂ u v →
      Δ ≤ edgeTime I lam s S₁ S₂ u v)

/-- The dual vector after raising `y_S` uniformly by `Δ` for every active set `S`. -/
def raise (s : PDState V) (Δ : ℝ) : Finset V → ℝ :=
  fun S => s.y S + if S ∈ s.active then Δ else 0

/-- One event of the primal-dual subroutine PD(λ₁) (Algorithm 1, p. 5), for the fixed value
`lam = λ₁`. The duals of all active sets are raised uniformly by the time `Δ` until the next
event, and then one event that happens at time `Δ` is processed:

* `neutral`: an active set `S` becomes neutral and is marked inactive;
* `edge`: the dual constraint of an edge `e = s(u, v)` between two different components
  `S₁ ∋ u` and `S₂ ∋ v` becomes tight; `e` is added to `T`, and `S₁`, `S₂` are replaced by the
  active component `S₁ ∪ S₂`.

When several events happen at the same time, any one of them may be processed first, and the
event times are then recomputed from the new state (an event that is no longer possible, such as
a second edge between two components that have just merged, disappears). The relation therefore
admits exactly the runs of PD(λ₁) under every order of breaking ties ("we break ties in some
order", p. 8). -/
inductive PDStep (I : Instance V) (lam : ℝ) : PDState V → PDState V → Prop
  | neutral (s : PDState V) (Δ : ℝ) (S : Finset V)
      (hΔ : IsNextEventTime I lam s Δ) (hS : S ∈ s.active) (ht : neutralTime s S = Δ) :
      PDStep I lam s
        { comps := s.comps
          active := s.active.erase S
          y := raise s Δ
          T := s.T
          everActive := s.everActive }
  | edge (s : PDState V) (Δ : ℝ) (S₁ S₂ : Finset V) (u v : V)
      (hΔ : IsNextEventTime I lam s Δ) (he : IsEdgeCandidate I s S₁ S₂ u v)
      (ht : edgeTime I lam s S₁ S₂ u v = Δ) :
      PDStep I lam s
        { comps := insert (S₁ ∪ S₂) ((s.comps.erase S₁).erase S₂)
          active := insert (S₁ ∪ S₂) ((s.active.erase S₁).erase S₂)
          y := raise s Δ
          T := insert s(u, v) s.T
          everActive := insert (S₁ ∪ S₂) s.everActive }

/-- `s` is a state of PD(λ₁) at some point of some run: it is reached from the start by
finitely many events. -/
def IsReachable (I : Instance V) (lam : ℝ) (s : PDState V) : Prop :=
  Relation.ReflTransGen (PDStep I lam) PDState.init s

/-- `s` is the final state of a complete run of PD(λ₁), under some order of breaking ties: it is
reachable and no set is active (the `while` loop of Algorithm 1 has stopped). Its dual vector
`s.y` is the `y` of Sections 4 and 5 and `s.everActive` is the laminar family `𝒮`. -/
def IsCompleteRun (I : Instance V) (lam : ℝ) (s : PDState V) : Prop :=
  IsReachable I lam s ∧ s.active = ∅

/-- `𝒮⁺ = 𝒮 ∪ {V}` (p. 6). -/
def sPlus (s : PDState V) : Finset (Finset V) :=
  insert Finset.univ s.everActive

end BudgetedPCTSP.Rooted


