-- Prove2me | Definitions.Def_PulseSyncLowerBound_Pulse_Views
-- name    : PulseSyncLowerBound_Pulse_Views
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:45.303445+00:00
-- url     : https://prove2.me/theorems/1ca60a24-e826-49a0-bd04-44235d123625
-- title:
--   Full-information views, round complexes, prefix and suffix
-- statement:
--   A zero-round view is a local state. A later view stores the previous local view and the identity-indexed set of received previous views. The state map $\mu$ recursively applies the actual protocol transition, and the view output is the output of that computed state.
--
--   The failure operator removes at most $k$ processes. In a round with survivor configuration $\tau\subseteq\rho$, each survivor independently receives a set between $\tau$ and $\rho$. Reachability iterates precisely this rule from every full initial configuration, with at most $k$ newly crashed identities per round. The round complex $R(r,k)$ is the nonempty downward closure of these reachable configurations.
--
--   The prefix removes the final round. The suffix collapses the first round to its resulting state and recursively transforms both local and received views. Neither map is assumed simplicial. Finite traces constrain only the specified horizon; a function on natural indices harmlessly supplies unused later entries.
--
--   These objects preserve the operational crash semantics and include every crash-free execution window. No unused ambient view acquires a singleton face.
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; §5.3; failure and round operators, views and executions; PDF p.18–19 / printed p.16–17; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Model
import Definitions.Def_PulseSyncLowerBound_Pulse_Topology

noncomputable section

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {O : Type}

/-- §5.3: a local history retains its previous view and the identity-indexed
received-view set. The index is external and never an input of Γ. -/
def View (P : Protocol n O) : ℕ → Fin n → Type
  | 0, i => P.State i
  | r + 1, i => View P r i × ((j : Fin n) → Option (View P r j))

instance viewFintype (P : Protocol n O) (r : ℕ) (i : Fin n) : Fintype (View P r i) := by
  induction r generalizing i with
  | zero => exact P.finiteState i
  | succ r ih =>
    letI : ∀ j, Fintype (View P r j) := ih
    exact inferInstanceAs (Fintype (View P r i × ((j : Fin n) → Option (View P r j))))

/-- μ recursively simulates the original protocol. -/
def viewState (P : Protocol n O) : (r : ℕ) → (i : Fin n) → View P r i → P.State i
  | 0, _, v => v
  | r + 1, i, v => P.transition i (fun j => (v.2 j).map (viewState P r j))

def viewOutput (P : Protocol n O) (r : ℕ) (v : (i : Fin n) × View P r i) : O :=
  P.output v.1 (viewState P r v.1 v.2)

abbrev ViewConfig (P : Protocol n O) (r : ℕ) := (i : Fin n) → Option (View P r i)
abbrev TaggedView (P : Protocol n O) (r : ℕ) := (i : Fin n) × View P r i

/-- F_k: remove at most k processes. -/
def Failure {V : Type} (k : ℕ) (ρ : Finset V) : Set (Finset V) :=
  {τ | τ ⊆ ρ ∧ (ρ \ τ).card ≤ k}

/-- The interval of permitted received-view sets in the round operator. -/
def Between {V : Type} (τ ρ : Finset V) : Set (Finset V) := {M | τ ⊆ M ∧ M ⊆ ρ}

/-- R_k(ρ), before taking nonempty downward closure. The surviving identity
set is τ; each recipient independently chooses a set between τ and ρ. -/
def RoundOperator {V : Type} (k : ℕ) (ρ : Finset V) : Set (Finset (V × Finset V)) :=
  {η | ∃ τ ∈ Failure k ρ, ∃ g : V → Finset V,
    (∀ v ∈ τ, g v ∈ Between τ ρ) ∧ η = τ.image (fun v => (v, g v))}

/-- Identity-indexed presentation of precisely one synchronous round.
The source's nonempty generated faces will be taken after reachability. -/
def ViewRound (P : Protocol n O) {r : ℕ} (a : ViewConfig P r)
    (b : ViewConfig P (r + 1)) : Prop :=
  ∀ i v, b i = some v → a i = some v.1 ∧
    (∀ j, v.2 j = none ∨ v.2 j = a j) ∧
    (∀ j, b j ≠ none → v.2 j = a j)

def NewCrashes (P : Protocol n O) {r : ℕ} (a : ViewConfig P r)
    (b : ViewConfig P (r + 1)) : ℕ :=
  (Finset.univ.filter (fun i => a i ≠ none ∧ b i = none)).card

/-- All full initial configurations, with at most k crashes in each round. -/
inductive Reachable (P : Protocol n O) (k : ℕ) : (r : ℕ) → ViewConfig P r → Prop
  | initial (a : ViewConfig P 0) (h : ∀ i, ∃ s, a i = some s) : Reachable P k 0 a
  | next {r : ℕ} (a : ViewConfig P r) (b : ViewConfig P (r + 1))
      (h : Reachable P k r a) (step : ViewRound P a b) (budget : NewCrashes P a b ≤ k) :
      Reachable P k (r + 1) b

/-- §5.3: the nonempty downward closure of the reachable configurations.
Unreachable views are not made vertices by an ambient singleton convention. -/
def RoundComplex (P : Protocol n O) (r k : ℕ) : Set (Finset (TaggedView P r)) :=
  {s | s.Nonempty ∧ ∃ a : ViewConfig P r, Reachable P k r a ∧
    ∀ v ∈ s, a v.1 = some v.2}

/-- Prefix keeps the previous view. -/
def viewPrefix (P : Protocol n O) (r : ℕ) (v : TaggedView P (r + 1)) : TaggedView P r :=
  ⟨v.1, v.2.1⟩

/-- Suffix collapses the first round into its resulting state, recursively
in both the local view and every received message. -/
def localSuffix (P : Protocol n O) : (r : ℕ) → (i : Fin n) → View P (r + 1) i → View P r i
  | 0, i, v => viewState P 1 i v
  | r + 1, i, v => (localSuffix P r i v.1, fun j => (v.2 j).map (localSuffix P r j))

def viewSuffix (P : Protocol n O) (r : ℕ) (v : TaggedView P (r + 1)) : TaggedView P r :=
  ⟨v.1, localSuffix P r v.1 v.2⟩

def prefixConfig (P : Protocol n O) (r : ℕ) (a : ViewConfig P (r + 1)) : ViewConfig P r :=
  fun i => (a i).map Prod.fst

def suffixConfig (P : Protocol n O) (r : ℕ) (a : ViewConfig P (r + 1)) : ViewConfig P r :=
  fun i => (a i).map (localSuffix P r i)

def stateConfig (P : Protocol n O) (r : ℕ) (a : ViewConfig P r) : Configuration P :=
  fun i => (a i).map (viewState P r i)

/-- A finite execution prefix. The sequence is harmlessly extended after h;
only times ≤h and transitions before h are constrained or observed. -/
def IsViewTrace (P : Protocol n O) (h : ℕ) (a : (r : ℕ) → ViewConfig P r) : Prop :=
  (∀ i, ∃ s, a 0 i = some s) ∧ ∀ r, r < h → ViewRound P (a r) (a (r + 1))

def CrashFreeTrace (P : Protocol n O) (h : ℕ) (a : (r : ℕ) → ViewConfig P r) : Prop :=
  IsViewTrace P h a ∧ ∀ r, r ≤ h → ∀ i, a r i ≠ none

end PulseSyncLowerBound.Pulse


