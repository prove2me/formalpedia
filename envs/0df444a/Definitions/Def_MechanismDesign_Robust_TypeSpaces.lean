-- Prove2me | Definitions.Def_MechanismDesign_Robust_TypeSpaces
-- name    : MechanismDesign_Robust_TypeSpaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T04:23:43.359606+00:00
-- url     : https://prove2.me/theorems/308a9bae-5c9b-44e9-93b8-dcddaef7322a
-- title:
--   Type spaces, common priors, large variety of certainties, belief hierarchies and the space of finite types
-- statement:
--   There are finitely many agents $i \in I$. Agent $i$'s **payoff types** form a set $\Theta_i$; write $\Theta = \prod_i \Theta_i$, and for any family $(X_i)_{i\in I}$ write $X_{-i} = \prod_{j \ne i} X_j$ for the profiles of the agents other than $i$, and $(x_i, y_{-i})$ for the full profile obtained by combining agent $i$'s component with the others'.
--
--   A **type space** (Definition 10.2) is a list $\mathcal T = (T_i, \hat\theta_i, \hat\beta_i)_{i\in I}$ where every $T_i$ is a nonempty set of types, $\hat\theta_i : T_i \to \Theta_i$ gives each type its payoff type, and $\hat\beta_i : T_i \to \Delta(T_{-i})$ gives each type its belief about the other agents' types. A family $(\hat T_i)_i$ with $\hat T_i \subseteq T_i$ is **belief closed** (Definition 10.3) if every $\tau_i \in \hat T_i$ assigns probability one to $\hat T_{-i}$. A probability distribution $\mu$ on $T_1 \times \dots \times T_N$ is a **common prior** (Definition 10.4) if for every agent $i$ and type $\tau_i$ with $\mu(\tau_i) > 0$,
--
--   $$\hat\beta_i(\tau_i)(\tau_{-i}) = \frac{\mu(\tau_i, \tau_{-i})}{\mu(\tau_i)} \quad\text{for all } \tau_{-i}\in T_{-i}.$$
--
--   The conditional probability of an event $E$ given $F$ under $\mu$ is $\mu(E\mid F) = \mu(E\cap F)/\mu(F)$.
--
--   The type space has a **large variety of certainties** (Definition 10.7) if for every agent $i$, every $\theta_i \in \Theta_i$ and every $\theta_{-i} \in \Theta_{-i}$ there are types $\tau_i \in T_i$, $\tau_{-i} \in T_{-i}$ with $\hat\theta_i(\tau_i) = \theta_i$, $\hat\theta_{-i}(\tau_{-i}) = \theta_{-i}$, such that $\hat\beta_i(\tau_i)$ assigns probability one to $\{\tau_{-i} : \hat\theta_{-i}(\tau_{-i}) = \theta_{-i}\}$. It has **common certainties** if moreover, for every $i$ and $\theta_{-i}$, one belief $b$ that is certain of $\theta_{-i}$ is held by a type of every payoff type $\theta_i$; this stronger property holds in the universal type space and in the space of finite types, and it is what the proof of Proposition 10.8 in the book uses.
--
--   **Belief hierarchies** (Definition 10.1) are encoded level by level: a level-$0$ description of agent $i$ is a payoff type, and a level-$(n+1)$ description is a payoff type together with a belief about the other agents' level-$n$ descriptions. For a type $\tau_i$ of a type space, its level-$0$ description is $\hat\theta_i(\tau_i)$ and its level-$(n+1)$ description is $\hat\theta_i(\tau_i)$ together with the image of $\hat\beta_i(\tau_i)$ under the others' level-$n$ descriptions; the sequence of these is the type's infinite hierarchy of beliefs (p.173). The **space of finite types** $\mathcal T^+$ (Definition 10.6) has as agent $i$'s types the hierarchies that arise from some type of some finite type space; the payoff type of such a type is its level-$0$ component, and its belief on $T^+_{-i}$ is the image of the representing type's belief under the others' hierarchies.
--
--   These are the objects on which every statement of Chapter 10 is formulated.
--
--   **Formalization Note** $\Delta(X)$ is formalized as `PMF X`, the countably supported probability distributions on $X$: the book does not specify the measure-theoretic structure of type spaces (p.179, note 3 p.237); beliefs of finite types, of finite type spaces and point beliefs are all of this kind. The belief $\hat\beta_i(\tau_i)$ is a distribution on $\prod_{j\ne i}T_j$ (`Others T i`). The belief of a finite type in $\mathcal T^+$ is computed from a representative chosen by `Classical.choose`; it does not depend on the choice. The universal type space $\mathcal T^*$ (Definition 10.5) is not formalized; $\mathcal T^+$ is built directly from finite type spaces, which is equivalent for finite types.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.170–177, §§10.3–10.4, Definitions 10.1, 10.2, 10.3, 10.4, 10.6, 10.7; p.188 (proof of Proposition 10.8); note 3, p.237

import Mathlib

open scoped ENNReal

namespace MechanismDesign.Robust

universe u v

/-- Profiles of the agents other than `i`: an element of `X_{-i} = ∏_{j ≠ i} X_j`. -/
abbrev Others {ι : Type} (X : ι → Type u) (i : ι) : Type u := ∀ j : {j : ι // j ≠ i}, X j

/-- The profile `(x_i, y_{-i})` obtained by putting agent `i`'s component `x` together with the
components `y` of the other agents. -/
def join {ι : Type} [DecidableEq ι] {X : ι → Type u} (i : ι) (x : X i) (y : Others X i) :
    ∀ j, X j :=
  fun j => if h : j = i then h ▸ x else y ⟨j, h⟩

/-- The components of a full profile belonging to the agents other than `i`. -/
def others {ι : Type} {X : ι → Type u} (x : ∀ j, X j) (i : ι) : Others X i :=
  fun j => x j

/-- **Definition 10.2** (Börgers p.172). A type space over the payoff type sets `Θ i`: for every
agent `i` a nonempty set `T i` of types, a payoff type map `θhat i : T i → Θ i` and a belief type
map `β i : T i → Δ(T_{-i})`. Beliefs are countably supported probability distributions (`PMF`).
-/
structure TypeSpace {ι : Type} (Θ : ι → Type u) (T : ι → Type v) where
  /-- every `T i` is nonempty -/
  nonempty : ∀ i, Nonempty (T i)
  /-- the payoff type `θ̂_i(τ_i)` of a type -/
  θhat : ∀ i, T i → Θ i
  /-- the belief type `β̂_i(τ_i) ∈ Δ(T_{-i})` of a type -/
  β : ∀ i, T i → PMF (Others T i)

variable {ι : Type} [DecidableEq ι] {Θ : ι → Type u} {T : ι → Type v}

/-- The payoff type profile `θ̂(τ) = (θ̂_1(τ_1), …, θ̂_N(τ_N))` of a type profile. -/
def TypeSpace.payoff (ts : TypeSpace Θ T) (τ : ∀ i, T i) : ∀ i, Θ i :=
  fun i => ts.θhat i (τ i)

/-- The belief type profile `β̂(τ) = (β̂_1(τ_1), …, β̂_N(τ_N))` of a type profile. -/
def TypeSpace.beliefs (ts : TypeSpace Θ T) (τ : ∀ i, T i) : ∀ i, PMF (Others T i) :=
  fun i => ts.β i (τ i)

/-- **Definition 10.3** (p.173). `(T̂_i)_i` with `T̂_i ⊆ T_i` is a belief closed subset if every
type in `T̂_i` assigns probability one to `T̂_{-i}`. -/
def TypeSpace.IsBeliefClosed (ts : TypeSpace Θ T) (That : ∀ i, Set (T i)) : Prop :=
  ∀ i, ∀ τi ∈ That i, (ts.β i τi).toOuterMeasure {τo | ∀ j : {j : ι // j ≠ i}, τo j ∈ That j} = 1

/-- **Definition 10.4** (p.173). `μ` is a common prior of the type space: whenever the type `τ_i`
has positive prior probability, its belief `β̂_i(τ_i)` is the conditional distribution of
`τ_{-i}` given `τ_i` under `μ`. -/
def TypeSpace.IsCommonPrior (ts : TypeSpace Θ T) (μ : PMF (∀ i, T i)) : Prop :=
  ∀ i (τi : T i), μ.toOuterMeasure {τ | τ i = τi} ≠ 0 →
    ∀ τo : Others T i, ts.β i τi τo = μ (join i τi τo) / μ.toOuterMeasure {τ | τ i = τi}

/-- The conditional probability `μ(E | F) = μ(E ∩ F) / μ(F)` of an event under a discrete
distribution (in `ℝ≥0∞`). -/
noncomputable def condProb {α : Type*} (μ : PMF α) (E F : Set α) : ℝ≥0∞ :=
  μ.toOuterMeasure (E ∩ F) / μ.toOuterMeasure F

/-- **Definition 10.7** (p.177). The type space has a large variety of certainties: for every
agent `i`, every payoff type `θ_i` and every payoff type profile `θ_{-i}` of the others, there are
types `τ_i`, `τ_{-i}` with `θ̂_i(τ_i) = θ_i` such that `β̂_i(τ_i)` assigns probability one to
`{τ_{-i} : θ̂_{-i}(τ_{-i}) = θ_{-i}}` (and `τ_{-i}` lies in that set). -/
def TypeSpace.HasLargeVarietyOfCertainties (ts : TypeSpace Θ T) : Prop :=
  ∀ i (θi : Θ i) (θo : Others Θ i), ∃ (τi : T i) (τo : Others T i),
    ts.θhat i τi = θi ∧ (∀ j : {j : ι // j ≠ i}, ts.θhat j (τo j) = θo j) ∧
      (ts.β i τi).toOuterMeasure {τo' | ∀ j : {j : ι // j ≠ i}, ts.θhat j (τo' j) = θo j} = 1

/-- A strengthening of Definition 10.7 used for the corrected Proposition 10.9 (see the mission's
notes): for every agent `i` and payoff type profile `θ_{-i}` there is one belief `b`, certain
that the others' payoff types are `θ_{-i}`, that is held by a type of *every* payoff type `θ_i`.
The universal type space and the space of finite types have this property. -/
def TypeSpace.HasCommonCertainties (ts : TypeSpace Θ T) : Prop :=
  ∀ i (θo : Others Θ i), ∃ b : PMF (Others T i),
    b.toOuterMeasure {τo | ∀ j : {j : ι // j ≠ i}, ts.θhat j (τo j) = θo j} = 1 ∧
      ∀ θi : Θ i, ∃ τi : T i, ts.θhat i τi = θi ∧ ts.β i τi = b

/-! ### Belief hierarchies and the space of finite types (Definitions 10.1 and 10.6) -/

/-- The `n`-th level of belief hierarchies (Definition 10.1, pp.170–171), in the recursive encoding
`L_0 i = Θ_i`, `L_{n+1} i = Θ_i × Δ(∏_{j ≠ i} L_n j)`: a level-`(n+1)` description of agent `i`
is her payoff type together with her belief about the others' level-`n` descriptions. Beliefs of
finite types are finitely supported, so `Δ` is taken to be `PMF`. -/
def Level (Θ : ι → Type u) : ℕ → ι → Type u
  | 0 => Θ
  | n + 1 => fun i => Θ i × PMF (Others (Level Θ n) i)

/-- The level-`n` belief hierarchy `b̂_{i,n}(τ_i)` of a type in a type space (p.173): level `0` is
the payoff type; level `n+1` is the payoff type and the image of the belief `β̂_i(τ_i)` under the
others' level-`n` hierarchies. -/
noncomputable def hier (ts : TypeSpace Θ T) : (n : ℕ) → (i : ι) → T i → Level Θ n i
  | 0 => fun i τ => ts.θhat i τ
  | n + 1 => fun i τ => (ts.θhat i τ, (ts.β i τ).map (fun τo j => hier ts n j (τo j)))

/-- A finite type space (all `T j` finite) in the universe of the payoff types, together with a
type of agent `i` in it. -/
structure FiniteRep (Θ : ι → Type u) (i : ι) where
  /-- the type sets -/
  T : ι → Type u
  /-- they are finite -/
  fin : ∀ j, Fintype (T j)
  /-- the type space -/
  ts : TypeSpace Θ T
  /-- a type of agent `i` -/
  τ : T i

/-- The infinite hierarchy of beliefs of `i` arises from some type of some finite type space. -/
def IsFiniteHierarchy (Θ : ι → Type u) (i : ι) (h : ∀ n, Level Θ n i) : Prop :=
  ∃ r : FiniteRep Θ i, ∀ n, hier r.ts n i r.τ = h n

/-- **Definition 10.6** (p.177), types: `T⁺_i` is the set of infinite belief hierarchies of agent
`i` (including her payoff type at level `0`) that arise from a type in a finite type space. -/
def TPlusType (Θ : ι → Type u) (i : ι) : Type u :=
  {h : ∀ n, Level Θ n i // IsFiniteHierarchy Θ i h}

/-- The belief of a finite type on `T⁺_{-i}`: take any finite type space and type representing
the hierarchy, and push its belief forward along the others' hierarchies. (The result does not
depend on the representative; this is the belief `β̂*_i` of the universal type space restricted
to finite types.) -/
noncomputable def βPlus (Θ : ι → Type u) (i : ι) (h : TPlusType Θ i) : PMF (Others (TPlusType Θ) i) :=
  let r := Classical.choose h.2
  (r.ts.β i r.τ).map (fun τo j =>
    ⟨fun n => hier r.ts n j (τo j), ⟨⟨r.T, r.fin, r.ts, τo j⟩, fun _ => rfl⟩⟩)

/-- The one-type-per-agent type space in which a fixed payoff type profile is common certainty. -/
noncomputable def unitTypeSpace (θ : ∀ i, Θ i) : TypeSpace Θ (fun _ : ι => PUnit.{u + 1}) where
  nonempty := fun _ => ⟨PUnit.unit⟩
  θhat := fun i _ => θ i
  β := fun _ _ => PMF.pure (fun _ => PUnit.unit)

/-- **Definition 10.6** (p.177). The space of finite types `T⁺ = (T⁺_i, θ̂⁺_i, β̂⁺_i)`: payoff type
the level-`0` component, beliefs `βPlus`. -/
noncomputable def TPlus (Θ : ι → Type u) [∀ i, Nonempty (Θ i)] : TypeSpace Θ (TPlusType Θ) where
  nonempty := fun i =>
    let θ : ∀ j, Θ j := fun j => Classical.arbitrary (Θ j)
    ⟨⟨fun n => hier (unitTypeSpace θ) n i PUnit.unit,
      ⟨⟨fun _ => PUnit, fun _ => inferInstance, unitTypeSpace θ, PUnit.unit⟩, fun _ => rfl⟩⟩⟩
  θhat := fun i h => (h.1 0 : Θ i)
  β := fun i h => βPlus Θ i h

end MechanismDesign.Robust


