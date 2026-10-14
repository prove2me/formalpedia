-- Prove2me | Definitions.Def_SourceTheory_Uniform_Model
-- name    : SourceTheory_Uniform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:20.441756+00:00
-- url     : https://prove2.me/theorems/b24da1ca-3f1d-450a-ba18-1c393f203bb4
-- title:
--   §3–§4 and Assumption 1, pp. 8769–8774 — Savage acts, biseparable utility, sources, uniformity, source preference (Def. 2) and insensitivity (Def. 4)
-- statement:
--   This module sets up the decision-theoretic model of Baillon, Bleichrodt, Li and Wakker, *Source Theory* (Management Science, 2025), §3–§4 and §5.2–§7.
--
--   **States, events, acts.** $S$ is a state space, $\Gamma$ an outcome set, and the events are the members of an algebra $\mathcal E$ of subsets of $S$ (endnote 1; the power set is the case $\mathcal E = 2^S$). An *act from* an algebra $\mathcal A$ is a finite-valued map $x : S \to \Gamma$ whose level sets $x^{-1}(\alpha)$ all lie in $\mathcal A$. The binary act $\gamma E \beta$ yields $\gamma$ on $E$ and $\beta$ on $E^c$. A preference $\succcurlyeq$ is a binary relation on acts; an event $E$ is *null* if any two acts that agree outside $E$ are indifferent.
--
--   **Structural Assumption 1** (p. 8771) bundles: $\succcurlyeq$ is a weak order on acts; a *weighting function* $W$ with $W(\emptyset)=0$, $W(S)=1$, monotone on events; a utility $U : \Gamma \to \mathbb R$ ranking constant acts; at least three nonindifferent outcomes; *biseparable utility*, i.e. for $\gamma \succcurlyeq \beta$ and $\gamma' \succcurlyeq \beta'$,
--   $$\gamma E\beta \succcurlyeq \gamma' F \beta' \iff W(E)U(\gamma)+(1-W(E))U(\beta) \ge W(F)U(\gamma')+(1-W(F))U(\beta');$$
--   *convex rangedness* of $W$ (for events $A \subseteq C$ and $W(A)\le\mu\le W(C)$ there is an event $B$ with $A\subseteq B\subseteq C$ and $W(B)=\mu$); *strong monotonicity* (strictly improving the outcome of an act on a nonnull event strictly improves the act); *cumulative dominance* (4): if $W\{x \succcurlyeq \alpha\} \ge W\{y \succcurlyeq\alpha\}$ for all outcomes $\alpha$ then $x \succcurlyeq y$; and the *Archimedean axiom*: no infinite sequence of disjoint nonnull events of equal weight.
--
--   **Sources and uniformity.** A *source* $\mathcal S$ is a subalgebra of $\mathcal E$ on which $W$ is convex ranged. A *probability measure* on $\mathcal S$ is a finitely additive, nonnegative $P$ with $P(S)=1$. $\mathcal S$ is *uniform* (source theory holds, Definition 1) if for some probability measure $P$ on $\mathcal S$ stochastic dominance (2) holds for all acts $x,y$ from $\mathcal S$:
--   $$\bigl[\forall \alpha\in\Gamma:\ P(x\succcurlyeq\alpha)\ge P(y\succcurlyeq\alpha)\bigr]\ \Longrightarrow\ x\succcurlyeq y.$$
--   A *probability weighting function* is a strictly increasing $w:[0,1]\to[0,1]$ with $w(0)=0$, $w(1)=1$; a *transformation* is a continuous one; $w$ is a *source function* of $\mathcal S$ w.r.t. $P$ if moreover $W = w\circ P$ on $\mathcal S$ (5).
--
--   **Comparisons of sources** (events are ranked by $W$). $\mathcal C$ is *preferred* to $\mathcal A$ (Definition 2, (6)) if for all $C_1\in\mathcal C$, $A_1\in\mathcal A$: $W(A_1)=W(C_1)\Rightarrow W(A_1^c)\le W(C_1^c)$. For events $B, D$, $\mathcal A$ is *more insensitive* than $\mathcal C$ with insensitivity region $[B,D]$ (Definition 4) if for all ordered threefold partitions $(C_1,C_2,C_3)$ of $S$ from $\mathcal C$ and $(A_1,A_2,A_3)$ from $\mathcal A$ (cells may be empty):
--   $$W(A_1)=W(C_1)\ \&\ W(A_3^c)=W(C_3^c)\le W(D)\Rightarrow W(A_2)\ge W(C_2) \quad (8)$$
--   $$W(B)\le W(A_1)=W(C_1)\ \&\ W(A_3^c)=W(C_3^c)\Rightarrow W(A_2^c)\le W(C_2^c). \quad (9)$$
--   The region $[B,D]$ is *regular* for $\mathcal S$ (p. 8774) if every fourfold partition $(E_1,\dots,E_4)$ of $S$ from $\mathcal S$ has a cell with $W(E_j)\ge W(B)$ and $W(E_j^c)\le W(D)$. The module also defines Assumption 2, disliked and insensitive weighting functions ((13)–(14)), used by the companion missions.
--
--   These are the objects all four missions on this paper are stated in.
--
--   **Formalization Note** Event preference $A\succcurlyeq B$ is encoded as $W(A)\ge W(B)$, as Assumption 1 prescribes ("to events via bets on them, maximizing $W$"). Assumption 1's "W is convex ranged for every source" is split: convex rangedness on all events is a field of `Assumption1`, and each source carries its own convex rangedness in `IsSource` (the paper's "we only consider rich infinite sources", p. 8770); requiring it of every subalgebra would be unsatisfiable, since $\{\emptyset,S\}$ has no event of weight $1/2$. Twofold partitions $(A_1,A_2)$ are written $(A_1,A_1^c)$. A null event is defined by acts from $\mathcal E$, and strong monotonicity improves the outcome on any nonnull event on which the act is constant. A *transformation* (a word the paper leaves undefined) is read as a continuous probability weighting function, the properties (18) attributes to the pmatcher. In the insensitivity of a weighting function the endpoints $b, d$ are arbitrary reals: the page's parenthetical $0 \le b < d \le 1$ is not imposed, a disclosed generalization, since Theorem 3's region $[P_{\mathcal A}(B), P_{\mathcal A}(D)]$ need not satisfy it. A probability measure on a source and the weighting function $W$ are total functions on all subsets of $S$; only their values on the source, respectively on $\mathcal E$, carry meaning, and every statement of the series quantifies only over such events.
-- source:
--   Baillon et al. (2025), Management Science 71(10), §3–§4, Assumption 1, Definitions 1, 2, 4, regularity, pp. 8769–8774; endnotes 1–2, p. 8780

import Mathlib

namespace SourceTheory.Uniform

open Set MeasureTheory

/-- An act from the algebra `𝓐` (Baillon et al. 2025, §3, p. 8769; §4, p. 8770): a finite-valued map
`S → Γ` whose level sets `x⁻¹(α)` all belong to `𝓐` ("measurable w.r.t. that source"). -/
def IsActFrom {S Γ : Type*} (𝓐 : Set (Set S)) (x : S → Γ) : Prop :=
  (Set.range x).Finite ∧ ∀ α : Γ, x ⁻¹' {α} ∈ 𝓐

open Classical in
/-- The binary act `γEβ = (E : γ, Eᶜ : β)` (§3, p. 8769). -/
noncomputable def bet {S Γ : Type*} (γ : Γ) (E : Set S) (β : Γ) : S → Γ :=
  fun s => if s ∈ E then γ else β

open Classical in
/-- The act `x` with its outcome on the event `E` replaced by `β`. -/
noncomputable def replaceOn {S Γ : Type*} (x : S → Γ) (E : Set S) (β : Γ) : S → Γ :=
  fun s => if s ∈ E then β else x s

/-- A null event (§3, p. 8769): its outcomes never affect preference, i.e. any two acts that agree
outside `E` are indifferent. -/
def IsNull {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop) (E : Set S) : Prop :=
  ∀ x y : S → Γ, IsActFrom 𝓔 x → IsActFrom 𝓔 y → (∀ s, s ∉ E → x s = y s) → pref x y ∧ pref y x

/-- Convex rangedness of `W` on `𝓐` (p. 8770): for `A ⊆ C` in `𝓐` and `W(A) ≤ μ ≤ W(C)` there is
`B ∈ 𝓐` with `A ⊆ B ⊆ C` and `W(B) = μ`. -/
def IsConvexRanged {S : Type*} (𝓐 : Set (Set S)) (W : Set S → ℝ) : Prop :=
  ∀ A ∈ 𝓐, ∀ C ∈ 𝓐, A ⊆ C → ∀ μ : ℝ, W A ≤ μ → μ ≤ W C →
    ∃ B ∈ 𝓐, A ⊆ B ∧ B ⊆ C ∧ W B = μ

/-- Structural Assumption 1 (p. 8771), with the definitions of §3 (pp. 8769–8770) it uses. Events are
the members of the algebra `𝓔` (endnote 1, p. 8780); `pref x y` is `x ≽ y` on acts; outcomes are
ranked by `U` through constant acts and events by `W` through bets. Convex rangedness is imposed on all
events here and on each source by `IsSource`. -/
structure Assumption1 {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) : Prop where
  events : IsSetAlgebra 𝓔
  weakOrder_total : ∀ x y : S → Γ, IsActFrom 𝓔 x → IsActFrom 𝓔 y → pref x y ∨ pref y x
  weakOrder_trans : ∀ x y z : S → Γ, IsActFrom 𝓔 x → IsActFrom 𝓔 y → IsActFrom 𝓔 z →
    pref x y → pref y z → pref x z
  W_empty : W ∅ = 0
  W_univ : W univ = 1
  W_mono : ∀ A ∈ 𝓔, ∀ B ∈ 𝓔, B ⊆ A → W B ≤ W A
  utility : ∀ α β : Γ, pref (fun _ => α) (fun _ => β) ↔ U β ≤ U α
  three_outcomes : ∃ α β γ : Γ, U β < U α ∧ U γ < U β
  biseparable : ∀ γ β γ' β' : Γ, ∀ E ∈ 𝓔, ∀ F ∈ 𝓔, U β ≤ U γ → U β' ≤ U γ' →
    (pref (bet γ E β) (bet γ' F β') ↔
      W F * U γ' + (1 - W F) * U β' ≤ W E * U γ + (1 - W E) * U β)
  convexRanged : IsConvexRanged 𝓔 W
  strongMonotone : ∀ x : S → Γ, IsActFrom 𝓔 x → ∀ E ∈ 𝓔, ¬ IsNull 𝓔 pref E →
    ∀ α β : Γ, (∀ s ∈ E, x s = α) → U α < U β →
      pref (replaceOn x E β) x ∧ ¬ pref x (replaceOn x E β)
  cumulativeDominance : ∀ x y : S → Γ, IsActFrom 𝓔 x → IsActFrom 𝓔 y →
    (∀ α : Γ, W {s | U α ≤ U (y s)} ≤ W {s | U α ≤ U (x s)}) → pref x y
  archimedean : ¬ ∃ E : ℕ → Set S, (∀ i, E i ∈ 𝓔) ∧ Pairwise (fun i j => Disjoint (E i) (E j)) ∧
    (∀ i, ¬ IsNull 𝓔 pref (E i)) ∧ ∀ i j, W (E i) = W (E j)

/-- A source (§4, p. 8770; Assumption 1): a subalgebra of the events on which `W` is convex ranged
("we only consider 'rich' infinite sources"). -/
structure IsSource {S : Type*} (𝓔 : Set (Set S)) (W : Set S → ℝ) (𝒮 : Set (Set S)) : Prop where
  algebra : IsSetAlgebra 𝒮
  subset : 𝒮 ⊆ 𝓔
  convexRanged : IsConvexRanged 𝒮 W

/-- A probability measure on the source `𝒮` (§3, p. 8769): an additive weighting function;
countable additivity is not imposed. -/
def IsProbOn {S : Type*} (𝒮 : Set (Set S)) (P : Set S → ℝ) : Prop :=
  P univ = 1 ∧ (∀ E ∈ 𝒮, 0 ≤ P E) ∧
    ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, Disjoint E F → P (E ∪ F) = P E + P F

/-- `𝒮` is uniform with a-neutral probability measure `P` (§4, p. 8770): `P` is a probability
measure on `𝒮` and stochastic dominance (2) holds with `P` for all acts from `𝒮`. -/
def IsUniformWith {S Γ : Type*} (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ)
    (𝒮 : Set (Set S)) (P : Set S → ℝ) : Prop :=
  IsProbOn 𝒮 P ∧ ∀ x y : S → Γ, IsActFrom 𝒮 x → IsActFrom 𝒮 y →
    (∀ α : Γ, P {s | U α ≤ U (y s)} ≤ P {s | U α ≤ U (x s)}) → pref x y

/-- Source theory holds for `𝒮` (Definition 1, p. 8770): biseparable utility (part of
`Assumption1`) and `𝒮` is uniform. -/
def IsUniform {S Γ : Type*} (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ)
    (𝒮 : Set (Set S)) : Prop :=
  ∃ P : Set S → ℝ, IsUniformWith pref U 𝒮 P

/-- A probability weighting function (p. 8770): `w : [0,1] → [0,1]`, strictly increasing,
`w(0) = 0`, `w(1) = 1`. -/
def IsProbWeighting (w : ℝ → ℝ) : Prop :=
  MapsTo w (Icc 0 1) (Icc 0 1) ∧ StrictMonoOn w (Icc 0 1) ∧ w 0 = 0 ∧ w 1 = 1

/-- A transformation of probabilities (Theorems 2 and 3, p. 8775): a continuous probability
weighting function, the properties (18) gives the pmatcher. -/
def IsTransformation (φ : ℝ → ℝ) : Prop :=
  IsProbWeighting φ ∧ ContinuousOn φ (Icc 0 1)

/-- `w` is the source function of `𝒮` with respect to `P` (5), p. 8771: a continuous probability
weighting function with `W = w ∘ P` on `𝒮`. -/
def IsSourceFunction {S : Type*} (W : Set S → ℝ) (𝒮 : Set (Set S)) (P : Set S → ℝ)
    (w : ℝ → ℝ) : Prop :=
  IsTransformation w ∧ ∀ E ∈ 𝒮, W E = w (P E)

/-- Assumption 2 (p. 8774): source theory holds for `𝒞` and `𝒜`, with a-neutral probability
measures `PC`, `PA` and source functions `wC`, `wA`. -/
def Assumption2 {S Γ : Type*} (pref : (S → Γ) → (S → Γ) → Prop) (U : Γ → ℝ) (W : Set S → ℝ)
    (𝒞 𝒜 : Set (Set S)) (PC PA : Set S → ℝ) (wC wA : ℝ → ℝ) : Prop :=
  IsUniformWith pref U 𝒞 PC ∧ IsUniformWith pref U 𝒜 PA ∧
    IsSourceFunction W 𝒞 PC wC ∧ IsSourceFunction W 𝒜 PA wA

/-- An ordered threefold partition `(A₁, A₂, A₃)` of `S` from `𝒮` (endnote 2); cells may be empty. -/
def IsPartition3 {S : Type*} (𝒮 : Set (Set S)) (A₁ A₂ A₃ : Set S) : Prop :=
  A₁ ∈ 𝒮 ∧ A₂ ∈ 𝒮 ∧ A₃ ∈ 𝒮 ∧ Disjoint A₁ A₂ ∧ Disjoint A₁ A₃ ∧ Disjoint A₂ A₃ ∧
    A₁ ∪ A₂ ∪ A₃ = univ

/-- Definition 2 (p. 8771), (6): `𝒞` is preferred to `𝒜` — for all twofold partitions `(C₁, C₂)`
from `𝒞` and `(A₁, A₂)` from `𝒜`, `W(A₁) = W(C₁) ⇒ W(A₂) ≤ W(C₂)`; here `C₂ = C₁ᶜ`, `A₂ = A₁ᶜ`. -/
def IsPreferredTo {S : Type*} (W : Set S → ℝ) (𝒞 𝒜 : Set (Set S)) : Prop :=
  ∀ C₁ ∈ 𝒞, ∀ A₁ ∈ 𝒜, W A₁ = W C₁ → W (A₁ᶜ) ≤ W (C₁ᶜ)

/-- Definition 4 (p. 8772), (8)–(9): `𝒜` is more insensitive than `𝒞` with insensitivity region
`[B, D]`. -/
def IsMoreInsensitive {S : Type*} (W : Set S → ℝ) (𝒜 𝒞 : Set (Set S)) (B D : Set S) : Prop :=
  ∀ C₁ C₂ C₃ A₁ A₂ A₃ : Set S, IsPartition3 𝒞 C₁ C₂ C₃ → IsPartition3 𝒜 A₁ A₂ A₃ →
    (W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (C₃ᶜ) ≤ W D → W C₂ ≤ W A₂) ∧
    (W B ≤ W A₁ → W A₁ = W C₁ → W (A₃ᶜ) = W (C₃ᶜ) → W (A₂ᶜ) ≤ W (C₂ᶜ))

/-- A regular insensitivity region for `𝒮` (p. 8774): every fourfold partition `(E₁, …, E₄)` of `S`
from `𝒮` has a cell with `Eⱼ ≽ B` and `Eⱼᶜ ≼ D`. -/
def IsRegularRegion {S : Type*} (W : Set S → ℝ) (𝒮 : Set (Set S)) (B D : Set S) : Prop :=
  ∀ E : Fin 4 → Set S, (∀ j, E j ∈ 𝒮) → Pairwise (fun i j => Disjoint (E i) (E j)) →
    (⋃ j, E j) = univ → ∃ j, W B ≤ W (E j) ∧ W ((E j)ᶜ) ≤ W D

/-- A disliked weighting function (p. 8773): `w(p) ≤ 1 − w(1 − p)` for all `p ∈ [0,1]`. -/
def IsDisliked (w : ℝ → ℝ) : Prop :=
  ∀ p ∈ Icc (0 : ℝ) 1, w p ≤ 1 - w (1 - p)

/-- An insensitive weighting function with insensitivity region `[b, d]` (13)–(14), pp. 8773–8774:
for all probabilities `p₁, p₂, p₃` summing to 1. -/
def IsInsensitive (w : ℝ → ℝ) (b d : ℝ) : Prop :=
  ∀ p₁ p₂ p₃ : ℝ, 0 ≤ p₁ → 0 ≤ p₂ → 0 ≤ p₃ → p₁ + p₂ + p₃ = 1 →
    (p₁ + p₂ ≤ d → w (p₁ + p₂) - w p₁ ≤ w p₂) ∧
    (b ≤ p₁ → w (p₁ + p₂) - w p₁ ≤ 1 - w (p₁ + p₃))

end SourceTheory.Uniform


