-- Prove2me | Definitions.Def_DPDeconstructed_DynProg
-- name    : DPDeconstructed_DynProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:31.061986+00:00
-- url     : https://prove2.me/theorems/9945e839-5d80-4ce8-bbaf-bf6f64fa40bf
-- title:
--   Abstract dynamic program $(\mathsf X,\mathsf A,\Gamma,\mathcal V,H)$ and the Bellman operator $T$
-- statement:
--   A **dynamic program** consists of a nonempty state space $\mathsf X$, a nonempty action space $\mathsf A$, a nonempty-valued feasible correspondence $\Gamma$ from $\mathsf X$ to $\mathsf A$ with set of state-action pairs
--
--   $$\mathsf F:=\{(x,a)\in\mathsf X\times\mathsf A: a\in\Gamma(x)\},$$
--
--   a set $\mathcal V\subseteq\mathbb R^{\mathsf X}$ of candidate value functions, and a state-action aggregator $H:\mathsf F\times\mathcal V\to\mathbb R\cup\{-\infty\}$. The value $H(x,a,v)$ is the lifetime value of choosing $a$ at $x$ and continuing with the value function $v$. The **Bellman operator** is
--
--   $$Tv(x)=\sup_{a\in\Gamma(x)}H(x,a,v)\qquad(x\in\mathsf X,\ v\in\mathcal V),$$
--
--   and the Bellman equation (1) says $v=Tv$.
--
--   This is the abstract model on which every object of the mission is built; it covers finite MDPs, optimal stopping, and recursive preferences.
--
--   **Formalization Note** $\mathbb R\cup\{-\infty\}$ is encoded as `EReal` together with the requirement that $H\neq+\infty$ on $\mathsf F\times\mathcal V$. $H$ is typed on all of $\mathsf X\times\mathsf A\times\mathbb R^{\mathsf X}$, but only its values on $\mathsf F\times\mathcal V$ are ever used. $T$ takes its supremum in `EReal`. Nonemptiness of $\mathsf X$ is a hypothesis of each theorem; nonemptiness of $\mathsf A$ follows from it and nonemptiness of $\Gamma$.
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §2.1, p.4 (dynamic program) and display (2), p.5 (Bellman operator)

import Mathlib

namespace DPDeconstructed

/-- An abstract dynamic program, Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, §2.1, p.4: a state space `X`, an action space `A`, a nonempty feasible
correspondence `Γ : X ⇉ A` with state-action pairs `F := {(x, a) ∈ X × A : a ∈ Γ(x)}`, a set
`𝒱 ⊆ ℝ^X` of candidate value functions, and a state-action aggregator `H : F × 𝒱 → ℝ ∪ {−∞}`.

**Formalization Note** `ℝ ∪ {−∞}` is encoded as `EReal` together with the field `H_ne_top`
(`H` never takes the value `+∞` on `F × 𝒱`). `H` is typed on all of `X × A × ℝ^X`; only its
values on `F × 𝒱` (`a ∈ Γ x`, `v ∈ 𝒱`) enter any definition or statement of the mission.
Nonemptiness of `X` is a hypothesis of each theorem (`[Nonempty X]`); nonemptiness of `A`
follows from it and `Γ_nonempty`. -/
structure DynProg (X A : Type*) where
  /-- The feasible correspondence `Γ`. -/
  Γ : X → Set A
  /-- `Γ` is nonempty-valued. -/
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- The set `𝒱 ⊆ ℝ^X` of candidate value functions. -/
  𝒱 : Set (X → ℝ)
  /-- The state-action aggregator `H(x, a, v)`. -/
  H : X → A → (X → ℝ) → EReal
  /-- `H` takes values in `ℝ ∪ {−∞}` on `F × 𝒱`. -/
  H_ne_top : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ 𝒱, H x a v ≠ ⊤

namespace DynProg

variable {X A : Type*} (D : DynProg X A)

/-- The set of state-action pairs `F := {(x, a) ∈ X × A : a ∈ Γ(x)}`, arXiv:1811.01940v2,
§2.1, p.4, as a subtype; functions on `F` (the paper's `ℝ^F`) are `D.SA → ℝ`. -/
abbrev SA : Type _ := {p : X × A // p.2 ∈ D.Γ p.1}

/-- The Bellman operator, arXiv:1811.01940v2, display (2), p.5:
`T v(x) = sup_{a ∈ Γ(x)} H(x, a, v)`.

**Formalization Note** The supremum is taken in `EReal` (it may be `+∞`); it is the paper's
operator for `v ∈ 𝒱`, and is not used outside `𝒱`. -/
noncomputable def T (v : X → ℝ) (x : X) : EReal :=
  ⨆ a ∈ D.Γ x, D.H x a v

end DynProg

end DPDeconstructed


