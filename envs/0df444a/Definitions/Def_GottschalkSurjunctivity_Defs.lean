-- Prove2me | Definitions.Def_GottschalkSurjunctivity_Defs
-- name    : GottschalkSurjunctivity_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T14:04:11.667989+00:00
-- url     : https://prove2.me/theorems/b9413e7e-7fdf-4c54-8d30-595cec09dc80
-- title:
--   Shifts, cellular automata, surjunctive, residually finite and sofic groups
-- statement:
--   Let $G$ be a group and $A$ a set. For $g \in G$ and a configuration $x : G \to A$, the **left shift** is
--   $$(g\cdot x)(h) = x(g^{-1}h), \qquad h \in G.$$
--   It satisfies $1\cdot x = x$ and $(g_1g_2)\cdot x = g_1\cdot(g_2\cdot x)$.
--
--   1. A map $\tau : A^G \to A^G$ is **shift-equivariant** if $\tau(g\cdot x) = g\cdot\tau(x)$ for all $g\in G$, $x \in A^G$.
--   2. A map $\tau : A^G \to A^G$ is a **cellular automaton** if there are a finite set $S \subseteq G$ (memory set) and a map $\mu : A^S \to A$ (local rule) with $\tau(x)(g) = \mu(s \mapsto x(gs))$ for all $x$ and $g$.
--   3. $G$ is **surjunctive** if for every finite nonempty set $A$ with the discrete topology, every continuous, shift-equivariant, injective $\tau : A^G \to A^G$ (product topology on $A^G$) is surjective.
--   4. $G$ is **residually finite** if for every $g \neq 1$ there is a normal subgroup $N$ of finite index with $g \notin N$.
--   5. $G$ is **sofic** if for every finite $K \subseteq G$ and every $\varepsilon > 0$ there are a finite nonempty set $X$ and a map $\sigma : G \to \mathrm{Sym}(X)$ with
--   $$\#\{x : \sigma_{gh}(x) = \sigma_g(\sigma_h(x))\} \ge (1-\varepsilon)\,|X| \quad (g,h \in K),$$
--   $$\#\{x : \sigma_g(x) \ne x\} \ge (1-\varepsilon)\,|X| \quad (g \in K,\ g \neq 1).$$
--
--   These are the basic notions of Gottschalk's surjunctivity problem and of the known sufficient conditions for surjunctivity.
--
--   **Formalization Note** The shift is a plain function rather than a `MulAction` instance, to avoid a clash with Mathlib's pointwise action on function types. In `IsSurjunctive` the alphabet is a type in universe 0 with a `Fintype` structure and an arbitrary topology assumed discrete.
-- source:
--   Formal Conjectures project, file `SurjunctiveGroup.lean` (Gottschalk's surjunctivity conjecture); W. H. Gottschalk, Some general dynamical notions, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728; residual finiteness and soficity as in T. Ceccherini-Silberstein, M. Coornaert, Cellular Automata and Groups, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1 (Chapters 2 and 7); B. Weiss, Sofic groups and dynamical systems, Sankhya Ser. A 62 (2000)

import Mathlib

namespace GottschalkSurjunctivity

variable (G : Type*) [Group G]

/-- The left shift of `x : G → A` by `g : G`, defined by `(shift g x)(h) = x(g⁻¹ * h)`. -/
def shift {A : Type*} (g : G) (x : G → A) : G → A :=
  fun h => x (g⁻¹ * h)

@[simp]
theorem shift_apply {A : Type*} (g : G) (x : G → A) (h : G) :
    shift G g x h = x (g⁻¹ * h) := rfl

@[simp]
theorem shift_one {A : Type*} (x : G → A) :
    shift G 1 x = x := by
  ext h; simp [shift]

theorem shift_mul {A : Type*} (g₁ g₂ : G) (x : G → A) :
    shift G (g₁ * g₂) x = shift G g₁ (shift G g₂ x) := by
  ext h; simp [shift, mul_assoc]

/-- A map `τ : (G → A) → (G → A)` is shift-equivariant if
`τ (shift g x) = shift g (τ x)` for all `g : G` and `x : G → A`. -/
def IsShiftEquivariant {A : Type*} (τ : (G → A) → (G → A)) : Prop :=
  ∀ (g : G) (x : G → A), τ (shift G g x) = shift G g (τ x)

/-- A map `τ : (G → A) → (G → A)` is a cellular automaton if there are a finite memory set
`S ⊆ G` and a local rule `μ : (S → A) → A` with `τ x g = μ (s ↦ x (g * s))` for all `x` and `g`. -/
def IsCellularAutomaton {A : Type*} (τ : (G → A) → (G → A)) : Prop :=
  ∃ (S : Finset G) (μ : (S → A) → A), ∀ (x : G → A) (g : G),
    τ x g = μ (fun s => x (g * (s : G)))

/-- A group `G` is surjunctive if for every finite nonempty type `A`, every injective,
continuous, shift-equivariant map `(G → A) → (G → A)` is also surjective
(product topology on `G → A`, discrete topology on `A`). -/
def IsSurjunctive : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]
    (τ : (G → A) → (G → A)),
    Continuous τ →
    IsShiftEquivariant G τ →
    Function.Injective τ →
    Function.Surjective τ

/-- A group `G` is residually finite if every non-identity element lies outside some
normal subgroup of finite index. -/
def IsResiduallyFinite : Prop :=
  ∀ g : G, g ≠ 1 → ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ g ∉ N

/-- A group `G` is sofic if for every finite `K ⊆ G` and every `ε > 0` there are a finite
nonempty set `X` and a map `σ : G → Sym(X)` such that
* for all `g, h ∈ K`, `σ (g * h) x = σ g (σ h x)` for at least `(1 - ε)|X|` points `x`;
* for all `g ∈ K` with `g ≠ 1`, `σ g x ≠ x` for at least `(1 - ε)|X|` points `x`. -/
def IsSofic : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ (X : Type) (_ : Finite X) (_ : Nonempty X) (σ : G → Equiv.Perm X),
      (∀ g ∈ K, ∀ h ∈ K,
        (1 - ε) * (Nat.card X : ℝ) ≤ (Nat.card {x : X // σ (g * h) x = σ g (σ h x)} : ℝ)) ∧
      (∀ g ∈ K, g ≠ 1 →
        (1 - ε) * (Nat.card X : ℝ) ≤ (Nat.card {x : X // σ g x ≠ x} : ℝ))

end GottschalkSurjunctivity


