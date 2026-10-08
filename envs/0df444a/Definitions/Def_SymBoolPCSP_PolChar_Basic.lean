-- Prove2me | Definitions.Def_SymBoolPCSP_PolChar_Basic
-- name    : SymBoolPCSP_PolChar_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:53.170975+00:00
-- url     : https://prove2.me/theorems/65b9493d-3369-45cc-9b62-01c3ee8de506
-- title:
--   Families of functions, projections $f^\pi$, projection-closed and finitizable families, $\mathrm{Pol}(\Gamma)$, clones (Definitions 2.4, 6.4; §6.2–6.3)
-- statement:
--   Let $D$ be a domain. A **family of functions** over $D$ is a collection $\mathcal F$ of functions $f : D^L \to D$ of various arities $L$; in this formalization it is given by a set $\mathcal F_L$ of functions $D^L \to D$ for every arity $L$, and only the positive arities $L \ge 1$ are ever inspected.
--
--   1. **Projection** (Definition 6.4). For $f : D^L \to D$ and any map $\pi : [L] \to [R]$, the projection of $f$ along $\pi$ is the function $f^\pi : D^R \to D$ given by
--   $$f^\pi(y) = f(x), \qquad x_i = y_{\pi(i)} \text{ for all } i \in [L].$$
--   The arity $R$ may be larger than, equal to, or smaller than $L$.
--   2. **Projection-closed.** $\mathcal F$ is projection-closed if for all $L, R \ge 1$, all $f \in \mathcal F$ of arity $L$ and all maps $\pi : [L] \to [R]$, the projection $f^\pi$ belongs to $\mathcal F$.
--   3. **Finitizable.** $\mathcal F$ is finitizable if there is an arity $R \ge 1$, the *finitized arity*, such that for every $L \ge 1$ and every $f : D^L \to D$,
--   $$f \in \mathcal F \iff f^\pi \in \mathcal F \text{ for every } \pi : [L] \to [R].$$
--   4. **Contains the identity.** $\mathrm{id}_D \in \mathcal F$, where $\mathrm{id}_D : D \to D$, $\mathrm{id}_D(x) = x$, viewed as a function of arity $1$.
--   5. **Polymorphisms** (Definition 2.4). A family $\Gamma = \{(P_R, Q_R)\}$ of promise relations over $D$ is a pair of relational structures $\mathbb A, \mathbb B$ on a common signature, with $P_R = R^{\mathbb A}$ and $Q_R = R^{\mathbb B}$. $\mathrm{Pol}(\Gamma)$ is the family whose arity-$L$ members are the $f : D^L \to D$ such that for every relation symbol $R$ of arity $k$ and all $x^{(1)}, \dots, x^{(L)} \in P_R$,
--   $$\bigl(f(x^{(1)}_1, \dots, x^{(L)}_1), \dots, f(x^{(1)}_k, \dots, x^{(L)}_k)\bigr) \in Q_R.$$
--   6. **Clone** (§6.3, p. 30). $\mathcal F$ is a clone if for all $f \in \mathcal F$ of arity $L_1$ and all $g_1, \dots, g_{L_1} \in \mathcal F$ of arity $L_2$, the function
--   $$h(x^{(1)}, \dots, x^{(L_1)}) = f\bigl(g_1(x^{(1)}), \dots, g_{L_1}(x^{(L_1)})\bigr),$$
--   of arity $L_1 L_2$ (each $x^{(i)} \in D^{L_2}$), belongs to $\mathcal F$.
--
--   These notions are the vocabulary of the characterization of polymorphism families of finite promise templates (Theorem 6.5) and of its CSP analogue (Lemma 6.8).
--
--   **Formalization Note** A family is `FunFamily D := (L : ℕ) → Set ((Fin L → D) → D)`; coordinates are 0-based (`Fin L`) rather than the paper's $[L] = \{1, \dots, L\}$, and $f^\pi$ is `fun y => f (y ∘ π)` with `π : Fin L → Fin R`. All arities are positive: the paper writes $L, R \in \mathbb N$ without excluding $0$, but at arity $0$ the finitized-arity argument of Claim 6.6 breaks, so arities are read as positive integers. `Pol` reuses `IsPolymorphism` from the published `PCSPBLPAff_Symmetric_Setting`. In the clone condition the input of $h$ is indexed by `Fin (L₁ * L₂)`, and the block $x^{(i)}$ is `j ↦ x (finProdFinEquiv (i, j))`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 9, Definition 2.4; pp. 28–30, Definition 6.4, projection-closed (p. 28), finitizable and id_D (p. 29), clone (p. 30)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

/-! ### Families of functions, projections, Pol(Γ) (§2.1, p. 9; §6.2–6.3, pp. 28–30)

A finite family `Γ = {(P_i, Q_i)}` of promise relations over the domain `D` is a pair of
relational structures `𝔸 𝔹 : RelStruct τ ar D` on the same signature `τ` (finite in every
statement), with `𝔸.rel R ⊆ 𝔹.rel R` for each symbol `R`. Arities of functions are positive
throughout: every condition below is imposed only on arities `L ≥ 1`. Coordinates are indexed
by `Fin L` (0-based) instead of the paper's `[L] = {1, …, L}`. -/

/-- A family of functions over the domain `D`: for each arity `L`, a set of functions
`f : D^L → D`. Only the arities `L ≥ 1` are ever inspected. -/
abbrev FunFamily (D : Type) : Type := (L : ℕ) → Set ((Fin L → D) → D)

/-- The projection `f^π : D^R → D` of `f : D^L → D` along `π : [L] → [R]` (Definition 6.4,
p. 28): `f^π(y) = f(x)` where `x_i = y_{π(i)}` for all `i ∈ [L]`, i.e. `x = y ∘ π`.
`R` may be larger than `L`. -/
def projection {D : Type} {L R : ℕ} (f : (Fin L → D) → D) (π : Fin L → Fin R) :
    (Fin R → D) → D :=
  fun y => f (y ∘ π)

/-- `F` is projection-closed (p. 28): for all arities `L, R ≥ 1`, every `f ∈ F` of arity `L` and
every map `π : [L] → [R]`, the projection `f^π` lies in `F`. -/
def ProjectionClosed {D : Type} (F : FunFamily D) : Prop :=
  ∀ L R : ℕ, 0 < L → 0 < R → ∀ f ∈ F L, ∀ π : Fin L → Fin R, projection f π ∈ F R

/-- `F` is finitizable (p. 29): there is a finitized arity `R ≥ 1` such that, for every arity
`L ≥ 1`, a function `f : D^L → D` lies in `F` if and only if every projection `f^π` with
`π : [L] → [R]` lies in `F`. -/
def Finitizable {D : Type} (F : FunFamily D) : Prop :=
  ∃ R : ℕ, 0 < R ∧ ∀ L : ℕ, 0 < L → ∀ f : (Fin L → D) → D,
    f ∈ F L ↔ ∀ π : Fin L → Fin R, projection f π ∈ F R

/-- `id_D ∈ F` (p. 29): the unary identity `id_D(x) = x`, i.e. `x ↦ x_1` on `D^1`, lies in `F`. -/
def ContainsId {D : Type} (F : FunFamily D) : Prop :=
  (fun x : Fin 1 → D => x 0) ∈ F 1

/-- `Pol(Γ)` for `Γ = (𝔸, 𝔹)` as a family of functions (Definition 2.4, p. 9): at arity `L`,
the functions `f : D^L → D` that are polymorphisms of every promise relation
`(𝔸.rel R, 𝔹.rel R)`. -/
def Pol {D : Type} {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar D) : FunFamily D :=
  fun _ => {f | IsPolymorphism 𝔸 𝔹 f}

/-- `F` is a clone (p. 30): for all arities `L₁, L₂ ≥ 1`, every `f ∈ F` of arity `L₁` and all
`g_1, …, g_{L₁} ∈ F` of arity `L₂`, the function
`h(x^{(1)}, …, x^{(L₁)}) = f(g_1(x^{(1)}), …, g_{L₁}(x^{(L₁)}))` of arity `L₁ L₂` (the `g_i` act on
disjoint blocks of inputs) lies in `F`. The input of `h` is indexed by `Fin (L₁ * L₂)`, and the
block `x^{(i)}` is `j ↦ x (finProdFinEquiv (i, j))`. -/
def IsClone {D : Type} (F : FunFamily D) : Prop :=
  ∀ L₁ L₂ : ℕ, 0 < L₁ → 0 < L₂ → ∀ f ∈ F L₁, ∀ g : Fin L₁ → (Fin L₂ → D) → D,
    (∀ i, g i ∈ F L₂) →
      (fun x : Fin (L₁ * L₂) → D => f (fun i => g i (fun j => x (finProdFinEquiv (i, j))))) ∈
        F (L₁ * L₂)

end SymBoolPCSP.PolChar


