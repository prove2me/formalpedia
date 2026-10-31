-- Prove2me | Definitions.Def_DPDeconstructed_PlanFactorization
-- name    : DPDeconstructed_PlanFactorization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:58.179996+00:00
-- url     : https://prove2.me/theorems/4ce9bd62-9fd4-4814-86fe-93b6b417f346
-- title:
--   Plan factorizations $(W_0,W_1)$, $\mathcal G$, $\mathbb G$, $M$, $M_\sigma$, $S$, $S_\sigma$, $g_\sigma$, $g^*$ and $g$-greedy policies
-- statement:
--   Let $(\mathsf X,\mathsf A,\Gamma,\mathcal V,H)$ be a dynamic program and $\mathbb V\subseteq\mathcal V$ the set of Assumption 2.1. For $h\in\mathbb R^{\mathsf F}$ set
--
--   $$(Mh)(x)=\sup_{a\in\Gamma(x)}h(x,a)\quad(6),\qquad M_\sigma h(x)=h(x,\sigma(x))\quad(18).$$
--
--   A **plan factorization** is a pair of operators $W_0:\mathcal V\to\mathbb R^{\mathsf F}$ and $W_1$ on $\mathcal G:=W_0\mathcal V$ such that
--
--   $$(W_1W_0v)(x,a)=H(x,a,v)\qquad\text{for all }(x,a)\in\mathsf F,\ v\in\mathcal V.\qquad(7)$$
--
--   Then $T=MW_1W_0$. With $\mathbb G:=W_0\mathbb V$:
--
--   1. the **refactored Bellman operator** is $S=W_0MW_1$ on $\mathbb G$ (9);
--   2. the **refactored $\sigma$-value operator** is $S_\sigma=W_0M_\sigma W_1$ on $\mathcal G$ (21), and the **refactored $\sigma$-value function** $g_\sigma$ is its fixed point in $\mathcal G$;
--   3. the **refactored value function** is $g^*(x,a)=\sup_{\sigma\in\Sigma}g_\sigma(x,a)$ (27);
--   4. for $g\in\mathbb G$, $\sigma\in\Sigma$ is **$g$-greedy** if $M_\sigma W_1g=MW_1g$.
--
--   The refactored operator $S$ rotates the cycle $T=MW_1W_0$ and acts on functions of state-action pairs; in the Q-factor transformation $W_1$ is the identity, in Rust's expected-value transformation $W_0$ integrates over the next state.
--
--   **Formalization Note** $W_0$ and $W_1$ are total maps on $\mathbb R^{\mathsf X}$ and $\mathbb R^{\mathsf F}$; only their values on $\mathcal V$ and $\mathcal G$ matter. Conditions (1) "$W_0$ takes values in $\mathcal G$" and (2) "$W_1$ takes values in $\mathcal H$" of the paper hold automatically (the first by definition of $\mathcal G$, the second by (7)), so only (7) is required; read in `EReal`, it also forces $H$ to be real on $\mathsf F\times\mathcal V$. $M$ is `EReal`-valued and $S$ applies `toReal` to $MW_1g$, which is real for $g\in\mathbb G$; $S$ is used only on $\mathbb G$. $g_\sigma$ is the unique fixed point of $S_\sigma$ in $\mathcal G$ when there is one (junk $0$ otherwise) and is not defined as $W_0v_\sigma$; $g^*$ is extended-real valued.
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §2.3, pp.6–7 (𝒢, 𝔾, M (6), plan factorization (7), S (9)), §2.5, pp.10–11 (M_σ (18), S_σ (21), g_σ), §3.1, pp.13–14 (g* (27), g-greedy)

import Mathlib
import Definitions.Def_DPDeconstructed_Policy

namespace DPDeconstructed

namespace DynProg

variable {X A : Type*} (D : DynProg X A)

/-- The maximization operator `M`, Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, display (6), p.6: `(M h)(x) = sup_{a ∈ Γ(x)} h(x, a)`.

**Formalization Note** The supremum is taken in `EReal`. The paper defines `M` on `ℋ`; here it
is defined for every `h : F → ℝ`. -/
noncomputable def M (h : D.SA → ℝ) (x : X) : EReal :=
  ⨆ (a : A) (ha : a ∈ D.Γ x), ((h ⟨(x, a), ha⟩ : ℝ) : EReal)

/-- The operator `M_σ`, arXiv:1811.01940v2, display (18), p.10: `M_σ h(x) := h(x, σ(x))`.

**Formalization Note** The paper defines `M_σ` on `ℋ`; here it is defined for every
`h : F → ℝ`. -/
def Mσ (σ : D.Policy) (h : D.SA → ℝ) (x : X) : ℝ :=
  h ⟨(x, σ.1 x), σ.2.1 x⟩

end DynProg

/-- A plan factorization, arXiv:1811.01940v2, §2.3, pp.6–7: a pair of operators `(W₀, W₁)`
such that (1) `W₀` is defined on `𝒱` and takes values in `𝒢`, (2) `W₁` is defined on `𝒢` and
takes values in `ℋ`, and (3) display (7): `(W₁ W₀ v)(x, a) = H(x, a, v)` for all
`(x, a) ∈ F` and `v ∈ 𝒱`.

**Formalization Note** `W₀ : ℝ^X → ℝ^F` and `W₁ : ℝ^F → ℝ^F` are total maps whose values
outside `𝒱` (resp. `𝒢 = W₀ 𝒱`) never enter a statement. Condition (1) holds by the definition
of `𝒢` (`PlanFactorization.calG`), and condition (2) follows from (7): for `g = W₀ v ∈ 𝒢`,
`W₁ g = H(·, ·, v)` on `F`, which is the definition of `ℋ`. Only (7) is a field. It is an
equation in `EReal`, so it also forces `H` to be real on `F × 𝒱`. -/
structure PlanFactorization {X A : Type*} (D : DynProg X A) where
  /-- `W₀ : 𝒱 → 𝒢`. -/
  W₀ : (X → ℝ) → (D.SA → ℝ)
  /-- `W₁ : 𝒢 → ℋ`. -/
  W₁ : (D.SA → ℝ) → (D.SA → ℝ)
  /-- Display (7): `W₁ W₀ v = H(·, ·, v)` on `F`, for `v ∈ 𝒱`. -/
  factor : ∀ v ∈ D.𝒱, ∀ p : D.SA, ((W₁ (W₀ v) p : ℝ) : EReal) = D.H p.1.1 p.1.2 v

namespace PlanFactorization

variable {X A : Type*} {D : DynProg X A} (P : PlanFactorization D)

/-- `𝒢 := {g ∈ ℝ^F : g = W₀ v for some v ∈ 𝒱}`, arXiv:1811.01940v2, §2.3, p.6. -/
def calG : Set (D.SA → ℝ) := P.W₀ '' D.𝒱

/-- `𝔾 := {g ∈ ℝ^F : g = W₀ v for some v ∈ 𝕍}`, arXiv:1811.01940v2, §2.3, p.6, for the set
`𝕍` of Assumption 2.1. -/
def bbG (𝕍 : Set (X → ℝ)) : Set (D.SA → ℝ) := P.W₀ '' 𝕍

/-- The refactored Bellman operator `S = W₀ M W₁`, arXiv:1811.01940v2, display (9), p.7,
defined on `𝔾`.

**Formalization Note** `M W₁ g` is `EReal`-valued and is converted with `EReal.toReal` before
`W₀` is applied. For `g = W₀ v ∈ 𝔾`, `M W₁ g = T v` is a real-valued element of `𝕍` (by (7) and
Assumption 2.1), so this is the paper's `S` on `𝔾`; off `𝔾` the value is junk, and the mission
applies `S` only to elements of `𝔾`. -/
noncomputable def S (g : D.SA → ℝ) : D.SA → ℝ :=
  P.W₀ (fun x => (D.M (P.W₁ g) x).toReal)

/-- The refactored `σ`-value operator `S_σ := W₀ M_σ W₁`, arXiv:1811.01940v2, display (21),
p.11, on `𝒢`. -/
def Sσ (σ : D.Policy) (g : D.SA → ℝ) : D.SA → ℝ :=
  P.W₀ (D.Mσ σ (P.W₁ g))

open Classical in
/-- The refactored `σ`-value function `g_σ`, arXiv:1811.01940v2, §2.5, p.11 ("a fixed point
`g_σ` of `S_σ` is called a refactored `σ`-value function") and p.14 (under Assumption 2.2 it is
the unique one in `𝒢`, by Proposition 2.3).

**Formalization Note** `g_σ` is defined as the unique fixed point of `S_σ` in `𝒢` (it is *not*
defined as `W₀ v_σ`; that identity is Proposition 2.3). When `S_σ` has no unique fixed point in
`𝒢` the value is the junk `0`; the theorems of the mission all have hypotheses under which the
fixed point exists and is unique. -/
noncomputable def gσ (σ : D.Policy) : D.SA → ℝ :=
  if h : ∃! g, g ∈ P.calG ∧ P.Sσ σ g = g then h.exists.choose else 0

/-- The refactored value function, arXiv:1811.01940v2, display (27), p.13:
`g*(x, a) := sup_{σ ∈ Σ} g_σ(x, a)`, extended-real valued (`⊥` if `Σ` is empty). -/
noncomputable def gstar (p : D.SA) : EReal :=
  ⨆ σ : D.Policy, (P.gσ σ p : EReal)

/-- `g`-greedy policies, arXiv:1811.01940v2, §3.1, p.14: given `g ∈ 𝔾`, `σ ∈ Σ` is `g`-greedy
if `M_σ W₁ g = M W₁ g` (pointwise on `X`, in `EReal`).

**Formalization Note** The predicate is stated for every `g : F → ℝ`; every use has `g ∈ 𝔾`. -/
def IsGGreedy (g : D.SA → ℝ) (σ : D.Policy) : Prop :=
  ∀ x, ((D.Mσ σ (P.W₁ g) x : ℝ) : EReal) = D.M (P.W₁ g) x

end PlanFactorization

end DPDeconstructed


