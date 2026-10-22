-- Prove2me | Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
-- name    : RiskFunctionals_NestedAVaR_Compositions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:41.231487+00:00
-- url     : https://prove2.me/theorems/4b71a673-f08f-471c-abfc-72909636c202
-- title:
--   Conditional acceptability mappings along a filtration and their compositions (3.45), (3.46)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $\boldsymbol{\mathcal F}=(\mathcal F_0,\mathcal F_1,\dots,\mathcal F_T)$ of sub-$\sigma$-fields, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_t\subseteq\mathcal F_{t+1}$, $\mathcal F_T=\mathcal F$. Fix $p\in[1,\infty)$ and put $\mathcal Y_t=L_p(\Omega,\mathcal F_t,\mathbb P)$ and $\mathcal Y=\mathcal Y_1\times\dots\times\mathcal Y_T$. All (in)equalities between random variables hold $\mathbb P$-almost surely.
--
--   1. A family $\mathcal A_0,\dots,\mathcal A_{T-1}$ of **conditional acceptability mappings** consists of maps $\mathcal A_{t-1}=\mathcal A(\cdot\mid\mathcal F_{t-1}):\mathcal Y_T\to\mathcal Y_{t-1}$, $t=1,\dots,T$, such that for all $Y_T,\tilde Y_T\in\mathcal Y_T$:
--      - (CA1) $\mathcal A_{t-1}(Y_T+Y_{t-1})=\mathcal A_{t-1}(Y_T)+Y_{t-1}$ for every $Y_{t-1}\in\mathcal Y_{t-1}$;
--      - (CA2) $\mathcal A_{t-1}(\lambda Y_T+(1-\lambda)\tilde Y_T)\ge\lambda\mathcal A_{t-1}(Y_T)+(1-\lambda)\mathcal A_{t-1}(\tilde Y_T)$ for all $\lambda\in[0,1]$;
--      - (CA3) $Y_T\le\tilde Y_T$ implies $\mathcal A_{t-1}(Y_T)\le\mathcal A_{t-1}(\tilde Y_T)$.
--   2. The family is **positively homogeneous** if $\mathcal A_t(\lambda Y_T)=\lambda\mathcal A_t(Y_T)$ for all $\lambda>0$ and $Y_T\in\mathcal Y_T$.
--   3. The **nested functional** and the **compositions** are
--   $$\mathcal A(Y;\boldsymbol{\mathcal F})=\mathcal A_0\big[Y_1+\dots+\mathcal A_{T-2}[Y_{T-1}+\mathcal A_{T-1}(Y_T)]\cdots\big],\tag{3.45}$$
--   $$\mathcal A^{(t)}(Y_T)=\mathcal A_0\circ\mathcal A_1\circ\dots\circ\mathcal A_{t-1}(Y_T),\qquad t=1,\dots,T.\tag{3.46}$$
--   Both are $\mathcal F_0$-measurable, hence constant, and their real values are their expectations.
--
--   These are the objects of §3.3.4 of the book: the nested functional builds a multi-period acceptability functional from one-period conditional ones by backward recursion, and the composition $\mathcal A^{(t)}$ is the single-period functional obtained by chaining the first $t$ of them.
--
--   **Formalization Note** The filtration is Mathlib's `Filtration ℕ mΩ`, of which only the indices $0,\dots,T$ matter; `IsStandardFiltration ℱ T` records $\mathcal F_0=\{\emptyset,\Omega\}$ and $\mathcal F_T=\mathcal F$. Random variables are functions `Ω → ℝ`; $X\in L_p(\mathcal G)$ is `IsLp 𝒢 P p X`: $X$ is $\mathcal G$-measurable and in $L_p$. The mappings are a single family `A : ℕ → (Ω → ℝ) → Ω → ℝ` with `A s` $=\mathcal A_s$; (CA1)–(CA3) and positive homogeneity are required only on arguments in $\mathcal Y_T$ and only for $s<T$. The process $Y=(Y_1,\dots,Y_T)$ is `Y : ℕ → Ω → ℝ`, of which only `Y 1, …, Y T` are used. `nestedFunctional` evaluates (3.45) from the inside out with $\mathcal A_{T-1}(Y_T+0)$ innermost; `nestedValue` and `compositionValue` are the expectations of the two random variables.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 154, §3.3.4 (conditions (CA1)–(CA3)); p. 155, Eqs. (3.45), (3.46)

import Mathlib

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- `X ∈ L_p(Ω, 𝒢, P)`: `X` is `𝒢`-measurable and `p`-integrable (Pflug & Römisch, *Modeling,
Measuring and Managing Risk*, World Scientific 2007, p. 154, §3.3.4: `𝒴_t := L_p(ℱ_t)`).
Here `P` is a measure on the ambient σ-field `ℱ` and `𝒢 ⊆ ℱ` is a sub-σ-field. -/
def IsLp {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (p : ENNReal) (X : Ω → ℝ) : Prop :=
  Measurable[m] X ∧ MemLp X p P

/-- The standing assumptions on the filtration in §3.3.4, p. 154: `𝓕 = (ℱ₀, ℱ₁, …, ℱ_T)` is a
filtration of sub-σ-fields of `ℱ` (Mathlib's `Filtration ℕ mΩ`, of which only the indices
`0, …, T` matter), `ℱ₀ = {∅, Ω}` is trivial, and `ℱ_T = ℱ` is the ambient σ-field. -/
def IsStandardFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (T : ℕ) : Prop :=
  (∀ s : Set Ω, MeasurableSet[ℱ 0] s → s = ∅ ∨ s = Set.univ) ∧ ℱ T = mΩ

/-- A family of conditional acceptability mappings along a filtration (p. 154, §3.3.4, after
Definition 2.50): for each `t = 1, …, T` a mapping `𝒜_{t−1} = 𝒜(· | ℱ_{t−1})` from
`𝒴_T = L_p(ℱ_T)` to `𝒴_{t−1} = L_p(ℱ_{t−1})`; here `A s` is `𝒜_s` for `s = 0, …, T − 1`.
For all `Y_T, Ỹ_T ∈ 𝒴_T`, with every (in)equality holding `P`-almost surely:
* (CA1) `𝒜_{t−1}(Y_T + Y_{t−1}) = 𝒜_{t−1}(Y_T) + Y_{t−1}` for every `Y_{t−1} ∈ 𝒴_{t−1}`;
* (CA2) `𝒜_{t−1}(λY_T + (1 − λ)Ỹ_T) ≥ λ𝒜_{t−1}(Y_T) + (1 − λ)𝒜_{t−1}(Ỹ_T)` for `λ ∈ [0, 1]`;
* (CA3) `Y_T ≤ Ỹ_T` implies `𝒜_{t−1}(Y_T) ≤ 𝒜_{t−1}(Ỹ_T)`.
The values of `A s` outside `𝒴_T`, and the maps `A s` for `s ≥ T`, are not constrained. -/
structure IsConditionalAcceptabilityFamily {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω) (p : ENNReal) (T : ℕ)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop where
  /-- `𝒜_s` maps `𝒴_T` into `𝒴_s = L_p(ℱ_s)`. -/
  mapsTo : ∀ s < T, ∀ X, IsLp (ℱ T) P p X → IsLp (ℱ s) P p (A s X)
  /-- (CA1) Predictable translation-equivariance. -/
  translation : ∀ s < T, ∀ X W, IsLp (ℱ T) P p X → IsLp (ℱ s) P p W →
    A s (X + W) =ᵐ[P] A s X + W
  /-- (CA2) Concavity. -/
  concave : ∀ s < T, ∀ X X', IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' →
    ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      (fun ω => l * A s X ω + (1 - l) * A s X' ω) ≤ᵐ[P] A s (l • X + (1 - l) • X')
  /-- (CA3) Monotonicity. -/
  monotone : ∀ s < T, ∀ X X', IsLp (ℱ T) P p X → IsLp (ℱ T) P p X' →
    X ≤ᵐ[P] X' → A s X ≤ᵐ[P] A s X'

/-- Positive homogeneity of the conditional mappings `𝒜_s`, `s = 0, …, T − 1` (p. 155,
Proposition 3.33; Definition 2.50): `𝒜_s(λY_T) = λ𝒜_s(Y_T)` almost surely for `λ > 0`,
`Y_T ∈ 𝒴_T`. -/
def IsPositivelyHomogeneousFamily {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω) (p : ENNReal) (T : ℕ)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ s < T, ∀ X, IsLp (ℱ T) P p X → ∀ l : ℝ, 0 < l → A s (l • X) =ᵐ[P] l • A s X

/-- The composition (3.46), p. 155: `𝒜⁽ᵗ⁾ := 𝒜₀ ∘ 𝒜₁ ∘ ⋯ ∘ 𝒜_{t−1}`, so
`composition A 0 X = X` and `composition A (t + 1) X = composition A t (A t X)`. -/
noncomputable def composition {Ω : Type*} (A : ℕ → (Ω → ℝ) → Ω → ℝ) : ℕ → (Ω → ℝ) → Ω → ℝ
  | 0, X => X
  | t + 1, X => composition A t (A t X)

/-- The nested multi-period functional (3.45), p. 155, as a random variable:
`𝒜₀[Y₁ + 𝒜₁[Y₂ + ⋯ + 𝒜_{T−2}[Y_{T−1} + 𝒜_{T−1}(Y_T)]⋯]]`, computed from the inside out:
the innermost term is `𝒜_{T−1}(Y_T + 0)`, and stage `s` applies `𝒜_s` to `Y_{s+1}` plus the
result of the later stages. The process `Y = (Y₁, …, Y_T)` is indexed by `ℕ`; only `Y 1, …, Y T`
are used. -/
noncomputable def nestedFunctional {Ω : Type*} (A : ℕ → (Ω → ℝ) → Ω → ℝ)
    (Y : ℕ → Ω → ℝ) (T : ℕ) : Ω → ℝ :=
  (List.range T).foldr (fun s acc => A s (Y (s + 1) + acc)) 0

/-- The real value `𝒜(Y; 𝓕)` of (3.45): the expectation of the `ℱ₀`-measurable random variable
`nestedFunctional A Y T`. Since `ℱ₀ = {∅, Ω}`, that random variable is constant and the
expectation is its value. -/
noncomputable def nestedValue {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∫ ω, nestedFunctional A Y T ω ∂P

/-- The real value `𝒜⁽ᵗ⁾(Y_T)` of (3.46): the expectation of the `ℱ₀`-measurable (hence constant)
random variable `𝒜₀ ∘ ⋯ ∘ 𝒜_{t−1}(Y_T)`. -/
noncomputable def compositionValue {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (A : ℕ → (Ω → ℝ) → Ω → ℝ) (t : ℕ) (X : Ω → ℝ) : ℝ :=
  ∫ ω, composition A t X ω ∂P

end RiskFunctionals.NestedAVaR


