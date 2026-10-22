-- Prove2me | Definitions.Def_RiskFunctionals_NestedAVaR_AverageValueAtRisk
-- name    : RiskFunctionals_NestedAVaR_AverageValueAtRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:24.566997+00:00
-- url     : https://prove2.me/theorems/bcd91bd7-2f19-4be1-a89d-ab4ee79d7ed0
-- title:
--   Conditional, nested and multi-period average value-at-risk; the dual set of (3.49)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-field and $\alpha\in(0,1]$. The book works with profit variables (larger is better), and the average value-at-risk is the lower-tail average.
--
--   1. For $Y\in L_1(\mathcal F)$, a random variable $V\in L_1(\mathcal G)$ is a version of the **conditional average value-at-risk** $\mathbb{AV@R}_\alpha(Y\mid\mathcal G)$ if for every $B\in\mathcal G$
--   $$\mathbb E\big(V\,\mathbb 1_B\big)=\inf\Big\{\mathbb E(YZ):0\le Z\le\tfrac1\alpha\mathbb 1_B,\ \mathbb E(Z\mid\mathcal G)=\mathbb 1_B\Big\},\tag{2.54}$$
--   the infimum running over $Z\in L_\infty(\mathcal F)$.
--   2. For a filtration $\boldsymbol{\mathcal F}=(\mathcal F_0,\dots,\mathcal F_T)$ and $Y_t\in L_1(\mathcal F_t)$, the **nested average value-at-risk** is
--   $$\mathrm{n}\mathbb{AV@R}_\alpha(Y;\boldsymbol{\mathcal F})=\mathbb{AV@R}_\alpha(\cdot\mid\mathcal F_0)\circ\mathbb{AV@R}_\alpha(\cdot\mid\mathcal F_1)\circ\dots\circ\mathbb{AV@R}_\alpha(\cdot\mid\mathcal F_{T-1})\Big(\sum_{t=1}^TY_t\Big).\tag{3.48}$$
--   A real number $v$ is a value of it if some versions of the conditional average values-at-risk (one map per stage, defined on all of $L_1(\mathcal F)$) give $v$ as the expectation of the composition.
--   3. For probabilities $\alpha=(\alpha_1,\dots,\alpha_T)$ and constants $c=(c_1,\dots,c_T)$ the **multi-period average value-at-risk** is
--   $$\mathbb{AV@R}_{\alpha,c}(Y;\boldsymbol{\mathcal F})=\sum_{t=1}^Tc_t\,\mathbb E\big[\mathbb{AV@R}_{\alpha_t}(Y_t\mid\mathcal F_{t-1})\big];$$
--   a real number is a value of it if some versions of the conditional average values-at-risk give it.
--   4. The **dual set** of (3.49) is the set of processes $(Z_0,\dots,Z_T)$ with $Z_0=1$ and, for $t=1,\dots,T$, $Z_t$ $\mathcal F_t$-measurable, $0\le Z_t\le\frac1\alpha Z_{t-1}$ and $\mathbb E(Z_t\mid\mathcal F_{t-1})=Z_{t-1}$.
--
--   The conditional average value-at-risk is the basic conditional acceptability mapping of the book; the nested and multi-period versions are two different ways of turning it into a multi-period acceptability functional, and the dual set is the feasible set of the nested one's dual representation.
--
--   **Formalization Note** The book defines $\mathbb{AV@R}_\alpha(Y\mid\mathcal G)$ implicitly by (2.54), so it is a predicate `IsConditionalAVaR 𝒢 P α Y V` (with $V$ $\mathcal G$-measurable and integrable), not a function; existence and uniqueness are results of the book, not built in. The infimum in (2.54) is over measurable $Z$ with the constraints holding almost surely (they force $Z$ to be essentially bounded), and is computed in `EReal`, so an empty constraint set gives $+\infty$ and an unbounded one $-\infty$; neither gives a junk value. $\mathbb E(Z\mid\mathcal G)$ is Mathlib's `P[Z|𝒢]`. The nested and multi-period values are the predicates `IsNestedAVaR` and `IsMultiPeriodAVaR`, existential over versions; since versions agree almost surely, every value is the same number. The nested value uses the composition of the definition `RiskFunctionals.NestedAVaR.Compositions`. In `NestedDualSet`, $Z_0=1$ is the constant function, and the $\mathcal F_t$-measurability of $Z_t$, implicit on the page, is explicit.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 71, Example 2.53(b), Eq. (2.54); p. 150, Definition 3.29; p. 156, Example 3.34, Eq. (3.48), and Proposition 3.35, Eq. (3.49)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions

namespace RiskFunctionals.NestedAVaR

open MeasureTheory

/-- The conditional average value-at-risk as the book defines it, implicitly "by the relation"
(Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 71,
Example 2.53(b), (2.54); p. 74, (2.57)), restated here for the profit convention of the book
(`𝔸𝕍@ℝ` is the *lower-tail* average, larger is better). For a sub-σ-field `𝒢 ⊆ ℱ` (`m`), a level
`α` and `Y ∈ L₁(ℱ)`, a random variable `V` is a version of `𝔸𝕍@ℝ_α(Y | 𝒢)` when `V ∈ L₁(𝒢)` and,
for every `B ∈ 𝒢`,
`𝔼(V 𝟙_B) = inf {𝔼(Y Z) : 0 ≤ Z ≤ (1/α) 𝟙_B, 𝔼(Z | 𝒢) = 𝟙_B}`,
the infimum running over `ℱ`-measurable `Z` (the constraints, holding almost surely, make `Z`
essentially bounded, i.e. `Z ∈ L_∞(ℱ)`). The infimum is taken in `[−∞, +∞]` (`EReal`), so an
empty constraint set gives `+∞` and the relation then fails. This is a predicate: existence and
almost-sure uniqueness of `V` are statements of the book (Example 2.53(b), Proposition 2.57),
not built in. Every theorem using it has `m ≤ mΩ`, so `P[Z|m]` is the true conditional
expectation. -/
def IsConditionalAVaR {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) (α : ℝ) (Y V : Ω → ℝ) : Prop :=
  Measurable[m] V ∧ Integrable V P ∧
    ∀ B : Set Ω, MeasurableSet[m] B →
      ((∫ ω in B, V ω ∂P : ℝ) : EReal)
        = ⨅ (Z : Ω → ℝ) (_ : Measurable Z ∧
            (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ B.indicator (fun _ => 1 / α) ω) ∧
            P[Z|m] =ᵐ[P] B.indicator (fun _ => (1 : ℝ))),
          ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)

/-- The nested average value-at-risk (p. 156, Example 3.34, (3.48)):
`n𝔸𝕍@ℝ_α(Y; 𝓕) = 𝔸𝕍@ℝ_α(· | ℱ₀) ∘ 𝔸𝕍@ℝ_α(· | ℱ₁) ∘ ⋯ ∘ 𝔸𝕍@ℝ_α(· | ℱ_{T−1})(Y₁ + ⋯ + Y_T)`,
the composition (3.46) `𝒜⁽ᵀ⁾` of the conditional acceptability mappings
`𝒜_s = 𝔸𝕍@ℝ_α(· | ℱ_s)`, `s = 0, …, T − 1`, applied to the sum. `v` is *a* value of it when
some choice of versions `A s` of the conditional `𝔸𝕍@ℝ`'s — on every integrable argument,
`A s X` satisfies (2.54) for `ℱ_s` — gives `v = 𝔼[𝒜⁽ᵀ⁾(Y₁ + ⋯ + Y_T)]`; the outermost map lands
in `L₁(ℱ₀)`, a constant when `ℱ₀` is trivial. Only `Y 1, …, Y T` are used. -/
def IsNestedAVaR {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (α : ℝ) (T : ℕ) (Y : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  ∃ A : ℕ → (Ω → ℝ) → Ω → ℝ,
    (∀ s < T, ∀ X : Ω → ℝ, Integrable X P → IsConditionalAVaR (ℱ s) P α X (A s X)) ∧
      v = compositionValue P A T (fun ω => ∑ t ∈ Finset.Icc 1 T, Y t ω)

/-- The multi-period average value-at-risk (p. 150, Definition 3.29):
`𝔸𝕍@ℝ_{α,c}(Y; 𝓕) = ∑_{t=1}^T c_t 𝔼[𝔸𝕍@ℝ_{α_t}(Y_t | ℱ_{t−1})]`. `v` is *a* value of it when
some versions `V t` of `𝔸𝕍@ℝ_{α_t}(Y_t | ℱ_{t−1})`, `t = 1, …, T`, give
`v = ∑_{t=1}^T c_t 𝔼[V_t]`. -/
def IsMultiPeriodAVaR {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (α c : ℕ → ℝ) (T : ℕ) (Y : ℕ → Ω → ℝ) (v : ℝ) : Prop :=
  ∃ V : ℕ → Ω → ℝ,
    (∀ t ∈ Finset.Icc 1 T, IsConditionalAVaR (ℱ (t - 1)) P (α t) (Y t) (V t)) ∧
      v = ∑ t ∈ Finset.Icc 1 T, c t * ∫ ω, V t ω ∂P

/-- The feasible set of the dual representation (3.49), p. 156: processes `Z = (Z₀, Z₁, …, Z_T)`
with `Z₀ = 1` and, for `t = 1, …, T`, `Z_t` `ℱ_t`-measurable (implicit on the page),
`0 ≤ Z_t ≤ (1/α) Z_{t−1}` and `𝔼(Z_t | ℱ_{t−1}) = Z_{t−1}`, all almost surely; such a `Z` is a
nonnegative martingale with `Z_t ≤ α^{−t}`. Indices beyond `T` are unconstrained. -/
def NestedDualSet {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (P : Measure[mΩ] Ω) (α : ℝ) (T : ℕ) : Set (ℕ → Ω → ℝ) :=
  {Z | Z 0 = (fun _ => 1) ∧
    ∀ t ∈ Finset.Icc 1 T, Measurable[ℱ t] (Z t) ∧
      (∀ᵐ ω ∂P, 0 ≤ Z t ω ∧ Z t ω ≤ (1 / α) * Z (t - 1) ω) ∧
      P[Z t|ℱ (t - 1)] =ᵐ[P] Z (t - 1)}

end RiskFunctionals.NestedAVaR


