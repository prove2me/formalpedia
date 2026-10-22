-- Prove2me | Definitions.Def_RiskFunctionals_Conditional_ConditionalAVaR
-- name    : RiskFunctionals_Conditional_ConditionalAVaR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:01.638393+00:00
-- url     : https://prove2.me/theorems/93fd2dc3-d5e4-4775-a7da-aefa0f493a30
-- title:
--   The conditional average value-at-risk, defined by the relation (2.54)/(2.57), and the unconditional $\mathbb{AV@R}_\alpha$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field.
--
--   1. For a probability law $\mu$ on $\mathbb R$ with distribution function $G(u)=\mu((-\infty,u])$, the **quantile function** is $G^{-1}(p)=\inf\{u:G(u)\ge p\}$ for $0<p\le1$.
--   2. For an integrable random variable $Y$ with distribution function $G$ and $0<\alpha\le1$, the **average value-at-risk** is the lower-tail average
--   $$\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du.$$
--   3. For $0<\alpha\le1$ and $Y\in L_1(\Omega,\mathcal F,\mathbb P)$, a class $V\in L_1(\Omega,\mathcal F_1,\mathbb P)$ is **a conditional average value-at-risk** $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)$ if for every $B\in\mathcal F_1$
--   $$\mathbb E(V\mathbb 1_B)=\inf\Big\{\mathbb E(YZ):0\le Z\le\tfrac1\alpha\mathbb 1_B,\ \mathbb E(Z\mid\mathcal F_1)=\mathbb 1_B\Big\},\tag{2.54}$$
--   the infimum running over $Z\in L_\infty(\Omega,\mathcal F,\mathbb P)$, with the constraints holding almost surely.
--   4. For a random variable $Y$, a **version of the conditional distribution function** $G(\cdot\mid\mathcal F_1)$ (2.56) is a map $(\omega,u)\mapsto G(u\mid\mathcal F_1)(\omega)$ with $G(u\mid\mathcal F_1)=\mathbb P(Y\le u\mid\mathcal F_1)$ almost surely for every $u\in\mathbb R$, such that for every $\omega$ the function $u\mapsto G(u\mid\mathcal F_1)(\omega)$ is a distribution function: monotone, continuous from the right, with limit $0$ at $-\infty$ and $1$ at $+\infty$ (an element of $\mathbb G^{(1)}$, p. 73).
--
--   The book defines $\mathbb{AV@R}_\alpha(Y\mid\mathcal F_1)$ implicitly "by the relation" (2.54), repeated as (2.57); it is the most important conditional acceptability mapping, and the unconditional $\mathbb{AV@R}_\alpha$ is what it reduces to when $\mathcal F_1$ is trivial. Item 4 is the object through which Definition 2.55 states version-independence.
--
--   **Formalization Note** Item 3 is a predicate on $V$, not a construction: that exactly one such class exists for each $Y$ is stated as a theorem (Example 2.53(b), Proposition 2.57(i)), never built in. $V$ ranges over Mathlib's `lpMeas ℝ ℝ m 1 P`. The infimum is in `EReal`. The bound $\frac1\alpha\mathbb 1_B$ depends on $B$, as printed. The profit convention is used: $\mathbb{AV@R}_\alpha$ averages the lower tail. The quantile is the left-continuous one; at $p=1$ the defining set may be empty (the book's $G^{-1}(1)=+\infty$) and Lean's `sInf` returns $0$ there, which does not affect the integral. These two unconditional definitions duplicate those of the chapter on the average value-at-risk in this series, which are drafts and cannot be imported.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 71, Example 2.53(b), Eq. (2.54); p. 74, Eq. (2.57); p. 6, Eq. (1.3); p. 48, Definition 2.33, Eq. (2.15)

import Mathlib

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- The quantile function (1.3) (Pflug & Römisch, *Modeling, Measuring and Managing Risk*,
World Scientific 2007, p. 6) of a law `μ` on `ℝ` with distribution function
`G(u) = μ((−∞, u])`: `G⁻¹(p) = inf {u : G(u) ≥ p}`, the left-continuous inverse, for
`0 < p ≤ 1`. For a probability law and `0 < p < 1` the set is nonempty and bounded below; at
`p = 1` it may be empty (the book's `G⁻¹(1) = +∞`) and `sInf` then returns `0`, which only
affects the single point `p = 1`, a null set in the integral of `averageValueAtRisk`. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ μ.real (Set.Iic u)}

/-- The (unconditional) average value-at-risk (p. 48, Definition 2.33, (2.15)) of a profit
variable `Y` at level `0 < α ≤ 1`: `𝔸𝕍@ℝ_α(Y) = (1/α) ∫₀^α G⁻¹(u) du`, the *lower-tail* average,
where `G` is the distribution function of `Y` (its law is `P.map Y`). Every theorem using it
takes `Y` integrable and `0 < α ≤ 1`. -/
noncomputable def averageValueAtRisk {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  (1 / α) * ∫ u in Set.Ioc 0 α, quantileFunction (P.map Y) u

/-- The conditional average value-at-risk (p. 71, Example 2.53(b), (2.54); p. 74, (2.57)) as
the book defines it, implicitly, "by the relation": a class `V ∈ L₁(Ω, ℱ₁, P)` (here
`lpMeas ℝ ℝ m 1 P`, `m` being `ℱ₁`) is `𝔸𝕍@ℝ_α(Y | ℱ₁)` for `Y ∈ L₁(Ω, ℱ, P)` when, for every
`B ∈ ℱ₁`,
`𝔼(𝔸𝕍@ℝ_α(Y|ℱ₁) 𝟙_B) = inf {𝔼(Y Z) : 0 ≤ Z ≤ (1/α) 𝟙_B, 𝔼(Z | ℱ₁) = 𝟙_B}`,
the infimum running over `Z ∈ L_∞(Ω, ℱ, P)` with the constraints holding almost surely. It is
taken in `[−∞, +∞]` (`EReal`). This is a predicate, not a construction: existence and almost-sure
uniqueness of such `V` are statements (Proposition 2.57(i)), not built in. -/
def IsConditionalAVaR {Ω : Type*} (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) (α : ℝ) (Y : Lp ℝ 1 P) (V : lpMeas ℝ ℝ m 1 P) : Prop :=
  ∀ B : Set Ω, MeasurableSet[m] B →
    ((∫ ω in B, (V : Lp ℝ 1 P) ω ∂P : ℝ) : EReal)
      = ⨅ (Z : Lp ℝ ⊤ P)
          (_ : (∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ B.indicator (fun _ => 1 / α) ω) ∧
            P[(Z : Ω → ℝ)|m] =ᵐ[P] B.indicator (fun _ => (1 : ℝ))),
          ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)

/-- A version of the conditional distribution function `G(·|ℱ₁)` of `Y` (p. 74, (2.56)):
`G(u|ℱ₁) = ℙ(Y ≤ u | ℱ₁)` almost surely for every `u`, and for every `ω` the map
`u ↦ G(u|ℱ₁)(ω)` lies in `𝔾⁽¹⁾`, the set of distribution functions on the real line (p. 73):
monotone, continuous from the right, with limits `0` at `−∞` and `1` at `+∞`. Any two versions
agree, as functions of `u`, for almost every `ω`. -/
def IsConditionalDistributionFunction {Ω : Type*} (m : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (Y : Ω → ℝ) (G : Ω → ℝ → ℝ) : Prop :=
  (∀ ω, Monotone (G ω) ∧ (∀ u, ContinuousWithinAt (G ω) (Set.Ici u) u) ∧
      Filter.Tendsto (G ω) Filter.atBot (nhds 0) ∧ Filter.Tendsto (G ω) Filter.atTop (nhds 1)) ∧
    ∀ u : ℝ, (fun ω => G ω u) =ᵐ[P] P[{ω | Y ω ≤ u}.indicator (fun _ => (1 : ℝ))|m]

end RiskFunctionals.Conditional


