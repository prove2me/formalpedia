-- Prove2me | Definitions.Def_ParetoDDO_DataDriven
-- name    : ParetoDDO_DataDriven
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:14.748642+00:00
-- url     : https://prove2.me/theorems/097ff0f9-a0ac-49f5-8c78-ded11de9811b
-- title:
--   Data-driven predictors and prescriptors, $\widehat{\mathcal X}$, and the meta-problem (2.4b)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be the decision set, $\{\mathbb P_\theta\}_{\theta\in\Theta}$ the models and $\mathcal F_T=\sigma(\xi_{[T]})$.
--
--   1. **Definition 2.2 (data-driven predictor).** A family of random variables $\widehat c_T(x)$, $T\in\mathbb N$, $x\in X$, such that (i) $x\mapsto\widehat c_T(x)$ is continuous on $X$; (ii) $\widehat c_T(x)$ is $\mathcal F_T$-measurable; (iii) there is one nonnegative random variable $\bar c$ with $\mathbb E_\theta[\bar c]<\infty$ and $|\widehat c_T(x)|\le\bar c$ $\mathbb P_\theta$-a.s. for all $T$, $x\in X$, $\theta\in\Theta$; (iv) for a Borel $c_\infty:X\times\Theta\to\mathbb R$, $\widehat c_T(x)\to c_\infty(x,\theta)$ in $\mathbb P_\theta$-probability; (v) for a Borel $v_\infty:\Theta\to\mathbb R$, $\min_{x\in X}\widehat c_T(x)\to v_\infty(\theta)$ in $\mathbb P_\theta$-probability.
--   2. **Definition 2.3 (data-driven prescriptor).** An $\mathcal F_T$-adapted process $\widehat x_T\in X$ that is induced by some data-driven predictor: $\widehat x_T\in\arg\min_{x\in X}\widehat c_T(x)$ for all $T$.
--   3. $\widehat{\mathcal X}$ is the set of pairs $(\widehat c,\widehat x)$ of a data-driven predictor and a data-driven prescriptor induced by it.
--   4. **Meta-problem (2.4b).** $(\widehat c,\widehat x)\in\widehat{\mathcal X}$ is feasible if for every $\theta\in\Theta$
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P_\theta\big[c(\widehat x_T,\theta)>\widehat c_T(\widehat x_T)\big]\le-r ,
--   $$
--   and the objectives are $\lim_{T\to\infty}\mathbb E_\theta[\widehat c_T(\widehat x_T)]$, one for each $\theta\in\Theta$.
--   5. A feasible pair is **Pareto dominant** (a strong solution) if for every feasible pair and every $\theta\in\Theta$ its objective is no larger.
--
--   The probability in 4 is the out-of-sample prescription disappointment of Definition 2.4.
--
--   **Formalization Note** `ĉ T x ω` is $\widehat c_T(x)(\omega)$ and `xh T ω` is $\widehat x_T(\omega)$. Every condition is imposed for $T\ge1$; continuity in (i) and the argmin property hold at every sample point; $\min_{x\in X}$ is `sInf` of the image of $X$; Borel measurability of $c_\infty$, $v_\infty$ is on the subspaces $X\times\Theta$ and $\Theta$. Pareto dominance states explicitly that both in-sample risks are integrable for $T\ge1$ and that both sequences of expectations converge, with the limits compared (the paper notes both limits are well defined, p.16).
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Definitions 2.2–2.4, pp.12–15; (2.4b), p.16; Notation (strong solution), p.6

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology

namespace ParetoDDO

variable {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}

/-- **Definition 2.2** (data-driven predictors; arXiv:2010.06606v4, pp.12–13). A decision-dependent
process `ĉ = {ĉ_T(x)}` is a data-driven predictor if
(i) `x ↦ ĉ_T(x)` is continuous on `X` for every `T` (and every sample point);
(ii) `{ĉ_T(x)}_T` is adapted to `{F_T}` for every `x ∈ X`;
(iii) one nonnegative random variable `c̄` with `E_θ[c̄] < ∞` for all `θ ∈ Θ` bounds `|ĉ_T(x)|`
`P_θ`-almost surely, for all `T`, `x ∈ X`, `θ ∈ Θ`;
(iv) for a deterministic Borel function `c∞ : X × Θ → ℝ`, `ĉ_T(x) → c∞(x, θ)` in `P_θ`-probability
for all `x ∈ X`, `θ ∈ Θ`;
(v) for a deterministic Borel function `v∞ : Θ → ℝ`, `min_{x∈X} ĉ_T(x) → v∞(θ)` in
`P_θ`-probability for all `θ ∈ Θ`.

**Formalization Note** `ĉ T x ω` is `ĉ_T(x)(ω)`. Time is `T ∈ {1, 2, …}`: the `T = 0` slice is
unconstrained. `min_{x∈X}` is `sInf` of the image of `X`, the minimum for compact nonempty `X`.
Borel measurability of `c∞`, `v∞` is on the subspaces `X × Θ`, `Θ`. -/
structure IsDataDrivenPredictor (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (X : Set (Vec n)) (ĉ : ℕ → Vec n → Ω → ℝ) : Prop where
  /-- (i) Continuity in the decisions. -/
  continuousOn : ∀ T, 1 ≤ T → ∀ ω, ContinuousOn (fun x => ĉ T x ω) X
  /-- (ii) Non-anticipativity. -/
  adapted : ∀ T, 1 ≤ T → ∀ x ∈ X, Measurable[histSigma ξ T] (ĉ T x)
  /-- (iii) Uniform integrability. -/
  dominated : ∃ cbar : Ω → ℝ, Measurable cbar ∧ (∀ ω, 0 ≤ cbar ω) ∧
    (∀ θ ∈ Θ, Integrable cbar (P θ)) ∧
    ∀ T, 1 ≤ T → ∀ x ∈ X, ∀ θ ∈ Θ, ∀ᵐ ω ∂(P θ), |ĉ T x ω| ≤ cbar ω
  /-- (iv) Convergence of objective. -/
  tendsto_objective : ∃ cinf : Vec n → Vec d → ℝ,
    Measurable (fun p : ↥(X ×ˢ Θ) => cinf p.1.1 p.1.2) ∧
    ∀ x ∈ X, ∀ θ ∈ Θ, TendstoInMeasure (P θ) (fun T => ĉ T x) atTop (fun _ => cinf x θ)
  /-- (v) Convergence of optimal value. -/
  tendsto_value : ∃ vinf : Vec d → ℝ, Measurable (fun θ : ↥Θ => vinf θ) ∧
    ∀ θ ∈ Θ, TendstoInMeasure (P θ) (fun T ω => sInf ((fun x => ĉ T x ω) '' X)) atTop
      (fun _ => vinf θ)

/-- The predictor `ĉ` induces the prescriptor `x̂`: `x̂_T ∈ argmin_{x∈X} ĉ_T(x)` for all `T`
(arXiv:2010.06606v4, Definition 2.3 (ii), p.13), at every sample point. -/
def Induces (X : Set (Vec n)) (ĉ : ℕ → Vec n → Ω → ℝ) (xh : ℕ → Ω → Vec n) : Prop :=
  ∀ T, 1 ≤ T → ∀ ω, xh T ω ∈ X ∧ IsMinOn (fun x => ĉ T x ω) X (xh T ω)

/-- **Definition 2.3** (data-driven prescriptors; arXiv:2010.06606v4, p.13). A process
`x̂ = {x̂_T}` valued in `X` is a data-driven prescriptor if (i) it is adapted to `{F_T}` and (ii) some
data-driven predictor induces it. -/
def IsDataDrivenPrescriptor (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (X : Set (Vec n)) (xh : ℕ → Ω → Vec n) : Prop :=
  (∀ T, 1 ≤ T → ∀ ω, xh T ω ∈ X) ∧ (∀ T, 1 ≤ T → Measurable[histSigma ξ T] (xh T)) ∧
    ∃ ĉ, IsDataDrivenPredictor ξ P Θ X ĉ ∧ Induces X ĉ xh

/-- Membership in `X̂`, the set of data-driven predictor-prescriptor pairs `(ĉ, x̂)` "where `x̂` is
induced by `ĉ`" (arXiv:2010.06606v4, p.13). -/
def IsPredictorPrescriptorPair (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (X : Set (Vec n)) (ĉ : ℕ → Vec n → Ω → ℝ) (xh : ℕ → Ω → Vec n) : Prop :=
  IsDataDrivenPredictor ξ P Θ X ĉ ∧ IsDataDrivenPrescriptor ξ P Θ X xh ∧ Induces X ĉ xh

/-- Feasibility in the meta-optimization problem **(2.4b)** (arXiv:2010.06606v4, p.16): `(ĉ, x̂) ∈ X̂`
and, for every `θ ∈ Θ`, the out-of-sample prescription disappointment
`P_θ[c(x̂_T, θ) > ĉ_T(x̂_T)]` (Definition 2.4, p.15) satisfies
`limsup_{T→∞} (1/T) log P_θ[c(x̂_T, θ) > ĉ_T(x̂_T)] ≤ −r`. -/
def IsFeasible24b (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (X : Set (Vec n)) (c : Vec n → Vec d → ℝ) (r : ℝ) (ĉ : ℕ → Vec n → Ω → ℝ)
    (xh : ℕ → Ω → Vec n) : Prop :=
  IsPredictorPrescriptorPair ξ P Θ X ĉ xh ∧
    ∀ θ ∈ Θ, decayRate (P θ) (fun T => {ω | ĉ T (xh T ω) ω < c (xh T ω) θ}) ≤ -(r : EReal)

/-- `(ĉ, x̂)` is a **Pareto dominant** (strong) solution of **(2.4b)** (arXiv:2010.06606v4, Notation,
p.6, and (2.4b), p.16): it is feasible, and for every feasible `(ĉ', x̂')` and every model `θ ∈ Θ`
the objective `lim_{T→∞} E_θ[ĉ_T(x̂_T)]` is at most `lim_{T→∞} E_θ[ĉ'_T(x̂'_T)]`.

**Formalization Note** The paper notes both limits are well defined (p.16). This is stated
explicitly: both in-sample risks are integrable for `T ≥ 1`, both sequences of expectations converge,
and the limits compare. -/
def IsParetoDominant24b (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (X : Set (Vec n)) (c : Vec n → Vec d → ℝ) (r : ℝ) (ĉ : ℕ → Vec n → Ω → ℝ)
    (xh : ℕ → Ω → Vec n) : Prop :=
  IsFeasible24b ξ P Θ X c r ĉ xh ∧
    ∀ (ĉ' : ℕ → Vec n → Ω → ℝ) (xh' : ℕ → Ω → Vec n), IsFeasible24b ξ P Θ X c r ĉ' xh' →
      ∀ θ ∈ Θ,
        (∀ T, 1 ≤ T → Integrable (fun ω => ĉ T (xh T ω) ω) (P θ)) ∧
        (∀ T, 1 ≤ T → Integrable (fun ω => ĉ' T (xh' T ω) ω) (P θ)) ∧
        ∃ a b : ℝ, Tendsto (fun T => ∫ ω, ĉ T (xh T ω) ω ∂(P θ)) atTop (𝓝 a) ∧
          Tendsto (fun T => ∫ ω, ĉ' T (xh' T ω) ω ∂(P θ)) atTop (𝓝 b) ∧ a ≤ b

end ParetoDDO


