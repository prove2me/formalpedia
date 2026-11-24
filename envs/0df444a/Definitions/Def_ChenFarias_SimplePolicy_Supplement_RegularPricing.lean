-- Prove2me | Definitions.Def_ChenFarias_SimplePolicy_Supplement_RegularPricing
-- name    : ChenFarias_SimplePolicy_Supplement_RegularPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:58:22.175801+00:00
-- url     : https://prove2.me/theorems/e74d3beb-0f25-4608-bfd6-6c4a60315ac5
-- title:
--   Assumption 2 — valuation densities, regular price paths and the robustness constraint
-- statement:
--   Let $f\ge0$ be an integrable density, zero on negative valuations, with $\int f=1$. The tail $\bar F(p)=\int_{(p,\infty)}f(v)\,dv$ is the published base definition. Neither Assumption 1 nor strict positivity of $f$ is required.
--
--   A pricing policy comprises a finite simple sales process and its finite price while stock remains. The posted price is $+\infty$ after sell-out. Its natural history is $\mathcal F_t=\sigma(\pi_s,N_s:0\le s\le t)$ and its pre-time history is $\mathcal G_t=\mathcal F_{t-}$. Prices are left continuous, nonnegative, and $\mathcal G$-adapted. Sales have intensity $\lambda\bar F(\pi_t)$ before stockout and zero afterward.
--
--   For every $0\le s\le t\le T$, the restricted sub-martingale constraint is
--   $$
--   \mathbb E[(\pi_s-\pi_t)^+\mid\mathcal G_s]\le\underline\theta(t-s)\quad\text{on }\{X_{s-}>0\}.
--   $$
--   A future infinite price contributes zero drop. The inequality is encoded equivalently by integrating over every event in $\mathcal G_s$; expectations are nonnegative integrals.
--
--   Assumption 2 is the decomposition, while stock remains,
--   $$
--   \pi_t=c_t+\sum_{S_k<t}\Delta_{S_k},\qquad |d_t|\le B,\quad |\Delta_t|\le B,
--   $$
--   where $c$ is continuous and differentiable away from sale times, $d$ is its actual left derivative, and $\Delta$ is left continuous. Both $c$ and $\Delta$ are adapted to $\mathcal F$. Regularity is defined separately from robustness, avoiding the circularity of Proposition 1's wording. The printed local condition is $d_s^-+\lambda\bar F(\pi_s)\Delta_s^-\le\underline\theta$, almost surely for each $s$ while stock remains. Expected revenue is
--   $$
--   \mathbb E\int_0^T\mathbf1_{\{X_{s-}>0\}}\lambda\pi_s\bar F(\pi_s)\,ds.
--   $$
--   These definitions share one fixed $B$ and one $\underline\theta$. They include a diagnostic example: exponential valuations, one item, price 1, and sale time $e/e^{-1}$ for a standard exponential coordinate $e$.
--
--   **Formalization Note** Joint measurability expresses the usual measurable-process convention. Path regularity is simultaneous almost surely. Initial price information is included in $\mathcal G_0$. The actual left derivative is imposed for positive times; its zero-time field is only bounded, since the source supplies no left neighbourhood at time zero. The finite price field after sell-out is unused. All expectations use `lintegral`; nonnegative integrands are converted with `ENNReal.ofReal`, which discards no value. No value-function or revenue bound is built into the policy.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), pp. 1123–1124, §2 and (1)–(2); p. 1133, Assumption 2 and (10); p. 1141, endnotes 2, 6, 7, 12

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
import Definitions.Def_ChenFarias_SimplePolicy_Supplement_PointProcess

namespace ChenFarias.SimplePolicy.Supplement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The valuation-law conventions of §2, without Assumption 1 or full support. -/
structure IsDensity (f : ℝ → ℝ) : Prop where
  nonnegative : ∀ v, 0 ≤ f v
  supported : ∀ v < 0, f v = 0
  integrable : Integrable f
  mass_one : (∫ v, f v) = 1

/-- Negative part of a real number. -/
def negPart (r : ℝ) : ℝ := max (-r) 0

/-- A price while inventory is available, on a general finite sales process.
The real field after sell-out is unused: the actual posted price is `⊤`. -/
structure Pricing (Ω : Type*) (x0 : ℕ) where
  sales : FinitePointProcess Ω x0
  core : ℝ → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {x0 : ℕ}

/-- Posted prices, implementing constraint 3 of p. 1124. -/
def Pricing.posted (P : Pricing Ω x0) (t : ℝ) (ω : Ω) : WithTop ℝ :=
  if P.sales.stock t ω = 0 then ⊤ else (P.core t ω : WithTop ℝ)

/-- `F_t = σ(π_s, N_s : 0 ≤ s ≤ t)`. -/
@[instance_reducible]
def Pricing.history (P : Pricing Ω x0) (t : ℝ) : MeasurableSpace Ω :=
  ⨆ s ∈ Icc (0 : ℝ) t,
    MeasurableSpace.comap (fun ω => (P.posted s ω, P.sales.count s ω)) inferInstance

/-- The pre-time history `G_t = F_{t-}`. Initial prices are already known at time zero. -/
@[instance_reducible]
def Pricing.preHistory (P : Pricing Ω x0) (t : ℝ) : MeasurableSpace Ω :=
  P.history 0 ⊔ ⨆ s ∈ Ico (0 : ℝ) t, P.history s

/-- Sales intensity, zero after sell-out (endnote 7). -/
def Pricing.rate (P : Pricing Ω x0) (lam : ℝ) (f : ℝ → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  if P.sales.stock t ω = 0 then 0 else lam * Fbar f (P.core t ω)

/-- A pricing policy with myopic sales, requirements 1 and 3, but without (1).
Left continuity and all path properties are understood up to indistinguishability. -/
structure IsPricing (P : Pricing Ω x0) (μ : Measure Ω) (lam T : ℝ)
    (f : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  simple : P.sales.IsSimple μ
  joint_price : Measurable (Function.uncurry P.posted)
  history_le : ∀ t ∈ Icc (0 : ℝ) T, P.history t ≤ ‹MeasurableSpace Ω›
  adapted : ∀ t ∈ Icc (0 : ℝ) T,
    Measurable[P.preHistory t] (P.posted t)
  left_continuous : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) T,
    ContinuousWithinAt (fun s => P.posted s ω) (Icc 0 t) t
  nonnegative : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) T,
    0 < P.sales.stock t ω → 0 ≤ P.core t ω
  intensity : P.sales.HasIntensity μ T P.history (P.rate lam f)

/-- A finite downward change; a future infinite price produces no price drop.
The value is zero when stock was already exhausted at the starting time. -/
def Pricing.drop (P : Pricing Ω x0) (s t : ℝ) (ω : Ω) : ℝ :=
  if P.sales.stock s ω = 0 ∨ P.sales.stock t ω = 0 then 0
  else max (P.core s ω - P.core t ω) 0

/-- The restricted sub-martingale constraint (1), equivalently tested on every
`G_s` event. This representation also handles conditional expectations of nonnegative variables. -/
def Restricted (P : Pricing Ω x0) (μ : Measure Ω) (theta T : ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    ∀ A : Set Ω, MeasurableSet[P.preHistory s] A →
      (∫⁻ ω in A, ENNReal.ofReal (P.drop s t ω) ∂μ) ≤
        ENNReal.ofReal (theta * (t - s)) * μ A

/-- Assumption 2's continuous component, predictable jump coefficient and actual
left derivative. No robustness assumption is hidden in this definition. -/
structure Regular (P : Pricing Ω x0) (μ : Measure Ω) (T B : ℝ)
    (c delta d : ℝ → Ω → ℝ) : Prop where
  continuous_measurable : Measurable (Function.uncurry c)
  jump_measurable : Measurable (Function.uncurry delta)
  derivative_measurable : Measurable (Function.uncurry d)
  continuous_adapted : ∀ t ∈ Icc (0 : ℝ) T, Measurable[P.history t] (c t)
  jump_adapted : ∀ t ∈ Icc (0 : ℝ) T, Measurable[P.history t] (delta t)
  paths : ∀ᵐ ω ∂μ,
    ContinuousOn (fun t => c t ω) (Icc 0 T) ∧
    (∀ t ∈ Icc (0 : ℝ) T,
      ContinuousWithinAt (fun s => delta s ω) (Icc 0 t) t) ∧
    (∀ t ∈ Ioo (0 : ℝ) T,
      (∀ k : Fin x0, P.sales.time k ω ≠ (t : WithTop ℝ)) →
        DifferentiableAt ℝ (fun s => c s ω) t) ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      HasDerivWithinAt (fun s => c s ω) (d t ω) (Icc 0 t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, |d t ω| ≤ B ∧ |delta t ω| ≤ B) ∧
    (∀ t ∈ Icc (0 : ℝ) T, 0 < P.sales.stock t ω →
      P.core t ω = c t ω + P.sales.sumBefore delta t ω)

/-- Exactly the printed local condition (10), tested while stock remains. -/
def LocalCondition (P : Pricing Ω x0) (μ : Measure Ω) (lam theta T : ℝ)
    (f : ℝ → ℝ) (delta d : ℝ → Ω → ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂μ, 0 < P.sales.stock s ω →
    negPart (d s ω) + lam * Fbar f (P.core s ω) * negPart (delta s ω) ≤ theta

/-- Theorem 2's revenue objective, with `∞ · 0 = 0` after stockout. -/
def expectedRevenue (P : Pricing Ω x0) (μ : Measure Ω) (lam T : ℝ)
    (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) T,
    ENNReal.ofReal (if P.sales.stock s ω = 0 then 0
      else lam * P.core s ω * Fbar f (P.core s ω))) ∂μ

/-- Exponential valuations, used only to demonstrate the stockout counterexample. -/
def exampleDensity (v : ℝ) : ℝ := if 0 ≤ v then Real.exp (-v) else 0

/-- One item at the constant price 1 until sale; the sale time is Exp(e⁻¹).
The driving coordinate has distribution `expMeasure 1`. -/
def terminalExample : Pricing ℝ 1 where
  sales := ⟨fun _ e => (e / Real.exp (-1) : ℝ)⟩
  core := fun _ _ => 1

end
end ChenFarias.SimplePolicy.Supplement


