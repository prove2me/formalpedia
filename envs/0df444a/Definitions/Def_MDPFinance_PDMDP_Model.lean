-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Model
-- name    : MDPFinance_PDMDP_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:04:51.649975+00:00
-- url     : https://prove2.me/theorems/115f1c56-7099-405d-9fa3-5764f37515c0
-- title:
--   A Piecewise Deterministic Markov Decision Model and its control-function spaces (Definition 8.1.1)
-- statement:
--   Definition 8.1.1 introduces the data $(E,U,\mu,\lambda,Q,r,\beta)$ of a **Piecewise Deterministic Markov Decision Model**: $E$ a Borel state space, $U$ a Borel control-action space, the control-function space $A := \{\alpha : \mathbb R_{\ge0} \to U \text{ measurable}\}$ (Eq. (8.1)), a deterministic drift $\mu(x,u)$, a flow $\varphi^\alpha_t(x)$ solving $\dot x_t = \mu(x_t,\alpha_t)$, $x_0=x$ (bundled as *data* satisfying $\varphi_0 = x$, continuity in $(t,x)$, and joint measurability in $(\alpha,x)$ — existence/uniqueness of this ODE solution is the book's own standing assumption on $\mu$, not re-derived here, per this chunk's own pitfall note), a jump-goal kernel $Q$ from $E \times U$ to $E$, a Poisson jump rate $\lambda > 0$, a reward rate $r$, and a discount $\beta \ge 0$. A second flow $\varphi\mathrm{Rel}$ solving the *relaxed* (measure-averaged) ODE for a relaxed control $\alpha : \mathbb R_{\ge0} \to \mathbb P(U)$ is bundled alongside it, consistent with $\varphi$ on point masses, since §8.2's existence proof needs both. The control-function space $A$ and its relaxed enlargement $R$ (Eq. (8.6), p. 249) are realized as subtypes of measurable functions $\mathbb R \to U$ and $\mathbb R \to \mathbb P(U)$.
--
--   **Formalization Note.** The book's own $\sigma$-algebra/topology construction on $A$ (the coarsest making certain integrals measurable, citing Yushkevich (1980)) and the Young topology on $R$ (Remark 8.2.3) are not reconstructed; continuity/compactness hypotheses that need a topology on these spaces are stated directly against the pointwise/product topology on the underlying function types in the theorems that need them (see `MODERATION_NOTES.md`).
--
--   **Moderation note.** The draft's model had no drift `μ`, no ODE for the flow, no measurability of the data and an arbitrary map in place of a Markov kernel `Q`, so the flow `φ` and the relaxed flow were unconstrained functions and the model was not the book's. Now the model carries `μ` (measurable), the ordinary flow `φ_t^α(x) = x + ∫_0^t μ(φ_s^α(x), α_s) ds` (continuous in `t`, `φ_0 = x`, jointly measurable), the relaxed flow `φ^α` with `∫_U μ(·,u) α_s(du)`, agreeing with `φ` on Dirac controls, a Markov kernel `Q` on `E × U`, `λ > 0`, measurable `r`, `β > 0`. Control functions are the measurable `α : ℝ₊ → U` and relaxed controls the measurable `α : ℝ₊ → P(U)`; the Young topology (the coarsest making `α ↦ ∫_0^∞ ∫_U w(t,u) α_t(du) dt` continuous for every Carathéodory `w`) is defined here and used wherever the book says "`R` is a compact metrizable space".
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 243-244, PDF 254-255, Definition 8.1.1 (corrected from `statements.jsonl`'s mislabeled citation-footer text); p. 249-250, PDF 260-261 for the relaxed control space R (Eq. (8.6))

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

/-- The control-function space `A := {α : ℝ₊ → U measurable}` (Bäuerle–Rieder, Eq. (8.1)),
rendered as the subtype of measurable functions `ℝ → U`. -/
def ControlFn (U : Type*) [MeasurableSpace U] := {α : ℝ → U // Measurable α}

instance instMeasurableSpaceControlFn (U : Type*) [MeasurableSpace U] :
    MeasurableSpace (ControlFn U) :=
  Subtype.instMeasurableSpace

/-- The relaxed control-function space `R := {α : ℝ₊ → ℙ(U) measurable}` (Bäuerle–Rieder,
Eq. (8.6), p. 249, PDF 260). -/
def RelaxedControlFn (U : Type*) [MeasurableSpace U] :=
  {α : ℝ → ProbabilityMeasure U // Measurable α}

instance instMeasurableSpaceRelaxedControlFn (U : Type*) [MeasurableSpace U] :
    MeasurableSpace (RelaxedControlFn U) :=
  Subtype.instMeasurableSpace

/-- The strong Carathéodory functions `Car(ℝ₊ × U)` (Bäuerle–Rieder, Remark 8.2.3, p. 249, PDF
260): continuous in `u`, measurable in `t`, with `∫_0^∞ max_u |w(t,u)| dt < ∞`. -/
def IsCaratheodory {U : Type*} [MeasurableSpace U] [TopologicalSpace U] (w : ℝ × U → ℝ) : Prop :=
  (∀ t, Continuous fun u => w (t, u)) ∧ (∀ u, Measurable fun t => w (t, u)) ∧
    (∫⁻ t in Set.Ioi (0 : ℝ), ⨆ u, ENNReal.ofReal |w (t, u)|) < ⊤

/-- The **Young topology** on relaxed controls (Bäuerle–Rieder, Remark 8.2.3, p. 249, PDF 260):
the coarsest topology making `α ↦ ∫_0^∞ ∫_U w(t,u) α_t(du) dt` continuous for every
`w ∈ Car(ℝ₊ × U)`. With it `R` is a compact metrizable Borel space and `A` is dense in `R`. -/
noncomputable def youngTopology (U : Type*) [MeasurableSpace U] [TopologicalSpace U] :
    TopologicalSpace (ℝ → ProbabilityMeasure U) :=
  ⨅ w ∈ {w : ℝ × U → ℝ | IsCaratheodory w},
    TopologicalSpace.induced
      (fun α : ℝ → ProbabilityMeasure U =>
        ∫ t in Set.Ioi (0 : ℝ), ∫ u, w (t, u) ∂(α t).toMeasure)
      inferInstance

/-- Definition 8.1.1 (Bäuerle–Rieder, p. 243-244, PDF 254-255). A Piecewise Deterministic Markov
Decision Model consists of `(E,U,μ,λ,Q,r,β)`: `E` the state space (a Borel subset of `ℝ^d`; here
a real normed space, of which `ℝ^d` is the case in the book), `U` a Borel control space, `A` the
control functions, `μ(x,u) ∈ E` the measurable deterministic drift, and for every `α ∈ A` the
unique solution `φ_t^α(x)` of `ẋ_t = μ(x_t,α_t)`, `x_0 = x` — bundled as data `φ` satisfying the
initial value problem in integral (Carathéodory) form, continuous in `t` and measurable in
`(α,x)`; the relaxed flow `φRel` solving `ẋ_t = ∫ μ(x_t,u) α_t(du)` for relaxed controls (Eq.
(8.7)), consistent with `φ` on point masses; `Q` a stochastic kernel from `E × U` to `E`
(jump-goal distribution); `λ > 0` the Poisson jump rate; `r : E × U → ℝ` the measurable reward
rate; `β ≥ 0` the discount rate. The book's own σ-algebra on `A` (the coarsest making
`α ↦ ∫_0^∞ e^{-t} w(t,α_t) dt` measurable) is rendered by the product σ-algebra on `ℝ → U`. -/
structure PDMDPModel (E U : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] where
  μ : E × U → E
  hμ_meas : Measurable μ
  φ : ℝ → (ℝ → U) → E → E
  hφ0 : ∀ α x, φ 0 α x = x
  /-- `φ^α_·(x)` solves `ẋ_t = μ(x_t,α_t)`, `x_0 = x` (integral form). -/
  hφ_ode : ∀ (α : ℝ → U), Measurable α → ∀ x, ∀ t, 0 ≤ t →
    φ t α x = x + ∫ s in (0 : ℝ)..t, μ (φ s α x, α s)
  hφ_cont : ∀ α x, Continuous fun t => φ t α x
  hφ_meas : ∀ t, Measurable fun p : (ℝ → U) × E => φ t p.1 p.2
  /-- The **relaxed** flow, solving `ẋ_t = ∫ μ(x_t,u) α_t(du)`, `x_0 = x` (Eq. (8.7)). -/
  φRel : ℝ → (ℝ → ProbabilityMeasure U) → E → E
  hφRel0 : ∀ α x, φRel 0 α x = x
  hφRel_ode : ∀ (α : ℝ → ProbabilityMeasure U), Measurable α → ∀ x, ∀ t, 0 ≤ t →
    φRel t α x = x + ∫ s in (0 : ℝ)..t, ∫ u, μ (φRel s α x, u) ∂(α s).toMeasure
  hφRel_pt : ∀ t (α : ℝ → U) (_hα : Measurable α) x,
    φRel t (fun s => (⟨Measure.dirac (α s), inferInstance⟩ : ProbabilityMeasure U)) x = φ t α x
  Q : Kernel (E × U) E
  isMarkovQ : IsMarkovKernel Q
  lam : ℝ
  hlam : 0 < lam
  r : E × U → ℝ
  hr_meas : Measurable r
  β : ℝ
  hβ : 0 ≤ β

end MDPFinance.PDMDP


