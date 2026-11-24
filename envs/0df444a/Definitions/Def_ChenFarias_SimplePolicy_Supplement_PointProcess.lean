-- Prove2me | Definitions.Def_ChenFarias_SimplePolicy_Supplement_PointProcess
-- name    : ChenFarias_SimplePolicy_Supplement_PointProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:57:37.498657+00:00
-- url     : https://prove2.me/theorems/afc08c86-aa8a-445e-81bf-ac7b0b5ebc08
-- title:
--   §3, (2) — finite simple counting processes and stochastic intensity
-- statement:
--   A finite simple counting process has at most $n$ events, represented by ordered positive event times $S_1,\ldots,S_n$ on a measurable outcome space. An event time may be $+\infty$, meaning the event never occurs. The post-event count is $N_t=\#\{k:S_k\le t\}$; the pre-event count uses $S_k<t$. Remaining inventory is $X_{t-}=n-N_{t-}$.
--
--   For a probability measure $\mu$, a history $(\mathcal F_t)$ and a nonnegative rate $r$, the intensity predicate is the conditional compensator identity, for every $0\le a\le b\le T$ and every $A\in\mathcal F_a$:
--   $$
--   \mathbb E[\mathbf1_A(N_b-N_a)]=\mathbb E\!\left[\mathbf1_A\int_a^b r_s\,ds\right].
--   $$
--   Finite-event sums implement the Stieltjes integral against $N$. This object is independent of the pricing model; the next definition supplies its particular intensity.
--
--   **Formalization Note** Event times use `Fin n` with labels zero through $n-1$, corresponding to source sales one through $n$. Positive finite times are strictly ordered. `WithTop ℝ` represents nonexistent events. The fallback value extracted from an infinite time is guarded by a strict comparison to a finite horizon, so it is never used. The compensated-count identity uses nonnegative extended integrals and is a definition of intensity, not a revenue identity assumed as an axiom.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1124, (2); p. 1141, endnote 6

import Mathlib

namespace ChenFarias.SimplePolicy.Supplement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A finite simple counting process, represented by its ordered possible event times.
`⊤` means that the event never occurs. This object has no pricing data. -/
structure FinitePointProcess (Ω : Type*) (n : ℕ) where
  time : Fin n → Ω → WithTop ℝ

variable {Ω : Type*} {n : ℕ}

/-- Number of events up to and including time `t`. -/
def FinitePointProcess.count (q : FinitePointProcess Ω n) (t : ℝ) (ω : Ω) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun k => q.time k ω ≤ (t : WithTop ℝ))).card

/-- Number of events strictly before `t`. -/
def FinitePointProcess.countBefore (q : FinitePointProcess Ω n) (t : ℝ) (ω : Ω) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun k => q.time k ω < (t : WithTop ℝ))).card

/-- The remaining inventory just before `t`, including a unit sold exactly at `t`. -/
def FinitePointProcess.stock (q : FinitePointProcess Ω n) (t : ℝ) (ω : Ω) : ℕ :=
  n - q.countBefore t ω

/-- The finite-event Stieltjes sum. The value selected from `⊤` is never used. -/
def FinitePointProcess.sumBefore (q : FinitePointProcess Ω n)
    (h : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin n, if q.time k ω < (t : WithTop ℝ)
    then h ((q.time k ω).untopD 0) ω else 0

/-- Positive, ordered event times, with no simultaneous finite events. -/
def FinitePointProcess.IsSimple [MeasurableSpace Ω] (q : FinitePointProcess Ω n)
    (μ : Measure Ω) : Prop :=
  (∀ k, Measurable (q.time k)) ∧
  ∀ᵐ ω ∂μ, (∀ k, (0 : WithTop ℝ) < q.time k ω) ∧
    (∀ i j : Fin n, i < j → q.time i ω ≤ q.time j ω) ∧
    (∀ i j : Fin n, i < j → q.time j ω ≠ ⊤ → q.time i ω < q.time j ω)

/-- Stochastic intensity, in its defining conditional compensator form. The equality
on every event in the history at `a` says that `N - ∫ rate` is a martingale.
All quantities are nonnegative integrals, so no default Bochner expectation occurs. -/
def FinitePointProcess.HasIntensity [MeasurableSpace Ω] (q : FinitePointProcess Ω n)
    (μ : Measure Ω) (T : ℝ) (history : ℝ → MeasurableSpace Ω)
    (rate : ℝ → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry rate) ∧
  (∀ t ∈ Icc (0 : ℝ) T, Measurable[history t] (rate t)) ∧
  (∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ rate t ω) ∧
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
    ∀ A : Set Ω, MeasurableSet[history a] A →
      (∫⁻ ω in A, ((q.count b ω - q.count a ω : ℕ) : ℝ≥0∞) ∂μ) =
        ∫⁻ ω in A, (∫⁻ s in Ioc a b, ENNReal.ofReal (rate s ω)) ∂μ

end
end ChenFarias.SimplePolicy.Supplement


