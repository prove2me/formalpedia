-- Prove2me | Definitions.Def_MultimodalPricing_Regret_LocalBandit
-- name    : MultimodalPricing_Regret_LocalBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:02:23.951208+00:00
-- url     : https://prove2.me/theorems/f204a5ab-6025-463b-8be5-50f3eb275c3e
-- title:
--   BiasedLinearBandit ridge estimate and local transitions
-- statement:
--   For an interval $[a,b]$ and dimension $k$, use $\phi(p)=(1,p-a,\ldots,(p-a)^{k-1})$. For an ordered history $h$, define $\Lambda=I+\sum_{(p,d)\in h}\phi(p)\phi(p)^\top$ and $\widehat\theta=\Lambda^{-1}\sum_{(p,d)\in h}d\phi(p)$. Repeated pairs contribute repeatedly. The positive identity regularization makes this the unique ridge minimizer.
--
--   For $n=|h|>0$, let $\gamma=C\sqrt k+\Delta\sqrt n+\sqrt{2k\log(4kn/\delta)}+2$. The uncertainty is $\sqrt{\phi(p)^\top\Lambda^{-1}\phi(p)}$. A local output maximizes $p\min\{1,\widehat\theta^\top\phi(p)+\gamma\sqrt{\phi(p)^\top\Lambda^{-1}\phi(p)}+\Delta\}$ over all real prices in $[a,b]$. There is no lower clipping. On empty history, any price in the interval is admitted because the source does not define its logarithm there. A local run applies these transitions to successive prefixes starting empty. All maximizing ties and all first-call completions are covered.
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Algorithms 1–2, printed/PDF p. 11; companion, p. 32

import Definitions.Def_MultimodalPricing_Regret_Smooth
import Definitions.Def_MultimodalPricing_Regret_Sequential

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MultimodalPricing.Regret

/-- Centered monomial features from Algorithm 2, not the uncentered p. 13 typo. -/
def feature (k : ℕ) (a p : ℝ) : Fin k → ℝ := fun i => (p - a) ^ i.val

/-- I plus the sum of all observed outer products, including repeated samples. -/
def design (k : ℕ) (a : ℝ) (h : History) : Matrix (Fin k) (Fin k) ℝ :=
  1 + (h.map (fun z => vecMulVec (feature k a z.1) (feature k a z.1))).sum

/-- The unique ridge minimizer, using the everywhere positive-definite design. -/
def estimate (k : ℕ) (a : ℝ) (h : History) : Fin k → ℝ :=
  (design k a h)⁻¹ *ᵥ (h.map (fun z => z.2 • feature k a z.1)).sum

/-- The numerical radius is used only on nonempty histories. -/
def radius (k n : ℕ) (C Δ δ : ℝ) : ℝ :=
  C * Real.sqrt k + Δ * Real.sqrt n +
    Real.sqrt (2 * k * Real.log (4 * k * n / δ)) + 2

/-- Local uncertainty at a real price. -/
def uncertainty (k : ℕ) (a : ℝ) (h : History) (p : ℝ) : ℝ :=
  Real.sqrt (feature k a p ⬝ᵥ ((design k a h)⁻¹ *ᵥ feature k a p))

/-- Algorithm 2's optimistic revenue, with only the printed upper clipping. -/
def upperReward (k : ℕ) (a C Δ δ : ℝ) (h : History) (p : ℝ) : ℝ :=
  p * min 1 (estimate k a h ⬝ᵥ feature k a p +
    radius k h.length C Δ δ * uncertainty k a h p + Δ)

/-- Every first price is allowed where the source leaves log(0) undefined.
After the first call the output is a genuine maximizer over the whole interval. -/
def LocalChoice (k : ℕ) (a b C Δ δ : ℝ) (h : History) (p : ℝ) : Prop :=
  p ∈ Set.Icc a b ∧
  (h ≠ [] → ∀ q ∈ Set.Icc a b,
    upperReward k a C Δ δ h q ≤ upperReward k a C Δ δ h p)

/-- Consecutive local calls start at the empty history and append every observation. -/
def LocalRun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (t k : ℕ) (a b C Δ δ : ℝ) (O : Observation Ω) : Prop :=
  ∀ᵐ ω ∂μ, ∀ n < t,
    LocalChoice k a b C Δ δ (history O.price O.demand n ω) (O.price n ω)

end MultimodalPricing.Regret


