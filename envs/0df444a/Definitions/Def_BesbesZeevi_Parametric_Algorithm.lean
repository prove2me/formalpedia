-- Prove2me | Definitions.Def_BesbesZeevi_Parametric_Algorithm
-- name    : BesbesZeevi_Parametric_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:02:30.845364+00:00
-- url     : https://prove2.me/theorems/23a03627-7ff7-433c-8ad0-be89d496c3d0
-- title:
--   Algorithm 2 and its capped expected revenue
-- statement:
--   Algorithm 2 devotes $\tau$ units of time to $k$ test prices, each for $\Delta=\tau/k$. Its normalized count increments give $\widehat d_i$ and $\widehat\theta=g(\widehat d)$. It then posts the larger of a revenue-maximizing price and a demand-matching price chosen at $\widehat\theta$.
--
--   $$\widehat p=\max\{p^u(\widehat\theta),p^c(\widehat\theta)\},\qquad R_n^\pi=1-\frac{J_n^\pi}{J_n^D}.$$
--
--   Sales stop at $\lfloor nx\rfloor$ units. Expected revenue is the nonnegative integral of the sum of prices times capped phase sales. **Formalization Note** The optimizer selections are measurable and satisfy the max/min properties at every $\theta\in\Theta$. Counts used to form the estimate remain uncapped after a stock-out, but all later capped sales are zero. This represents the same realized revenue as stopping the algorithm at that point.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 14 (PDF p. 16), Algorithm 2; p. 15 (PDF p. 17), Eq. (16); p. 32 (PDF p. 34), Eq. (A-17)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Model

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Measurable choices of the two optimizers in Algorithm 2. All maximizer and
minimizer conditions hold over the continuous interval of admissible prices. -/
structure OptimizerSelection {k : ℕ} (D : Market) (F : Family k D) where
  pu : (Fin k → ℝ) → ℝ
  pc : (Fin k → ℝ) → ℝ
  pu_measurable : Measurable pu
  pc_measurable : Measurable pc
  pu_range : ∀ θ ∈ F.Θ, pu θ ∈ Set.Icc D.pLo D.pHi
  pc_range : ∀ θ ∈ F.Θ, pc θ ∈ Set.Icc D.pLo D.pHi
  pu_max : ∀ θ ∈ F.Θ, ∀ p ∈ Set.Icc D.pLo D.pHi,
    p * F.demand p θ ≤ pu θ * F.demand (pu θ) θ
  pc_min : ∀ θ ∈ F.Θ, ∀ p ∈ Set.Icc D.pLo D.pHi,
    |F.demand (pc θ) θ - D.x / D.T| ≤ |F.demand p θ - D.x / D.T|

/-- The deterministic price from Lemma 1. -/
noncomputable def pD {k : ℕ} {D : Market} {F : Family k D}
    (S : OptimizerSelection D F) (θ : Fin k → ℝ) : ℝ :=
  max (S.pu θ) (S.pc θ)

/-- The `k` equal learning intervals of Algorithm 2 have length `τ/k`. -/
noncomputable def delta (k : ℕ) (τ : ℝ) : ℝ := τ / (k : ℝ)

/-- Cumulative Poisson clock at the end of the first `i` test-price intervals. -/
noncomputable def learningClock {k : ℕ} {D : Market} (F : Family k D)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (i : Fin (k + 1)) : ℝ :=
  ∑ j : Fin k, if j.val < i.val then
    (n : ℝ) * F.demand (F.testPrice j) θ * delta k τ else 0

/-- The uncapped observed demand rate at test price `i`, normalized by market size. -/
noncomputable def estimate {k : ℕ} {D : Market} (F : Family k D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (ω : Ω) (i : Fin k) : ℝ :=
  ((N.count (learningClock F n θ τ i.succ) ω -
    N.count (learningClock F n θ τ (Fin.castSucc i)) ω : ℕ) : ℝ) /
      ((n : ℝ) * delta k τ)

/-- Estimated parameter `g(d̂)` from Step 2(c) of Algorithm 2. -/
noncomputable def thetaHat {k : ℕ} {D : Market} (F : Family k D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (ω : Ω) : Fin k → ℝ :=
  F.g (estimate F N n θ τ ω)

/-- The Step 3 price, with measurable optimizer selections. -/
noncomputable def priceHat {k : ℕ} {D : Market} (F : Family k D)
    (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (ω : Ω) : ℝ :=
  pD S (thetaHat F N n θ τ ω)

/-- The inventory in whole units. It equals `nx` whenever `nx` is an integer. -/
noncomputable def cap (D : Market) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * D.x)

/-- End of the pricing-phase Poisson clock, with the price learned from the first phase. -/
noncomputable def finalClock {k : ℕ} {D : Market} (F : Family k D)
    (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (ω : Ω) : ℝ :=
  learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩ +
    (n : ℝ) * F.demand (priceHat F S N n θ τ ω) θ * (D.T - τ)

/-- Algorithm 2 revenue on one Poisson path: every increment is capped by the
initial inventory, including the learning increments. -/
noncomputable def pathRevenue {k : ℕ} {D : Market} (F : Family k D)
    (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) (ω : Ω) : ℝ :=
  (∑ i : Fin k, F.testPrice i *
    (((min (N.count (learningClock F n θ τ i.succ) ω) (cap D n) -
       min (N.count (learningClock F n θ τ (Fin.castSucc i)) ω) (cap D n) : ℕ) : ℝ))) +
  priceHat F S N n θ τ ω *
    (((min (N.count (finalClock F S N n θ τ ω) ω) (cap D n) -
       min (N.count (learningClock F n θ τ ⟨k, Nat.lt_succ_self k⟩) ω)
         (cap D n) : ℕ) : ℝ))

/-- Expected revenue under Algorithm 2, represented by a nonnegative integral. -/
noncomputable def jPolicy {k : ℕ} {D : Market} (F : Family k D)
    (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (pathRevenue F S N n θ τ ω) ∂P).toReal

/-- Equation (16) in the market scaled according to (11). -/
noncomputable def regret {k : ℕ} {D : Market} (F : Family k D)
    (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P)
    (n : ℕ) (θ : Fin k → ℝ) (τ : ℝ) : ℝ :=
  1 - jPolicy F S N n θ τ / jDetScaled D F θ n

end BesbesZeevi.Parametric


