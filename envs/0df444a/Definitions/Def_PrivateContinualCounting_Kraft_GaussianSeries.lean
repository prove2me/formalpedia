-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_GaussianSeries
-- name    : PrivateContinualCounting_Kraft_GaussianSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:34.22748+00:00
-- url     : https://prove2.me/theorems/0cc4e2a2-8119-4737-a74b-26c81a7c7567
-- title:
--   Independent Gaussian seeds and L² decoder sums
-- statement:
--   Let $I$ be a countable index set. The seed space is $\mathbb R^I$ with the product of standard real Gaussian probability measures, so its coordinate functions $Z_i$ are independent and have law $N(0,1)$. For decoder coefficients $L_{t,i}$, a Gaussian series realization supplies a measurable square-integrable random variable $W_t$ at every time satisfying
--   $$\lim_{J\uparrow I}\left\|\sum_{i\in J}L_{t,i}Z_i-W_t\right\|_{L^2}=0,$$
--   where $J$ ranges over finite subsets. This specifies the actual random sum without evaluating a divergent real series. It is a general probability interface used by the counter model; it assumes no variance bound or analytic identity.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 6, PDF p. 8, §§2.1–2.2, Definition 2.1 (countably indexed Gaussian sums)

import Mathlib

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Canonical stream-independent seed: countably many independent N(0,1) coordinates. -/
noncomputable def gaussianSeed (I : Type) : Measure (I → ℝ) :=
  Measure.infinitePi (fun _ : I => gaussianReal 0 1)

/-- A measurable representative of the L² sum of each square-summable decoder row.
The finite-subset net makes this independent of an enumeration of the countable index set.
No variance, privacy or accuracy assertion is part of this data. -/
structure GaussianSeries (I : Type) [Countable I] (L : ℕ → I → ℝ) where
  value : ℕ → (I → ℝ) → ℝ
  measurable : ∀ t, Measurable (value t)
  square_integrable : ∀ t, MemLp (value t) 2 (gaussianSeed I)
  l2_limit : ∀ t, Tendsto
    (fun s : Finset I => eLpNorm
      (fun ω => (∑ i ∈ s, L t i * ω i) - value t ω) 2 (gaussianSeed I))
    atTop (nhds 0)

end PrivateContinualCounting.Kraft


