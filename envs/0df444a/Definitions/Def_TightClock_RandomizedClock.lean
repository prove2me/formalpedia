-- Prove2me | Definitions.Def_TightClock_RandomizedClock
-- name    : TightClock_RandomizedClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:08:17.704397+00:00
-- url     : https://prove2.me/theorems/3a40fbad-0cf4-4df1-9254-c99de86dfe6d
-- title:
--   Adaptive randomized clock auction
-- statement:
--   A **randomized clock** for $\mathcal F$ consists of a probability space $(\Omega,P)$ of public random seeds and, for each seed $\omega$, a valid deterministic clock $\sigma_\omega$. Welfare at any fixed nonnegative profile is required to be a measurable function of the seed.
--
--   **Formalization Note** The seed space lives in `Type`. Welfare at a nonnegative profile is bounded by the first best, so measurability makes it integrable. Without that field, a non-measurable map would have Bochner integral $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, pp.13–14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_TightClock_IsValidClock
import Definitions.Def_TightClock_clockWelfare

set_option autoImplicit false

namespace TightClock

/-- An adaptive randomized clock auction: a probability space of public seeds, and a valid deterministic
clock for each seed. Afshinmehr et al., manuscript (STOC 2027 submission), §3, pp.13–14 (PDF 16–17).

**Formalization Note** The seed space lives in `Type`. The field `measurable` is what makes the expected
welfare a genuine integral: welfare is bounded by the first best on nonnegative profiles, so it is then
integrable (the Bochner integral would be junk `0` otherwise). -/
structure RandomizedClock {n : ℕ} (F : Finset (Finset (Fin n))) where
  /-- The space of public random seeds. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the seed. -/
  P : MeasureTheory.Measure Ω
  /-- The law is a probability measure. -/
  [isProb : MeasureTheory.IsProbabilityMeasure P]
  /-- The deterministic clock played under each seed. -/
  σ : Ω → Strategy n
  /-- Each of them obeys the rules. -/
  valid : ∀ ω, IsValidClock F (σ ω)
  /-- Welfare at a fixed nonnegative profile is a measurable function of the seed. -/
  measurable : ∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i) → Measurable (fun ω => clockWelfare (σ ω) v)

attribute [instance] RandomizedClock.mΩ RandomizedClock.isProb

end TightClock


