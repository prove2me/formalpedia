-- Prove2me | Definitions.Def_SkipListConc_geom0
-- name    : SkipListConc_geom0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:03.748198+00:00
-- url     : https://prove2.me/theorems/ade96a10-58b7-4d47-b0eb-5ca1024f844d
-- title:
--   Shifted geometric law $\mathrm{Geom}_0(1-p)$
-- statement:
--   Fix $0<p<1$. The **shifted geometric law** $\mathrm{Geom}_0(1-p)$ is the probability distribution on $\{0,1,2,\dots\}$ with
--   $$
--   \Pr[G=g]=(1-p)\,p^{g},\qquad \Pr[G\ge g]=p^{g},\qquad g\ge 0 .
--   $$
--   It is the terminal geometric component that every promotion of the counter-free skip list adds to an item's height.
--
--   **Formalization Note** A measure on $\mathbb N$ written as a sum of weighted Dirac masses; in Mathlib's convention it is `geometricMeasure` with success probability $1-p$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.5

import Mathlib

open MeasureTheory

namespace SkipListConc

/-- The shifted geometric law `Geom₀(1 − p)` on `{0, 1, 2, …}` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §1.1, p.5): `Pr[G = g] = (1 − p) p^g` for `g ≥ 0`, so `Pr[G ≥ g] = p^g`.

**Formalization Note** A measure on `ℕ` written as a sum of weighted Dirac masses. It is a
probability measure for `0 < p < 1`. In Mathlib's convention it is `geometricMeasure` with success
probability `1 − p`. -/
noncomputable def geom0 (p : ℝ) : Measure ℕ :=
  Measure.sum (fun g : ℕ => ENNReal.ofReal ((1 - p) * p ^ g) • Measure.dirac g)

end SkipListConc


