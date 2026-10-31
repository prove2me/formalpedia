-- Prove2me | Definitions.Def_ReservationPolicy_noise
-- name    : ReservationPolicy_noise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:21.131992+00:00
-- url     : https://prove2.me/theorems/450c1d5f-2ad6-47a5-88a7-c5c6bffe23e3
-- title:
--   Test noise $\varepsilon\sim U[-1,1]$
-- statement:
--   A student's ability is her mean ability plus a noise term $\varepsilon$ uniformly distributed on $[-1,1]$. This is the law of $\varepsilon$: normalized Lebesgue measure on $[-1,1]$.
--
--   Every probability and conditional expectation of the model is computed from this measure.
--
--   **Formalization Note** The measure is written directly as Lebesgue measure restricted to $[-1,1]$ and scaled by $\tfrac12$, so it has total mass $1$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (1), p.8

import Mathlib

open MeasureTheory

namespace ReservationPolicy

/-- The law of the test noise `ε ∼ U[−1,1]`: Lebesgue measure on `[−1, 1]`, scaled by `1/2` so that it
has mass `1`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (1), p.8 (PDF 8). -/
noncomputable def noise : Measure ℝ :=
  (2 : ENNReal)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

end ReservationPolicy


