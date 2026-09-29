-- Prove2me | Definitions.Def_HighDimStat_MetricEntropy_EntropyIntegral
-- name    : HighDimStat_MetricEntropy_EntropyIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:34.764197+00:00
-- url     : https://prove2.me/theorems/cd384721-6462-4649-9070-542b67c24c41
-- title:
--   The delta-truncated Dudley entropy integral J(delta; D)
-- statement:
--   The **$\delta$-truncated Dudley entropy integral** of Eq. (5.45), the key quantity in
--   Dudley's chaining bound (Theorem 5.22):
--
--   $$
--   J(\delta; D) \;:=\; \int_\delta^D \sqrt{\log N(u; T)}\, du,
--   $$
--
--   where $N(u;T)$ is the $u$-covering number of $T$ with respect to $\rho_X$ (`CoveringNumber`).
--
--   **Formalization Note** Realized as a Mathlib interval integral $\int_\delta^D$, which follows
--   the usual analytic sign convention $\int_a^b = -\int_b^a$ when $\delta > D$; every use of this
--   definition in this mission's theorems has $\delta \le D$, matching the book's own domain
--   $\delta \in [0,D]$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 139 (PDF p. 159), Eq. (5.45)

import Mathlib
import Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber

namespace HighDimStat.MetricEntropy

/-- The `δ`-truncated Dudley entropy integral `J(δ; D) := ∫_δ^D √(log N(u; T)) du` of Wainwright,
*High-Dimensional Statistics* (2019), Eq. (5.45), p. 139, where `N(u; T)` is the `u`-covering
number of `T`. Realized as a Mathlib interval integral over `[δ, D]` (with the usual convention
that it is the negative of the integral over `[D, δ]` if `δ > D`, matching the standard analytic
convention for `∫ᵦᵃ` used throughout the book). -/
noncomputable def EntropyIntegral (T : Type*) [Fintype T] [PseudoMetricSpace T] (δ D : ℝ) : ℝ :=
  ∫ u in δ..D, Real.sqrt (Real.log (CoveringNumber T u))

end HighDimStat.MetricEntropy


