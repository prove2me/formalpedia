-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanRisk_AVaR
-- name    : BauerleRiederMDP_MeanRisk_AVaR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:20.660784+00:00
-- url     : https://prove2.me/theorems/4b73c072-f5f8-4014-848a-ebde21e8c1fc
-- title:
--   Average-Value-at-Risk $\mathrm{AVaR}_\gamma(X)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $X\in L^1(\Omega,\mathcal F,\mathbb P)$, with positive values rewards and negative values losses. The **Average-Value-at-Risk** of $X$ at level $\gamma\in(0,1)$ is the average of the Value-at-Risk over the levels above $\gamma$:
--
--   $$
--   \mathrm{AVaR}_\gamma(X)=\frac{1}{1-\gamma}\int_\gamma^1 \mathrm{VaR}_u(X)\,du .
--   $$
--
--   It is the risk measure minimized in the mean-risk problem (MR) of §4.7. Its representation as the value of a convex optimization problem, eq. (C.1), is a separate theorem of this mission.
--
--   **Formalization Note** The integral is the Lebesgue integral over the open interval $(\gamma,1)$; the endpoints have measure zero. The book defines $\mathrm{AVaR}_\gamma$ for integrable $X$; the Lean function accepts any $X$ and is only applied to integrable ones.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Example C.2.2 b), p.368 (PDF p.373); §4.7, p.125 (PDF p.139)

import Mathlib
import Definitions.Def_BauerleRiederMDP_MeanRisk_VaR

open MeasureTheory

namespace BauerleRiederMDP.MeanRisk

/-- The Average-Value-at-Risk of a risk `X` at level `γ ∈ (0,1)`, Bäuerle & Rieder (2011),
Example C.2.2 b), p.368 (PDF 373), and §4.7, p.125 (PDF 139):
`AVaR_γ(X) = (1/(1 − γ)) ∫_γ^1 VaR_u(X) du`.

**Formalization Note.** The integral is the Lebesgue (Bochner) integral over `(γ, 1)`; the endpoints
have measure zero. The book defines `AVaR_γ` for `X ∈ L¹`; for such `X` the map `u ↦ VaR_u(X)` is
integrable on `(γ,1)`. The representation as an optimization problem, eq. (C.1), is a theorem
(`example_C_2_2_b`), not the definition. -/
noncomputable def AVaR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : ℝ :=
  (1 - γ)⁻¹ * ∫ u in Set.Ioo γ 1, VaR P u X

end BauerleRiederMDP.MeanRisk


