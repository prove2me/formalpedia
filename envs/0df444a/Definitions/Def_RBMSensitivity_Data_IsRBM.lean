-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsRBM
-- name    : RBMSensitivity_Data_IsRBM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:59.280884+00:00
-- url     : https://prove2.me/theorems/d8ea9520-f74f-421f-8b4f-0efe40bd5735
-- title:
--   Definition 2.1: reflected Brownian motion
-- statement:
--   Given $\alpha\in U$ and a $J$-dimensional $\{\mathcal F_t\}$-Brownian motion $W$, an **RBM associated with parameter $\alpha$ and driving Brownian motion $W$** is a $J$-dimensional continuous $\{\mathcal F_t\}$-adapted process $Z^\alpha$ such that a.s. for all $t\ge 0$, $Z^\alpha(t)\in G$ and
--   $$Z^\alpha(t)=Z^\alpha(0)+b(\alpha)t+\sigma(\alpha)W(t)+Y^\alpha(t),$$
--   where $Y^\alpha$ is a $J$-dimensional continuous $\{\mathcal F_t\}$-adapted process that a.s. satisfies, for all $0\le s<t<\infty$,
--   $$Y^\alpha(t)-Y^\alpha(s)\in\mathrm{cone}\Big[\bigcup_{u\in(s,t]}d(\alpha,Z^\alpha(u))\Big].$$
--   $Y^\alpha$ is the **constraining process**.
--
--   This is the central object of the mission. The whole statement is pathwise, so no stochastic integral is involved.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 2.1, (2.3), p.5

import Mathlib
import Definitions.Def_RBMSensitivity_IsFBrownian
import Definitions.Def_RBMSensitivity_Data_sigma
import Definitions.Def_RBMSensitivity_Data_coneAlong
import Definitions.Def_RBMSensitivity_SimpleCone_G
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Definition 2.1: arXiv:1907.00472v2, (2.3), p.5. An RBM associated with parameter `α` and driving
Brownian motion `W`: a `J`-dimensional continuous `{F_t}`-adapted process `Z` such that a.s. for all
`t ≥ 0`, `Z(t) ∈ G` and `Z(t) = Z(0) + b(α)t + σ(α)W(t) + Y(t)`, where `Y` is a `J`-dimensional
continuous `{F_t}`-adapted process that a.s. satisfies, for all `0 ≤ s < t < ∞`,
`Y(t) - Y(s) ∈ cone[⋃_{u ∈ (s,t]} d(α, Z(u))]`.

**Formalization Note.** This is the extended form of the paper, not an integral complementarity
condition. Continuity of paths is almost sure, as for `IsFBrownian`. -/
structure Data.IsRBM {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : Data J)
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → E J) (α : ℝ)
    (Z : ℝ≥0 → Ω → E J) : Prop where
  adapted : Adapted 𝓕 Z
  continuous : ∀ᵐ ω ∂P, Continuous fun t => Z t ω
  exists_constraining : ∃ Y : ℝ≥0 → Ω → E J, Adapted 𝓕 Y ∧
    (∀ᵐ ω ∂P, Continuous fun t => Y t ω) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω ∈ D.G ∧
      Z t ω = Z 0 ω + (t : ℝ) • D.b α + Matrix.toEuclideanLin (D.sigma α) (W t ω) + Y t ω) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → Y t ω - Y s ω ∈ D.coneAlong α (fun u => Z u ω) s t

end RBMSensitivity


