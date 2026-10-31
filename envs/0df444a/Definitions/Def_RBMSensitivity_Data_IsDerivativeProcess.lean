-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsDerivativeProcess
-- name    : RBMSensitivity_Data_IsDerivativeProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:33:22.926149+00:00
-- url     : https://prove2.me/theorems/31d46c00-1cf4-4c84-af7b-77e790e446b4
-- title:
--   Definition 2.10: derivative process along an RBM
-- statement:
--   Suppose Assumption 2.2 holds, and that $Z^\alpha$ is an RBM associated with $\alpha$ and driving Brownian motion $W$. A **derivative process along $Z^\alpha$** is a $J$-dimensional RCLL $\{\mathcal F_t\}$-adapted process $\mathcal J^\alpha$ such that a.s. for all $t\ge 0$, $\mathcal J^\alpha(t)\in\mathbb H_{Z^\alpha(t)}$ and
--   $$\mathcal J^\alpha(t)=\mathcal J^\alpha(0)+b'(\alpha)t+\sigma'(\alpha)W(t)+R'(\alpha)L^\alpha(t)+\mathcal K^\alpha(t),$$
--   where $\mathcal K^\alpha$ is a $J$-dimensional RCLL $\{\mathcal F_t\}$-adapted process such that a.s. $\mathcal K^\alpha(0)=0$ and for all $0\le s<t<\infty$,
--   $$\mathcal K^\alpha(t)-\mathcal K^\alpha(s)\in\mathrm{span}\Big[\bigcup_{u\in(s,t]}d(\alpha,Z^\alpha(u))\Big].$$
--
--   The right-continuous regularization of the pathwise derivative of the RBM in $\alpha$ is such a process, and (2.8) is the formal linearization of the equation of the RBM.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Definition 2.10, (2.8), p.7

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_RBMSensitivity_Data_localTime
import Definitions.Def_RBMSensitivity_Data_sigmaDeriv
import Definitions.Def_RBMSensitivity_Data_RDeriv
import Definitions.Def_RBMSensitivity_Data_bDeriv
import Definitions.Def_RBMSensitivity_Data_spanAlong
import Definitions.Def_RBMSensitivity_SimpleCone_H
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- Definition 2.10: arXiv:1907.00472v2, (2.8), p.7. A derivative process along `Z`: a `J`-dimensional
RCLL `{F_t}`-adapted process `𝒥` such that a.s. for all `t ≥ 0`, `𝒥(t) ∈ H_{Z(t)}` and
`𝒥(t) = 𝒥(0) + b'(α)t + σ'(α)W(t) + R'(α)L(t) + K(t)`, where `K` is a `J`-dimensional RCLL
`{F_t}`-adapted process such that a.s. `K(0) = 0` and for all `0 ≤ s < t < ∞`,
`K(t) - K(s) ∈ span[⋃_{u ∈ (s,t]} d(α, Z(u))]`.

**Formalization Note.** `L` is `Data.localTime`. The definition presupposes Assumption 2.2, as the
paper does, and that `Z` is an RBM. Both are hypotheses wherever this predicate is used. -/
structure Data.IsDerivativeProcess {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : Data J)
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → E J) (α : ℝ)
    (Z 𝒥 : ℝ≥0 → Ω → E J) : Prop where
  adapted : Adapted 𝓕 𝒥
  rcll : ∀ᵐ ω ∂P, IsRCLL fun t => 𝒥 t ω
  exists_correction : ∃ K : ℝ≥0 → Ω → E J, Adapted 𝓕 K ∧
    (∀ᵐ ω ∂P, IsRCLL fun t => K t ω) ∧ (∀ᵐ ω ∂P, K 0 ω = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, 𝒥 t ω ∈ D.H (Z t ω) ∧
      𝒥 t ω = 𝒥 0 ω + (t : ℝ) • D.bDeriv α + Matrix.toEuclideanLin (D.sigmaDeriv α) (W t ω) +
        Matrix.toEuclideanLin (D.RDeriv α) (D.localTime W α Z t ω) + K t ω) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → K t ω - K s ω ∈ D.spanAlong α (fun u => Z u ω) s t

end RBMSensitivity


