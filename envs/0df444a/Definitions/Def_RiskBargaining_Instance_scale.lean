-- Prove2me | Definitions.Def_RiskBargaining_Instance_scale
-- name    : RiskBargaining_Instance_scale
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:51.989962+00:00
-- url     : https://prove2.me/theorems/a44c681e-d975-4b65-8d64-a6d14710a4d3
-- title:
--   The instance with scaled endowments
-- statement:
--   Given an instance $(R,M,\mathcal A)$ and scalars $c_i$, this is the instance with endowments $c_iR_i$ and the same $M$ and $\mathcal A$.
--
--   It is the path along which the correction axiom CONT asks for continuity. It is not in the paper.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.3, p.37 (the operation is not in the paper)

import Mathlib
import Definitions.Def_RiskBargaining_Instance

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The instance `I` with each endowment `R i` replaced by `c i • R i`**, and `M`, `𝒜` unchanged.
Not in the paper: it is the path along which the correction axiom `RiskBargaining.ContScaling` asks for
continuity. Compare Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.3, p.37 ("representing vi ∈ ℝ as limits of rational numbers"). -/
def Instance.scale (I : Instance μ p X ι) (c : ι → ℝ) : Instance μ p X ι where
  R := fun i => c i • I.R i
  M := I.M
  A := I.A
  coherent := I.coherent
  cont_M := I.cont_M

end RiskBargaining


