-- Prove2me | Definitions.Def_RiskAverseConsistency_trueObjective
-- name    : RiskAverseConsistency_trueObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:13.762862+00:00
-- url     : https://prove2.me/theorems/38a03d08-7d2f-4eb5-bf64-73948990c2ae
-- title:
--   Objective of the risk-averse problem (8)
-- statement:
--   Let $f:Y_0\times\Xi\to\mathbb R$, let $\xi:\Omega\to\Xi$ be a random element, $F(y)(\omega):=f(y,\xi(\omega))$ as in (9), $\mathbf B:Z\to Y$ linear, $\wp:Z\to[0,\infty)$ and $\mathcal R:L^p(\Omega,\mathcal F,P)\to\mathbb R$. The objective of problem (8) is
--
--   $$
--   z\ \longmapsto\ \mathcal R[F(\mathbf Bz)]+\wp(z),
--   \qquad\text{and (8) is}\qquad \min_{z\in Z_{\mathrm{ad}}}\ \mathcal R[F(\mathbf Bz)]+\wp(z).
--   $$
--
--   **Formalization Note** The real value is cast to `EReal` so that $m^*$ and $\mathscr S$ are `optimalValue` and `solutionSet` of this function over $Z_{\mathrm{ad}}$.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, pp.8–9, (8)–(9)

import Mathlib
import Definitions.Def_RiskAverseConsistency_riskOf

open MeasureTheory

namespace RiskAverseConsistency

/-- The objective of the risk-averse problem (8): `z ↦ ℛ[F(Bz)] + ℘(z)`, where
`F(y)(ω) := f(y, ξ(ω))` as in (9).

Milz, Surowiec, arXiv:2207.14756v2, (8)–(9), p.8.

Formalization Note: the value is real and is cast to `EReal` so that the optimal value and
solution sets of (8) are computed with `optimalValue`, `solutionSet` and `epsSolutionSet`. `ℛ` is
applied through `riskOf`; `F(Bz) ∈ Lᵖ` for `z ∈ Z_ad` under Assumption 10. -/
noncomputable def trueObjective {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] {p : ENNReal}
    {P : Measure Ω} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    (ℛ : Lp ℝ p P → ℝ) (ξ : Ω → Ξ) (f : Y → Ξ → ℝ) (B : Z →ₗ[ℝ] Y) (φ : Z → ℝ) :
    Z → EReal :=
  fun z => ((riskOf ℛ (fun ω => f (B z) (ξ ω)) + φ z : ℝ) : EReal)

end RiskAverseConsistency


