-- Prove2me | Definitions.Def_HedgePSNV_Hedging
-- name    : HedgePSNV_Hedging
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:55.7128+00:00
-- url     : https://prove2.me/theorems/348a00d9-56af-4c54-887a-d055d1e61c6c
-- title:
--   Equivalent martingale measures $\mathcal M_X$, admissible strategies $\mathcal A_X$ and the minimal variance $B(m,P,R)$
-- statement:
--   **Equivalent martingale measures** (EC.7.13):
--   $$
--   \mathcal M_X=\Big\{\bar{\mathbb P}^M\sim\mathbb P:\ \tfrac{d\bar{\mathbb P}^M}{d\mathbb P}\in L^2(\mathbb P),\ X\text{ is a }\bar{\mathbb P}^M\text{-martingale on }[0,T]\Big\},
--   $$
--   probability measures equivalent to $\mathbb P$.
--
--   **Admissible strategies** (EC.7.15): $(\theta,\chi)\in\mathcal A_X$ when $\theta$ is progressively measurable, $\chi=\int_0^\cdot\theta\,dX$ on $[0,T]$ is an adapted gains process, $\chi_T\in L^2(\mathbb P)$, and $\chi$ is a $\bar{\mathbb P}^M$-martingale on $[0,T]$ for every $\bar{\mathbb P}^M\in\mathcal M_X$.
--
--   **Minimal variance** (14):
--   $$
--   B(m,P,R)=\inf\Big\{\mathrm{Var}\big[H_T(P,R)+\chi_T\big]:\ (\theta,\chi)\in\mathcal A_X,\ \mathbb E\big[H_T(P,R)+\chi_T\big]=m\Big\}\in[0,\infty].
--   $$
--
--   $B$ is the objective of problem (15) and of Theorem 2; Theorem 1 computes it.
--
--   **Formalization Note** $B$ is an infimum in $[0,\infty]$ of the extended variance, so an empty feasible set gives $+\infty$, not a default $0$; attainment is part of Theorem 1(i). The strategy is carried with its gains process (the stochastic integral is determined only up to null sets). The paper's "adapted" integrand is taken progressively measurable, the standard requirement for a stochastic integrand. In Lean the value is named `Bval`, since `B` is the Brownian motion.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (13)–(14), pp.13–14; (EC.7.13), (EC.7.15), p.ec29

import Mathlib
import Definitions.Def_HedgePSNV_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

namespace Model

variable {p : Params} {Ω : Type*} [m : MeasurableSpace Ω]

/-- The set `M_X` of equivalent martingale measures with square-integrable density,
arXiv:2201.01026v4, (EC.7.13), p.ec29:
`M_X := {P̄^M ∼ P : dP̄^M/dP ∈ L²(P), X_t is a P̄^M-martingale}` (on `[0, T]`, with respect to
`F`). -/
def MX (M : Model p Ω) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ M.P ∧ M.P ≪ Q ∧
    MemLp (fun ω => (Q.rnDeriv M.P ω).toReal) 2 M.P ∧ IsMartingaleOn p.T M.F Q M.X}

/-- The admissible hedging strategies `A_X`, arXiv:2201.01026v4, (EC.7.15), p.ec29, with the
gains process attached: `(θ, χ) ∈ A_X` when `θ` is progressively measurable with respect to
`F`, `χ = ∫_0^· θ dX` on `[0, T]` (`IsXGains`, "ϑ is X_t-integrable"), `χ_T ∈ L²(P)`, and
`χ` is a `P̄^M`-martingale on `[0, T]` for every `P̄^M ∈ M_X`.

**Formalization Note** The paper's `θ` is "an adapted process" (footnote 6, p.14); it is
taken progressively measurable, the standard requirement for a stochastic integrand. The
gains process `χ` is carried with the strategy, in an `F`-adapted version (the stochastic
integral is adapted; it is determined only up to null sets). -/
def AX (M : Model p Ω) : Set ((ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) :=
  {θχ | IsStronglyProgressive M.F θχ.1 ∧ StronglyAdapted M.F θχ.2 ∧ M.IsXGains θχ.1 θχ.2 ∧
    MemLp (θχ.2 p.T) 2 M.P ∧
    ∀ Q ∈ M.MX, IsMartingaleOn p.T M.F Q θχ.2}

/-- The optimal value of the hedging problem (14), arXiv:2201.01026v4, p.14:
`B(m,P,R) := min_{ϑ ∈ A_X} Var[H_T(P,R) + χ_T(ϑ)]` s.t. `E[H_T(P,R) + χ_T(ϑ)] = m`.

**Formalization Note** The value is an infimum in `ℝ≥0∞` of the extended variance
`evariance`, so an empty feasible set gives `⊤` rather than a junk `0`; attainment of the
minimum is part of Theorem 1, not of the definition. Named `Bval` because `B` is the Brownian
motion of the model. -/
noncomputable def Bval (M : Model p Ω) (mean P R : ℝ) : ℝ≥0∞ :=
  ⨅ θχ ∈ M.AX, ⨅ (_ : ∫ ω, (M.H P R ω + θχ.2 p.T ω) ∂M.P = mean),
    evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P

end Model

end HedgePSNV


