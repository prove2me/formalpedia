-- Prove2me | Definitions.Def_BetaCoskew_ThreeMoment_Model
-- name    : BetaCoskew_ThreeMoment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:47.528679+00:00
-- url     : https://prove2.me/theorems/7a421aab-54c7-46cb-bbfa-2c17455bdbea
-- title:
--   §2–§3.1: rank-dependent utility, equilibrium, pricing function and premiums
-- statement:
--   Let $u$ be a strictly increasing, strictly concave utility on positive wealth, continuously differentiable there, with Inada limits $u'(0+)=+\infty$ and $u'(+\infty)=0$, positive limiting utility, and asymptotic elasticity below one. Let $w$ be a strictly increasing, continuously differentiable probability weighting function on $[0,1]$, with $w(0)=0$ and $w(1)=1$. These are Assumption 1(ii)–(iii).
--
--   For a payoff $X$ with cumulative distribution function $F_X$, its rank-dependent utility is the paper's distributional integral
--
--   $$
--   U(X)=\int_{\mathbb R}u(x)w'(1-F_X(x))\,dF_X(x).
--   $$
--
--   Problem (P′) maximizes this value over measurable, almost-surely nonnegative payoffs satisfying $\mathbb E[\tilde mX]=1$. In equilibrium the market return $\tilde R_M$ is feasible and has at least the RDU value of every eligible competitor. The file also defines $K=\mathbb E[w'(1-F_M(\tilde R_M))u'(\tilde R_M)]$, the normalized pricing function $m(x)=w'(1-F_M(x))u'(x)/((1+r_f)K)$, the closed-form risk premiums $A,B$ of (6)–(7), and the fixed second-order Taylor remainder $\rho$ of $m$ at $1$.
--
--   **Formalization Note** RDU uses the Bochner integral against the payoff law. Equilibrium competitors have integrable RDU objective, positive payoffs almost surely, and continuous CDFs; these conditions ensure the represented objective and endpoint derivatives have their intended values. The denominator in $m$ is defined for all inputs by Lean, and Theorem 2 derives its nonvanishing in equilibrium.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 8–11 and 33–34, §2.1–2.2, §3.1, Assumption 1(ii)–(iii), (2), (3), (6), (7), Appendix A

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Market

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory Filter Topology

/-- Assumption 1(ii), including the Inada limits and asymptotic elasticity. -/
structure UtilityAssumption (u : ℝ → ℝ) : Prop where
  strictMonoOn : StrictMonoOn u (Set.Ioi 0)
  strictConcaveOn : StrictConcaveOn ℝ (Set.Ioi 0) u
  contDiffOn : ContDiffOn ℝ 1 u (Set.Ioi 0)
  inada_zero : Tendsto (deriv u) (𝓝[>] 0) atTop
  inada_top : Tendsto (deriv u) atTop (𝓝 0)
  pos_at_top : ∃ x : ℝ, 0 < x ∧ 0 < u x
  asymp_elasticity : ∃ L : ℝ, L < 1 ∧
    Tendsto (fun x => x * deriv u x / u x) atTop (𝓝 L)

/-- Assumption 1(iii). -/
structure WeightingAssumption (w : ℝ → ℝ) : Prop where
  strictMonoOn : StrictMonoOn w (Set.Icc 0 1)
  contDiffOn : ContDiffOn ℝ 1 w (Set.Icc 0 1)
  zero : w 0 = 0
  one : w 1 = 1

/-- The paper's RDU value, integrated against the law of the payoff. -/
noncomputable def rdu {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (X : Ω → ℝ) : ℝ :=
  ∫ x, u x * deriv w (1 - cdf (P.map X) x) ∂(P.map X)

/-- Ensures that the Bochner integral defining the RDU objective is genuine. -/
def RduIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (X : Ω → ℝ) : Prop :=
  Integrable (fun x => u x * deriv w (1 - cdf (P.map X) x)) (P.map X)

/-- Feasibility for problem (P′), equation (2). -/
def Feasible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (mt X : Ω → ℝ) : Prop :=
  Measurable X ∧ Integrable (fun ω => mt ω * X ω) P ∧
    (∫ ω, mt ω * X ω ∂P) = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ X ω

/-- Equilibrium for (P′): the market return maximizes RDU over feasible payoffs
whose objective is integrable and whose law is continuous and positive. -/
def IsEquilibrium {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (mt RM : Ω → ℝ) : Prop :=
  Feasible P mt RM ∧ RduIntegrable P u w RM ∧
    ∀ X, Feasible P mt X → RduIntegrable P u w X →
      Continuous (cdf (P.map X)) → (∀ᵐ ω ∂P, 0 < X ω) →
      rdu P u w X ≤ rdu P u w RM

/-- The expected product of probability and outcome marginal weights in (3). -/
noncomputable def kernelMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (RM : Ω → ℝ) : ℝ :=
  ∫ ω, deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω) ∂P

/-- Pricing function m(x) of equation (3). -/
noncomputable def mFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (rf : ℝ) (RM : Ω → ℝ) (x : ℝ) : ℝ :=
  deriv w (1 - cdf (P.map RM) x) * deriv u x /
    ((1 + rf) * kernelMean P u w RM)

/-- Closed form of the beta premium A in (6). -/
noncomputable def premA {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (RM : Ω → ℝ) (f : ℝ → ℝ) : ℝ :=
  let p0 := 1 - cdf (P.map RM) 1;
  -(kernelMean P u w RM)⁻¹ *
    (deriv w p0 * iteratedDeriv 2 u 1 -
      iteratedDeriv 2 w p0 * deriv u 1 * f 1)

/-- Closed form of the coskewness premium B in (7). -/
noncomputable def premB {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (RM : Ω → ℝ) (f : ℝ → ℝ) : ℝ :=
  let p0 := 1 - cdf (P.map RM) 1;
  -(kernelMean P u w RM)⁻¹ *
    (deriv w p0 * iteratedDeriv 3 u 1 +
      iteratedDeriv 3 w p0 * deriv u 1 * f 1 ^ 2 -
      iteratedDeriv 2 w p0 *
        (2 * iteratedDeriv 2 u 1 * f 1 + deriv u 1 * deriv f 1))

/-- The fixed second-order Taylor remainder of m at total return 1. -/
noncomputable def rho {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u w : ℝ → ℝ) (rf : ℝ)
    (RM : Ω → ℝ) (x : ℝ) : ℝ :=
  let m := mFun P u w rf RM;
  m (1 + x) - m 1 - deriv m 1 * x - iteratedDeriv 2 m 1 / 2 * x ^ 2

end BetaCoskew.ThreeMoment


