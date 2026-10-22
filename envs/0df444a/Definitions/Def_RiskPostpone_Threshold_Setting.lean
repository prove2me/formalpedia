-- Prove2me | Definitions.Def_RiskPostpone_Threshold_Setting
-- name    : RiskPostpone_Threshold_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:47.352784+00:00
-- url     : https://prove2.me/theorems/68dbd331-4b1a-4b1c-b047-3afaa0844bd6
-- title:
--   Random-yield monopoly under CVaR: yield law, demand, ex ante and responsive profits, Assumption 2 (§3, pp. 6–8; p. 12)
-- statement:
--   A monopoly firm produces one product and sells it to a market with deterministic price-sensitive demand. The model of §3 consists of the following data and assumptions.
--
--   1. **Yield.** Production of $q$ units of input yields $q\xi$ usable units, where the yield factor $\xi$ is a continuous random variable with support $[l,u]$, $0\le l<u\le1$. Its law $\nu$ is a probability measure on $\mathbb R$ with no atoms, $\nu([l,u]^{\mathrm c})=0$, and $\nu((a,b))>0$ for all $l\le a<b\le u$. Write $G(x)=\nu(\xi\le x)$ for the c.d.f., $\mu=\mathbb E[\xi]$ for the mean yield, $G^{-1}(\eta)=\inf\{x:G(x)\ge\eta\}$ for the lower quantile (the value-at-risk of $\xi$ at level $\eta$) and
--   $$
--   g(\eta)=\frac1\eta\int_l^{G^{-1}(\eta)}\xi\,dG(\xi),\qquad \eta\in(0,1],
--   $$
--   for the mean of the lower $\eta$-tail of the yield.
--   2. **Demand.** The demand $d(p)$ is continuous and strictly decreasing on $[0,p_0]$, where $p_0>0$ is the maximal allowable price, $d(p_0)=0$. The inverse demand $p(x)$ satisfies $p(d(p))=p$ for $p\in[0,p_0]$ and $d(p(x))=x$ for $x\in[0,d(0)]$.
--   3. **Cost.** The unit production cost $c$ satisfies $0\le c\le p_0\mu$.
--   4. **Ex ante pricing**, (1): price $p_a\in[0,p_0]$ and quantity $q_a\ge0$ are chosen before the yield realizes; the ex post profit and the objective are
--   $$
--   \pi_a(p_a,q_a)=p_a\min\{d(p_a),q_a\xi\}-cq_a,\qquad \Pi_a(p_a,q_a)=\mathrm{CVaR}_\eta(\pi_a(p_a,q_a)).
--   $$
--   5. **Responsive pricing**, (2): the quantity $q_r\ge0$ is chosen first and the price after the yield realizes;
--   $$
--   \pi_r(q_r)=\max_{p_r\in[0,p_0]}p_r\min\{d(p_r),q_r\xi\}-cq_r,\qquad \Pi_r(q_r)=\mathrm{CVaR}_\eta(\pi_r(q_r)).
--   $$
--   6. **Producing.** At risk level $\eta$ the ex ante firm *produces* if some $p_a\in[0,p_0]$, $q_a\ge0$ has $\Pi_a(p_a,q_a)>0$, and the responsive firm *produces* if some $q_r\ge0$ has $\Pi_r(q_r)>0$. Since $q=0$ gives CVaR $0$, "not producing is optimal" is exactly the negation.
--   7. **Assumption 2** (p. 12): the revenue function $x\mapsto p(x)\,x$ is concave on $[0,d(0)]$.
--
--   These are the objects of the paper's threshold results (Propositions 1–4).
--
--   **Formalization Note** The yield is represented by its law $\nu$ on $\mathbb R$ and every expectation is an integral against $\nu$; the paper's density is not assumed, only an atomless law with full support on $[l,u]$. The choke price $p_0$ is finite (the paper allows $p_0=\infty$). The inverse demand is a second function with both inverse identities on their intervals. The responsive maximum is a supremum over the image of $[0,p_0]$, which is nonempty and bounded, so it is attained. Assumption 2 is stated without "twice differentiable", which no statement uses, and as a separate predicate so that it is assumed exactly where the paper assumes it. Assumption 1 of p. 10 is not part of the model. The quantile and $g$ are only evaluated at $\eta\in(0,1]$.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), pp. 6–8, §3, (1)–(2); p. 12, Assumption 2; p. ec4, g(η)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RiskPostpone_Threshold_CVaR

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- The data of the random-yield monopoly of §3 (Kouvelis–Xiao–Yang, pp. 6–8):
the yield support `[l, u]`, the law `ν` of the yield factor `ξ` (a measure on `ℝ`), the
demand function `d(p)`, the inverse demand `P(x)` (the paper's `p(d) := d⁻¹(p)`), the maximal
allowable (choke) price `p0` and the unit production cost `c`. -/
structure Model where
  l : ℝ
  u : ℝ
  ν : Measure ℝ
  d : ℝ → ℝ
  P : ℝ → ℝ
  p0 : ℝ
  c : ℝ

namespace Model

variable (M : Model)

/-- Mean yield `µ = E[ξ]` (p. 7). -/
noncomputable def mean : ℝ := ∫ ξ, ξ ∂M.ν

/-- The c.d.f. `G(x) = P(ξ ≤ x)` of the yield (p. 7). -/
noncomputable def G (x : ℝ) : ℝ := (M.ν (Iic x)).toReal

/-- The lower quantile `G⁻¹(η) = inf {x : G(x) ≥ η}`, i.e. the value-at-risk of the yield at
level `η` (the published `MultistageStochastic.valueAtRisk`). For `η ∈ (0,1]` and the standing
assumptions the set contains `u` and is bounded below by `l`; for a continuous c.d.f. that is
strictly increasing on `[l,u]` this is the inverse of `G`. Only evaluated at `η ∈ (0,1]`. -/
noncomputable def quantile (η : ℝ) : ℝ := MultistageStochastic.valueAtRisk M.ν (fun ξ => ξ) η

/-- The tail mean `g(η) = (1/η) ∫_l^{G⁻¹(η)} ξ dG(ξ)` (proof of Proposition 2, p. ec4, and of
Proposition 3, p. ec8). Only used at `η ∈ (0,1]`. -/
noncomputable def tailMean (η : ℝ) : ℝ :=
  (1 / η) * ∫ ξ in Icc M.l (M.quantile η), ξ ∂M.ν

/-- Ex post profit under ex ante pricing, (1) p. 8: `π_a(p, q) = p·min{d(p), qξ} − c·q`,
as a function of the yield realization `ξ`. -/
noncomputable def profitA (p q : ℝ) (ξ : ℝ) : ℝ := p * min (M.d p) (q * ξ) - M.c * q

/-- Ex post profit under responsive pricing, (2) p. 8:
`π_r(q) = max_{p ∈ [0, p0]} p·min{d(p), qξ} − c·q`, as a function of `ξ`. The maximum is written
as `sSup` of the image of `[0, p0]`; under the standing assumptions (`d` continuous on the
compact `[0, p0]`) the image is nonempty and bounded, so the `sSup` is the attained maximum. -/
noncomputable def profitR (q : ℝ) (ξ : ℝ) : ℝ :=
  sSup ((fun p => p * min (M.d p) (q * ξ)) '' Icc 0 M.p0) - M.c * q

/-- `Π_a(p, q) = CVaR_η(π_a(p, q))`, (1) p. 8. -/
noncomputable def PiA (η p q : ℝ) : ℝ := cvar M.ν η (M.profitA p q)

/-- `Π_r(q) = CVaR_η(π_r(q))`, (2) p. 8. -/
noncomputable def PiR (η q : ℝ) : ℝ := cvar M.ν η (M.profitR q)

/-- The ex ante firm produces at risk level `η`: some decision `p ∈ [0, p0]`, `q ≥ 0` has
strictly positive CVaR. Since `q = 0` has CVaR `0`, its negation is exactly the paper's
"it is optimal for the firm not to produce". -/
def ProducesExAnte (η : ℝ) : Prop :=
  ∃ p ∈ Icc 0 M.p0, ∃ q : ℝ, 0 ≤ q ∧ 0 < M.PiA η p q

/-- The responsive firm produces at risk level `η`: some `q ≥ 0` has strictly positive CVaR. -/
def ProducesResponsive (η : ℝ) : Prop :=
  ∃ q : ℝ, 0 ≤ q ∧ 0 < M.PiR η q

/-- The yield assumptions of p. 6: `ξ` is a continuous random variable with support `[l, u]`,
`0 ≤ l < u ≤ 1`. The law is a probability measure without atoms, concentrated on `[l, u]`, and
charging every open subinterval of `[l, u]` (full support). A density is not required. -/
structure YieldLaw : Prop where
  l_nonneg : 0 ≤ M.l
  l_lt_u : M.l < M.u
  u_le_one : M.u ≤ 1
  prob : IsProbabilityMeasure M.ν
  noAtoms : NullSingletonClass M.ν
  support : M.ν (Icc M.l M.u)ᶜ = 0
  fullSupport : ∀ a b : ℝ, M.l ≤ a → a < b → b ≤ M.u → 0 < M.ν (Ioo a b)

/-- The standing assumptions of §3 (pp. 6–7): the yield assumptions; a strictly decreasing,
continuous demand on `[0, p0]` with finite choke price `p0 > 0`, `d(p0) = 0`, and inverse
demand `P` on `[0, d(0)]`; and a unit cost `0 ≤ c ≤ p0·µ` (p. 7). -/
structure Standing : Prop extends M.YieldLaw where
  p0_pos : 0 < M.p0
  d_strictAnti : StrictAntiOn M.d (Icc 0 M.p0)
  d_cont : ContinuousOn M.d (Icc 0 M.p0)
  d_p0 : M.d M.p0 = 0
  P_d : ∀ p ∈ Icc 0 M.p0, M.P (M.d p) = p
  d_P : ∀ x ∈ Icc 0 (M.d 0), M.d (M.P x) = x
  c_nonneg : 0 ≤ M.c
  c_le : M.c ≤ M.p0 * M.mean

/-- Assumption 2 (p. 12): the revenue function `x ↦ P(x)·x` is concave on the demand range
`[0, d(0)]`. (The paper also asks for twice differentiability, which no statement here uses.) -/
def Assumption2 : Prop :=
  ConcaveOn ℝ (Icc 0 (M.d 0)) (fun x => M.P x * x)

end Model

end RiskPostpone.Threshold


