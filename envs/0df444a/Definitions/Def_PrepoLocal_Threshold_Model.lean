-- Prove2me | Definitions.Def_PrepoLocal_Threshold_Model
-- name    : PrepoLocal_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:16.011222+00:00
-- url     : https://prove2.me/theorems/9f22ce9f-0642-41db-abf1-0fb68443b4be
-- title:
--   §3–§4.1, pp. 5–10 — single-cycle prepo model: local-spend budget b̂ (1), local shortage S, expected cycle cost C, auxiliary cost Ca, β∗, net-demand fractile
-- statement:
--   This file sets up the single-cycle prepositioning ("prepo") model of Eftekhar, Song and Webster. A humanitarian organization (HO) chooses, at the start of a cost cycle, a prepositioned stock $x$ of a relief item. The cycle ends when the next disaster strikes and its immediate relief period is over.
--
--   **Parameters.** The unit purchase-and-transport cost of prepo is normalized to $c=1$. The other parameters are
--   1. $\alpha$, the cost of a locally purchased unit as a multiple of the prepo cost, with $0<\alpha<1$;
--   2. $i\ge 0$, the holding cost per dollar-period of prepo;
--   3. $v>1$, the cost per unit of unsatisfied demand;
--   4. $b\ge 0$, the initial budget, which bounds the prepo investment ($x\le b$);
--   5. $\gamma\ge 0$, the inflow of funds per period.
--
--   **Random environment.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ live the relief demand $D$, the local supply $Q$, the emergency fund $R$ received when the disaster hits, and the time $T$ until the disaster. All four are measurable, integrable and almost surely nonnegative, and $T$ is independent of the triple $(D,Q,R)$. Write $\mu_D=\mathbb E[D]$ and $\mu_T=\mathbb E[T]$.
--
--   **Local spend and shortage.** After investing $x$ in prepo, the budget available for local spend when the disaster hits at time $T$ is
--   $$
--   \hat b(x,R,T)=b+\gamma T+R-x. \tag{1}
--   $$
--   The HO buys locally first, at most $\min\{D,Q,\hat b/\alpha\}$ units, and the remaining **local shortage** is
--   $$
--   S(x)=\bigl(D-\min\{Q,\hat b(x,R,T)/\alpha\}\bigr)^+ .
--   $$
--   Prepo covers $\min\{x,S(x)\}$ of it and $(S(x)-x)^+$ goes unmet.
--
--   **Costs.** The expected cost of a cycle is
--   $$
--   C(x)=\mathbb E\Bigl[iTx+\alpha\min\Bigl\{D,Q,\frac{b+\gamma T+R-x}{\alpha}\Bigr\}+\min\{x,S(x)\}+v\,(S(x)-x)^+\Bigr],
--   $$
--   and the HO's problem is $\Pi:\ \min_{x\le b}C(x)$. In the **auxiliary model** the local budget constraint is relaxed ($\min\{Q,\hat b/\alpha\}$ is replaced by $Q$), with cost
--   $$
--   C_a(x)=\alpha\mu_D+i\mu_T x+(1-\alpha)\,\mathbb E[(D-Q)^+]+(v-1)\,\mathbb E[(D-Q-x)^+].
--   $$
--   The critical shortage probability is $\beta^*=i\mu_T/(v-1)$.
--
--   **Net-demand fractile.** A number $x_+$ is a value of $\bar F^{-1}_{D-Q}(\beta)$, the generalized inverse of the survival function $\bar F_{D-Q}(y)=\mathbb P(D-Q>y)$ of the net demand, when
--   $$
--   \mathbb P(D-Q>x_+)\le\beta<\mathbb P(D-Q>y)\quad\text{for every }y<x_+,
--   $$
--   or when $\beta\ge1$ and $x_+\le 0$ (for every $\beta\ge1$, the generalized inverse $\inf\{y:\mathbb P(D-Q>y)\le\beta\}$ is $-\infty$, and only $(x_+)^+=0$ enters the results).
--
--   These objects are shared by every statement of the mission: the cost identity, the convexity of $C$, the newsvendor solution of the auxiliary model, and the budget-threshold result (Proposition 2(b)).
--
--   **Formalization Note** All quantities are real numbers and expectations are Bochner integrals; integrability of $D,Q,R,T$ is part of the standing assumptions, so every expectation above is a genuine one. $C$ is defined as the expectation of the first (operational) line of the paper's display on p. 7, not by its closed form, and $C_a$ is the separate expression of p. 9. The paper's densities $f_{DQR}$, $f_T$ are not assumed. The fractile is a predicate on $x_+$, not a closed-form infimum. The independence of $T$ from $(D,Q,R)$ is stated on p. 6 and kept, although no statement of the mission uses it.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), pp. 5–10, §3 (eq. (1), Table 1, display of C(x) on p. 7), §4.1 (display of Ca(x), eq. (4), β∗, p. 9)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- The deterministic parameters of the single-cycle prepo model (§3, pp. 5–7, Table 1),
with the unit prepo cost normalized to `c = 1`:
`al` = α (local cost multiple), `hold` = i (holding cost per dollar-period),
`v` (unit shortage cost), `b` (initial budget), `gam` = γ (inflow of funds per period). -/
structure Params where
  al : ℝ
  hold : ℝ
  v : ℝ
  b : ℝ
  gam : ℝ

/-- Standing assumptions on the parameters (p. 6, Table 1): `0 < α < 1`, `i ≥ 0`, `v > c = 1`,
`b ≥ 0`, `γ ≥ 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.al ∧ P.al < 1 ∧ 0 ≤ P.hold ∧ 1 < P.v ∧ 0 ≤ P.b ∧ 0 ≤ P.gam

/-- The random environment on a sample space `Ω`: demand `D`, local supply `Q`,
emergency fund `R` and time to the next disaster `T` (p. 6, Table 1). -/
structure Env (Ω : Type*) where
  D : Ω → ℝ
  Q : Ω → ℝ
  R : Ω → ℝ
  T : Ω → ℝ

/-- Standing assumptions on the environment (p. 6, Table 1): `μ` is a probability measure;
`D, Q, R, T` are measurable, integrable and almost surely nonnegative; and `T` is independent
of the triple `(D, Q, R)`. -/
def Env.Standing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Env Ω) : Prop :=
  IsProbabilityMeasure μ ∧
  Measurable E.D ∧ Measurable E.Q ∧ Measurable E.R ∧ Measurable E.T ∧
  Integrable E.D μ ∧ Integrable E.Q μ ∧ Integrable E.R μ ∧ Integrable E.T μ ∧
  (∀ᵐ ω ∂μ, 0 ≤ E.D ω ∧ 0 ≤ E.Q ω ∧ 0 ≤ E.R ω ∧ 0 ≤ E.T ω) ∧
  IndepFun E.T (fun ω => (E.D ω, E.Q ω, E.R ω)) μ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Eq. (1), p. 6: the random budget for local spend, `b̂(x, R, T) = b + γT + R − x`. -/
def bhat (P : Params) (E : Env Ω) (x : ℝ) (ω : Ω) : ℝ :=
  P.b + P.gam * E.T ω + E.R ω - x

/-- p. 7: the random local shortage `S(x) = (D − min{Q, b̂(x,R,T)/α})⁺`. -/
noncomputable def S (P : Params) (E : Env Ω) (x : ℝ) (ω : Ω) : ℝ :=
  max (E.D ω - min (E.Q ω) (bhat P E x ω / P.al)) 0

/-- p. 7: the random cost of a cycle,
`iTx + α min{D, Q, (b + γT + R − x)/α} + min{x, S(x)} + v (S(x) − x)⁺`. -/
noncomputable def cycleCost (P : Params) (E : Env Ω) (x : ℝ) (ω : Ω) : ℝ :=
  P.hold * E.T ω * x + P.al * min (E.D ω) (min (E.Q ω) (bhat P E x ω / P.al))
    + min x (S P E x ω) + P.v * max (S P E x ω - x) 0

/-- p. 7, first line of the display: the expected cycle cost `C(x) = E[cycleCost(x)]`. -/
noncomputable def C (P : Params) (μ : Measure Ω) (E : Env Ω) (x : ℝ) : ℝ :=
  ∫ ω, cycleCost P E x ω ∂μ

/-- p. 9: the cost of the auxiliary model, in which the local budget constraint is relaxed,
`Ca(x) = αμ_D + iμ_T x + (1 − α) E[(D − Q)⁺] + (v − 1) E[(D − Q − x)⁺]`. -/
noncomputable def Ca (P : Params) (μ : Measure Ω) (E : Env Ω) (x : ℝ) : ℝ :=
  P.al * (∫ ω, E.D ω ∂μ) + P.hold * (∫ ω, E.T ω ∂μ) * x
    + (1 - P.al) * (∫ ω, max (E.D ω - E.Q ω) 0 ∂μ)
    + (P.v - 1) * (∫ ω, max (E.D ω - E.Q ω - x) 0 ∂μ)

/-- p. 9: the critical shortage probability `β∗ = iμ_T/(v − 1)`. -/
noncomputable def betaStar (P : Params) (μ : Measure Ω) (E : Env Ω) : ℝ :=
  P.hold * (∫ ω, E.T ω ∂μ) / (P.v - 1)

/-- p. 9: `x` is a value of the generalized inverse `F̄⁻¹_{D−Q}(β)` of the survival function
of the net demand `D − Q`: either `P(D − Q > x) ≤ β < P(D − Q > y)` for every `y < x`, or
`β ≥ 1` (where the inverse `inf {y | P(D − Q > y) ≤ β}` is `−∞`) and `x ≤ 0`, so that
`x⁺ = 0`. -/
def IsNetFractile (μ : Measure Ω) (E : Env Ω) (β x : ℝ) : Prop :=
  ((μ {ω | x < E.D ω - E.Q ω}).toReal ≤ β ∧
      ∀ y < x, β < (μ {ω | y < E.D ω - E.Q ω}).toReal)
    ∨ (1 ≤ β ∧ x ≤ 0)

end PrepoLocal.Threshold


