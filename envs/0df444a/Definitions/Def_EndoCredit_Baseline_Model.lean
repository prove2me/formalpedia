-- Prove2me | Definitions.Def_EndoCredit_Baseline_Model
-- name    : EndoCredit_Baseline_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:14.922749+00:00
-- url     : https://prove2.me/theorems/12806f29-21c8-42ee-94e1-aadae72a5e5a
-- title:
--   §2, pp. 4–7 — baseline household, participation constraints, and constants
-- statement:
--   The baseline model has a household with positive stochastic income $I_t$, CRRA utility $u(c)=c^{1-\gamma}/(1-\gamma)$ for $\gamma>0$, $\gamma\ne1$, and a state-price density $H_t$. Its income and financial risks are driven by two independent standard Brownian motions $B_1,B_2$. The market price of risk is $\theta=(\mu-r)/\sigma$, and the present-value rate of income is $r_I=r-\mu_I+\theta\sigma_I\rho_I$.
--
--   The definition fixes the constants $K$, $\hat\beta$, the positive quadratic root $\alpha_+$, the allowed upper bound $\bar\delta$ on the default fraction, $Q$, and the proposed credit-limit coefficient $m^*$. It also defines the static budget and the feasible consumption plans: at every time, conditional continuation utility must exceed conditional utility from consuming $\delta I_s$ after default.
--
--   $$
--   \mathcal C(x)=\left\{c:\ \mathbb E\int_0^\infty H_s(c_s-I_s)\,ds\le x,\quad
--   \mathbb E\!\left[\int_t^\infty e^{-\beta s}u(c_s)\,ds\mid\mathcal F_t\right]\ge
--   \mathbb E\!\left[\int_t^\infty e^{-\beta s}u(\delta I_s)\,ds\mid\mathcal F_t\right]
--   \text{ for all }t\ge0\right\}.
--   $$
--
--   This model is shared by every result in the mission.
--
--   **Formalization Note** This is the static martingale form of Problem 2.2 solved in §3; the printed problem also mentions an undefined default time. The Brownian filtration is natural and uncompleted. Time is $\mathbb R_{\ge0}$; integrals use the real interval $(t,\infty)$. The model explicitly requires integrability of plan cost and utility and of conditional-expectation inputs. In addition to the printed standing conditions, $\hat\beta>0$ and a positive leading coefficient of the $\alpha_+$ quadratic make the displayed formulas well posed. The initial income $\bar I$ is positive.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), pp. 4–7, §2.1–§2.2, (2.1)–(2.7), Problem 2.2

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EndoCredit.Baseline

/-- The mortality-adjusted parameters of the baseline household model. -/
structure Params where
  gam : ℝ
  bet : ℝ
  r : ℝ
  mu : ℝ
  sig : ℝ
  muI : ℝ
  sigI : ℝ
  rhoI : ℝ
  delta : ℝ
  Ibar : ℝ

noncomputable def theta (p : Params) : ℝ := (p.mu - p.r) / p.sig
noncomputable def rI (p : Params) : ℝ := p.r - p.muI + theta p * p.sigI * p.rhoI
noncomputable def K (p : Params) : ℝ :=
  p.r + (p.bet - p.r) / p.gam + (p.gam - 1) / (2 * p.gam ^ 2) * theta p ^ 2
noncomputable def betaHat (p : Params) : ℝ :=
  p.bet - (1 - p.gam) * p.muI + (1 / 2 : ℝ) * p.gam * (1 - p.gam) * p.sigI ^ 2
noncomputable def quadA (p : Params) : ℝ :=
  (1 / 2 : ℝ) * ((p.gam * p.sigI * p.rhoI - theta p) ^ 2 +
    p.gam ^ 2 * p.sigI ^ 2 * (1 - p.rhoI ^ 2))

/-- The positive root of the quadratic on p. 7, expressed by the quadratic formula. -/
noncomputable def alphaPlus (p : Params) : ℝ :=
  let a := quadA p
  let b := betaHat p - rI p - a
  (-b + Real.sqrt (b ^ 2 + 4 * a * betaHat p)) / (2 * a)

noncomputable def Cq (p : Params) : ℝ :=
  K p * alphaPlus p * p.gam / ((1 - p.gam + alphaPlus p * p.gam) * betaHat p)
noncomputable def deltaBar (p : Params) : ℝ :=
  (1 / rI p) * (p.gam * K p * (alphaPlus p - 1) /
    (1 - p.gam + alphaPlus p * p.gam)) * Cq p ^ (-(1 / (1 - p.gam)))
noncomputable def Q (p : Params) : ℝ :=
  p.delta * Cq p ^ (1 / (1 - p.gam))
noncomputable def mStar (p : Params) : ℝ :=
  1 / rI p - (1 - p.gam + alphaPlus p * p.gam) /
    (p.gam * K p * (alphaPlus p - 1)) * Q p
noncomputable def ybar (p : Params) : ℝ := Q p ^ (-p.gam)
noncomputable def coefA (p : Params) : ℝ :=
  p.delta ^ (1 - p.gam) * alphaPlus p * Q p ^ (p.gam * alphaPlus p) /
    (betaHat p * (alphaPlus p - 1) * (1 - p.gam + alphaPlus p * p.gam))
noncomputable def phi (p : Params) (w : ℝ) : ℝ :=
  w ^ (-(1 / p.gam)) / K p - 1 / rI p + coefA p * w ^ (alphaPlus p - 1)

/-- Conditions independent of the reservation-utility fraction `delta`. -/
def Params.Core (p : Params) : Prop :=
  0 < p.sig ∧ 0 < p.muI ∧ 0 < p.sigI ∧ -1 ≤ p.rhoI ∧ p.rhoI ≤ 1 ∧
  0 < p.gam ∧ p.gam ≠ 1 ∧ 0 < rI p ∧ 0 < K p ∧ 0 < betaHat p ∧
  0 < quadA p ∧ 0 < p.Ibar

/-- Standing conditions of §§2–3, with the two necessary nondegeneracy additions. -/
def Params.Standing (p : Params) : Prop :=
  p.Core ∧ 0 < p.delta ∧ p.delta ≤ deltaBar p

noncomputable def u (gam c : ℝ) : ℝ := c ^ (1 - gam) / (1 - gam)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

abbrev BrownianPath (Ω : Type*) := ℝ≥0 → Ω → EthierKurtz.SDEState 2
abbrev Consumption (Ω : Type*) := ℝ≥0 → Ω → ℝ

/-- The natural, uncompleted filtration of the pair of Brownian motions. -/
noncomputable def filtration (P : Measure Ω) (W : BrownianPath Ω)
    (hW : EthierKurtz.IsStandardBrownian P W) : Filtration ℝ≥0 mΩ :=
  Filtration.natural W (fun t => (hW.1 t).stronglyMeasurable)

noncomputable def B1 (W : BrownianPath Ω) (t : ℝ≥0) (ω : Ω) : ℝ := W t ω 0
noncomputable def B2 (W : BrownianPath Ω) (t : ℝ≥0) (ω : Ω) : ℝ := W t ω 1

/-- The state-price density of p. 5. -/
noncomputable def H (p : Params) (W : BrownianPath Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(p.r + theta p ^ 2 / 2) * (t : ℝ) - theta p * B1 W t ω)

/-- The explicit GBM income process solving the SDE on p. 4. -/
noncomputable def inc (p : Params) (W : BrownianPath Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  p.Ibar * Real.exp ((p.muI - p.sigI ^ 2 / 2) * (t : ℝ) +
    p.sigI * (p.rhoI * B1 W t ω + Real.sqrt (1 - p.rhoI ^ 2) * B2 W t ω))

/-- The static t=0 budget of the martingale formulation of Problem 2.2. -/
noncomputable def budgetCost (p : Params) (P : Measure Ω) (W : BrownianPath Ω)
    (c : Consumption Ω) : ℝ :=
  ∫ ω, (∫ s in Set.Ioi (0 : ℝ),
    H p W s.toNNReal ω * (c s.toNNReal ω - inc p W s.toNNReal ω) ∂volume) ∂P

noncomputable def contU (p : Params) (c : Consumption Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioi (t : ℝ), Real.exp (-p.bet * s) * u p.gam (c s.toNNReal ω)

noncomputable def resU (p : Params) (W : BrownianPath Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioi (t : ℝ), Real.exp (-p.bet * s) * u p.gam (p.delta * inc p W s.toNNReal ω)

/-- Positive progressively measurable plans with genuine finite budget and utility integrals. -/
def IsPlan (p : Params) (P : Measure Ω) (W : BrownianPath Ω)
    (hW : EthierKurtz.IsStandardBrownian P W) (c : Consumption Ω) : Prop :=
  IsStronglyProgressive (filtration P W hW) c ∧
  (∀ t ω, 0 < c t ω) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => H p W s.toNNReal ω * c s.toNNReal ω)
    (Set.Ioi 0) volume) ∧
  Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ),
    H p W s.toNNReal ω * c s.toNNReal ω) P ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-p.bet * s) *
    |u p.gam (c s.toNNReal ω)|) (Set.Ioi 0) volume) ∧
  Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ),
    Real.exp (-p.bet * s) * |u p.gam (c s.toNNReal ω)|) P ∧
  (∀ t, Integrable (contU p c t) P) ∧
  Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ),
    H p W s.toNNReal ω * (c s.toNNReal ω - inc p W s.toNNReal ω)) P

/-- The static feasible set with the conditional participation constraints (2.6). -/
noncomputable def Feasible (p : Params) (P : Measure Ω) (W : BrownianPath Ω)
    (hW : EthierKurtz.IsStandardBrownian P W) (x : ℝ) : Set (Consumption Ω) :=
  {c | IsPlan p P W hW c ∧ budgetCost p P W c ≤ x ∧
    (∀ t, Integrable (resU p W t) P) ∧
    ∀ t, P[resU p W t | filtration P W hW t] ≤ᵐ[P]
      P[contU p c t | filtration P W hW t]}

noncomputable def J0 (p : Params) (P : Measure Ω) (c : Consumption Ω) : ℝ :=
  ∫ ω, contU p c 0 ω ∂P

end EndoCredit.Baseline


