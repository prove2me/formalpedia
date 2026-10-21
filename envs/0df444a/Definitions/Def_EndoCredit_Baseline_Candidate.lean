-- Prove2me | Definitions.Def_EndoCredit_Baseline_Candidate
-- name    : EndoCredit_Baseline_Candidate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:51.131829+00:00
-- url     : https://prove2.me/theorems/299041b8-8b68-4db7-855e-588bb07987e6
-- title:
--   §3, pp. 8–11 — dual process, running shadow price, candidate consumption, and wealth formula
-- statement:
--   Given an initial income-adjusted dual level $y_0>0$, the paper's dual process is $y_t=y_0\bar I^{-\gamma}e^{\beta t}H_t I_t^\gamma$. Its shadow price is the running maximum of $Q^\gamma y_s-1$ and zero. The candidate consumption is the inverse-marginal-utility choice with this shadow price.
--
--   $$
--   D_t^*=\max\left(0,\max_{0\le s\le t}Q^\gamma y_s-1\right),\qquad
--   c_t^*=I_t\left(\frac{y_t}{1+D_t^*}\right)^{-1/\gamma}.
--   $$
--
--   The file also defines the conditional-present-value integrand for net consumption and, separately, the explicit right side of the proposed wealth identity (3.10). Their equality is a theorem target, not part of either definition.
--
--   **Formalization Note** The path maximum is the real supremum on the compact interval $[0,t]$; the Brownian reference definition supplies continuous sample paths. A theorem using it must establish boundedness and the positivity of the real-power bases. The multiplier branch used by the goal is $0<y_0\le Q^{-\gamma}$, which ensures $D_0^*=0$ almost surely.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), pp. 8–11, (3.3), Proposition 3.1, (3.10)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

open MeasureTheory
open scoped NNReal

namespace EndoCredit.Baseline

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Income-adjusted dual process with `y 0 = y0` almost surely on Brownian paths. -/
noncomputable def y (p : Params) (W : BrownianPath Ω) (y0 : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  y0 * p.Ibar ^ (-p.gam) * Real.exp (p.bet * (t : ℝ)) * H p W t ω *
    inc p W t ω ^ p.gam

/-- Proposition 3.1's reflected shadow price, using a compact time interval. -/
noncomputable def Dstar (p : Params) (W : BrownianPath Ω) (y0 : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (sSup ((fun s : ℝ≥0 => Q p ^ p.gam * y p W y0 s ω) '' Set.Icc 0 t) - 1)

/-- Consumption candidate from (3.3). -/
noncomputable def cStar (p : Params) (W : BrownianPath Ω) (y0 : ℝ) : Consumption Ω :=
  fun t ω => (y p W y0 t ω / (1 + Dstar p W y0 t ω)) ^ (-(1 / p.gam)) *
    inc p W t ω

/-- Conditional present-value integrand for financial wealth, before conditioning. -/
noncomputable def pvNet (p : Params) (W : BrownianPath Ω) (c : Consumption Ω)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioi (t : ℝ),
    H p W s.toNNReal ω / H p W t ω *
      (c s.toNNReal ω - inc p W s.toNNReal ω)

/-- The explicit expression on the right of (3.10), kept separate from financial wealth. -/
noncomputable def wealthCF (p : Params) (W : BrownianPath Ω) (y0 : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  inc p W t ω * phi p (y p W y0 t ω / (1 + Dstar p W y0 t ω))

end EndoCredit.Baseline


