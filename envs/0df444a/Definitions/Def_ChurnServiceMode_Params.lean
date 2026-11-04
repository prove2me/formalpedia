-- Prove2me | Definitions.Def_ChurnServiceMode_Params
-- name    : ChurnServiceMode_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:48.102836+00:00
-- url     : https://prove2.me/theorems/b8815cb2-b26c-47c0-a1ac-e3b17b511a9a
-- title:
--   Model primitives: Risky/Safe drifts, Risky volatility, threshold, hazard $Q$, $\mathrm{erfc}$, the operator $B_i$, interval policies
-- statement:
--   A firm serves one customer and chooses at each time a **service mode** $u_t\in\{R,S\}$ (Risky or Safe). The **model primitives** are the drifts $\mu_R>0$, $\mu_S>0$, the Risky volatility $\sigma_R>0$ (the Safe volatility is $\sigma_S=0$) and the **satisfaction threshold** $q\in\mathbb R$. Write $\mu_u,\sigma_u$ for the drift and volatility of mode $u$.
--
--   The **hazard rate** is the step function
--   $$Q(h)=\mathbb 1\{h<q\}.$$
--   With the error function $\operatorname{erf}(x)=\frac{2}{\sqrt\pi}\int_0^x e^{-t^2}\,dt$ (the published `PSOutsourcing.PartialObs.erf`), the **complementary error function** is $\operatorname{erfc}(x)=1-\operatorname{erf}(x)$.
--
--   For a function $V:\mathbb R\to\mathbb R$ and a mode $i$, the operator of displays (14)–(15) is
--   $$B_i(x,V)=-Q(x)V(x)+(\mu_i-x)V'(x)+\tfrac12\sigma_i^2V''(x)+\mu_i .$$
--
--   A stationary Markov policy $\pi:\mathbb R\to\{R,S\}$ is an **interval policy** (Definition 2) if it divides the satisfaction line into countably many alternating Risky and Safe intervals and uses Safe at each boundary point. It has **finitely many intervals** if there are finitely many boundary points, and its Safe intervals are **nondegenerate** if none of them is a single point.
--
--   These are the objects in which every statement of the mission is written.
--
--   **Formalization Note** Positivity of $\sigma_R$ is never displayed in the paper, but all formulas divide by it. $V'$ and $V''$ are `deriv V` and `deriv (deriv V)`; since $\sigma_S=0$, the second-order term of $B_S$ vanishes identically, which is footnote 13's convention. An interval policy is encoded as: the Risky set $\{\pi=R\}$ is open and its boundary meets every bounded interval in finitely many points; a single-point Safe interval is allowed, as in the paper's own case $\theta_b=q$.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, §3, pp.5–7 (displays (1), (4), Definition 2); p.9 (erf); p.17 (displays (14)–(15), footnote 13); p.18 (erfc)

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- **Model primitives** of Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode
Control*, SSRN 3188226 (Dec 1, 2022), §3, pp.5–6: the drift `μR` and volatility `σR` of the
Risky mode, the drift `μS` of the Safe mode (whose volatility is `σS = 0`), and the satisfaction
threshold `q` of the hazard rate (4).

**Formalization Note.** `0 < μR` and `0 < μS` are stated on p.5. `0 < σR` is never displayed in
the paper, but every formula of Lemmas 2–3 and Proposition 3 divides by `σR` (reading R1). The
threshold `q` is unconstrained here; Assumption 1 (`μS < q`, p.8) is a hypothesis of the
statements that use it. -/
structure Params where
  /-- `μ_R`, the drift of the reward under the Risky mode. -/
  μR : ℝ
  /-- `μ_S`, the drift of the reward under the Safe mode. -/
  μS : ℝ
  /-- `σ_R`, the volatility of the reward under the Risky mode. -/
  σR : ℝ
  /-- `q`, the satisfaction threshold of the hazard rate (4). -/
  q : ℝ
  μR_pos : 0 < μR
  μS_pos : 0 < μS
  σR_pos : 0 < σR

/-- The two service modes `R` (Risky) and `S` (Safe), p.5. -/
inductive Mode
  | R
  | S
  deriving DecidableEq

/-- Every subset of the two-point action space is measurable. -/
instance : MeasurableSpace Mode := ⊤

/-- The reward drift `μ_u` of mode `u`, display (1), p.5. -/
def Params.mu (p : Params) : Mode → ℝ
  | .R => p.μR
  | .S => p.μS

/-- The reward volatility `σ_u` of mode `u`, display (1), p.5, with `σ_S = 0`. -/
def Params.sig (p : Params) : Mode → ℝ
  | .R => p.σR
  | .S => 0

/-- The hazard rate `Q(h) = 1{h < q}` of display (4), p.6. -/
noncomputable def Params.hazard (p : Params) (h : ℝ) : ℝ :=
  if h < p.q then 1 else 0

/-- The complementary error function `erfc(x) = 1 − erf(x)` (Lemma 5, p.18), where
`erf(x) = (2/√π) ∫₀ˣ e^{−t²} dt` is the paper's error function (p.9), taken from the published
definition `PSOutsourcing.PartialObs.erf`. -/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

/-- The operator `B_i(x, V) = −Q(x)V(x) + (μ_i − x)V′(x) + ½σ_i²V″(x) + μ_i` of displays
(14)–(15), p.17, for mode `i`.

**Formalization Note.** `V′` and `V″` are `deriv V` and `deriv (deriv V)`. Because `σ_S = 0`, the
second-order term vanishes identically for `i = S`, which is footnote 13's convention
`½σ_S²V″(x) ≜ 0` for every `x` (also where `V″` does not exist). For `i = R` the term uses
`deriv (deriv V) x`, which is `0` where `V′` is not differentiable; statements only use it off
the exceptional set. -/
noncomputable def Params.generator (p : Params) (i : Mode) (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  -p.hazard x * V x + (p.mu i - x) * deriv V x + 1 / 2 * p.sig i ^ 2 * deriv (deriv V) x
    + p.mu i

/-- **Interval policy** (Definition 2, p.7): a stationary Markov policy `π : ℝ → {R, S}` that
divides the satisfaction line into a countable number of alternating Risky and Safe intervals,
using Safe at each boundary point.

**Formalization Note.** Encoded as: the Risky set `{π = R}` is open (Safe at every boundary
point) and its frontier meets every bounded interval in finitely many points (the alternating
intervals can be listed in order, so their endpoints do not accumulate). A Safe interval may be a
single point, as in the paper's own case `θ_b = q` (p.10). -/
def IsIntervalPolicy (π : ℝ → Mode) : Prop :=
  IsOpen {y | π y = Mode.R} ∧ ∀ a b : ℝ, (frontier {y | π y = Mode.R} ∩ Set.Icc a b).Finite

/-- An interval policy "with a finite number of intervals" (Proposition 1, p.8; Lemma 4, p.17):
the boundary of its Risky set is finite. -/
def HasFinitelyManyIntervals (π : ℝ → Mode) : Prop :=
  (frontier {y | π y = Mode.R}).Finite

/-- Every Safe interval of `π` is nondegenerate: each Safe point is a limit of interior Safe
points (no Safe interval is a single point). Used by the corrected uniqueness clause of Lemma 1. -/
def SafeIntervalsNondegenerate (π : ℝ → Mode) : Prop :=
  {y | π y = Mode.S} ⊆ closure (interior {y | π y = Mode.S})

end ChurnServiceMode


