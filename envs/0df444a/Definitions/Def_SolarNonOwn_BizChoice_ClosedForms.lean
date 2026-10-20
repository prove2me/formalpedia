-- Prove2me | Definitions.Def_SolarNonOwn_BizChoice_ClosedForms
-- name    : SolarNonOwn_BizChoice_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:05.923073+00:00
-- url     : https://prove2.me/theorems/8daead13-5c70-4237-a719-4a9e1583f5de
-- title:
--   Proof of Proposition 1, pp. OA3–OA7 — thresholds and A/B candidate values
-- statement:
--   Let $\alpha$ be the investment subsidy fraction, $\beta$ the generation subsidy per unit, $r$ the retail price, $t$ the PPA transaction cost, $g$ the upper generation limit, and $c$ the panel cost. The appendix defines the profitability threshold and concavity threshold by
--
--   $$C_0=\frac{g(r+\beta)}{1-\alpha},\qquad A=\sqrt{\frac{\beta(r+t)}{r(r+\beta)+\beta t}}.$$
--
--   It also defines the segmentation thresholds $\eta_1,\eta_2,\eta_3$, feasible-price boundaries $s_1,s_2,l_1,l_2$, subsidy thresholds $A_1,A_2$, case boundary costs $C_{A1},C_{A2}$, and the five candidate price pairs and profit values for Cases A1–A3 and B1–B2. The exact appendix formulas are given in the Lean definitions. The piecewise values $\Pi_A^*$ and $\Pi_B^*$ choose those candidate values in the appendix's cost and subsidy regimes.
--
--   These names provide one shared definition for each object used by the milestones and goal. They do not define the company's actual profit, which comes from the customer-choice model in equation (1).
--
--   **Formalization Note** The standing assumptions (`Standing`) are the §3 model assumptions $0<\alpha$, $0<\beta$, $0<t<r$, $0<g$, together with p. 15's $\beta<r$ and $\alpha<A$. The panel cost $c$ is quantified separately. Every fraction is used by a theorem only in the source regime where its denominator is nonzero.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), pp. OA3–OA7 (PDF pp. 35–39), proofs of Lemma A.1, Lemma 2 and Proposition 1

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_Model

noncomputable section

namespace SolarNonOwn.BizChoice

/-- The concavity threshold A of p. OA5. -/
def Acon (prm : Params) : ℝ :=
  Real.sqrt (prm.beta * (prm.r + prm.t) /
    (prm.r * (prm.r + prm.beta) + prm.beta * prm.t))

/-- Standing assumptions of §§3–4, pp. 8–15: the model assumptions of §3 together
with `β < r` and `α < A` (p. 15). -/
def Standing (prm : Params) : Prop :=
  ModelAssumptions prm ∧ prm.beta < prm.r ∧ prm.alpha < Acon prm

/-- Appendix A, proof p. OA3: critical panel cost. -/
def C0 (prm : Params) : ℝ := prm.g * (prm.r + prm.beta) / (1 - prm.alpha)

def s0star (prm : Params) (c : ℝ) : ℝ :=
  (prm.g * (prm.r + prm.beta) + c * (1 - prm.alpha)) / (2 * (1 - prm.alpha))

def prof0star (prm : Params) (c : ℝ) : ℝ :=
  (prm.g * (prm.r + prm.beta) - c * (1 - prm.alpha)) ^ 2 /
  (4 * prm.g * (1 - prm.alpha) * (prm.r + prm.beta))

/-- Proof of Lemma 2, p. OA4. -/
def eta1 (prm : Params) (s l : ℝ) : ℝ := ((1 - prm.alpha) * s - l) / prm.beta
def eta2 (l p : ℝ) : ℝ := l / p
def eta3 (prm : Params) (l : ℝ) : ℝ := l / prm.r

/-- Feasible-region boundaries in proof of Proposition 1, p. OA5. -/
def s1 (prm : Params) : ℝ := prm.g * prm.beta / (1 - prm.alpha)
def s2 (prm : Params) : ℝ := prm.g * (prm.r + prm.beta) / (1 - prm.alpha)
def l1 (prm : Params) (s : ℝ) : ℝ := s * (1 - prm.alpha) - prm.g * prm.beta
def l2 (prm : Params) (s : ℝ) : ℝ := prm.r * s * (1 - prm.alpha) / (prm.r + prm.beta)

def A1 (prm : Params) : ℝ :=
  prm.beta * prm.t / (prm.r * (prm.r + prm.beta) + prm.beta * prm.t)
def A2 (prm : Params) : ℝ := prm.beta / (prm.beta + prm.r)

def CA1 (prm : Params) : ℝ :=
  prm.g * (prm.r * prm.alpha * (prm.r + prm.beta) -
    prm.t * prm.beta * (1 - prm.alpha)) /
  (prm.alpha * (1 - prm.alpha) * (prm.r + prm.t * (1 - prm.alpha)))
def CA2 (prm : Params) : ℝ :=
  prm.g * (prm.r ^ 2 + prm.beta * (prm.r + prm.t)) /
  ((1 - prm.alpha) * (prm.r + prm.t))

/-- Case A1, p. OA5. -/
def sA1 (prm : Params) (c : ℝ) : ℝ :=
  (prm.r + prm.beta) * (prm.g * (prm.r + prm.beta) + c * prm.alpha * (1 - prm.alpha)) /
  ((1 - prm.alpha) * ((prm.r + prm.beta) * (1 + prm.alpha) + prm.t * (1 - prm.alpha)))
def lA1 (prm : Params) (c : ℝ) : ℝ :=
  prm.r * (prm.g * (prm.r + prm.beta) + c * prm.alpha * (1 - prm.alpha)) /
  ((prm.r + prm.beta) * (1 + prm.alpha) + prm.t * (1 - prm.alpha))
def profA1 (prm : Params) (c : ℝ) : ℝ :=
  (c ^ 2 * prm.alpha ^ 2 * (1 - prm.alpha) ^ 2 +
    prm.g ^ 2 * (prm.r + prm.beta) ^ 2 -
    2 * c * prm.g * (1 - prm.alpha) * (prm.r + prm.beta + prm.t * (1 - prm.alpha))) /
  (2 * prm.g * (1 - prm.alpha) *
    (prm.r + prm.t + prm.alpha * (prm.r - prm.t) + prm.beta * (1 + prm.alpha)))

/-- Case A2, p. OA5. -/
def denomA2 (prm : Params) : ℝ :=
  prm.r ^ 2 * prm.alpha ^ 2 - prm.beta * (prm.r + prm.t) * (1 - prm.alpha ^ 2)
def sA2 (prm : Params) (c : ℝ) : ℝ :=
  (c * prm.alpha * (prm.r ^ 2 * prm.alpha - prm.beta * (prm.r + prm.t) * (1 - prm.alpha)) -
    prm.g * prm.beta * (prm.r ^ 2 + prm.beta * (prm.r + prm.t))) / denomA2 prm
def lA2 (prm : Params) (c : ℝ) : ℝ :=
  prm.r ^ 2 * (c * prm.alpha ^ 2 * (1 - prm.alpha) - prm.g * prm.beta) / denomA2 prm
def profA2 (prm : Params) (c : ℝ) : ℝ :=
  (2 * c * prm.g * prm.beta * (prm.r + prm.t) * (1 - prm.alpha) -
    c ^ 2 * prm.alpha ^ 2 * (prm.r + prm.t) * (1 - prm.alpha) ^ 2 -
    prm.g ^ 2 * prm.beta * (prm.r ^ 2 + prm.beta * (prm.r + prm.t))) /
  (2 * prm.g * denomA2 prm)

/-- Case A3, p. OA5. -/
def sA3 (prm : Params) : ℝ :=
  prm.g * (prm.t * prm.beta + prm.r * (prm.r + prm.beta)) /
  ((prm.r + prm.t) * (1 - prm.alpha))
def lA3 (prm : Params) : ℝ := prm.g * prm.r ^ 2 / (prm.r + prm.t)
def profA3 (prm : Params) (c : ℝ) : ℝ :=
  (prm.g * (prm.r ^ 2 / (prm.r + prm.t) + prm.beta) - 2 * c * (1 - prm.alpha)) / 2

/-- Case B1, p. OA6. -/
def sB1 (prm : Params) (c : ℝ) : ℝ := s0star prm c
def lB1 (prm : Params) (c : ℝ) : ℝ :=
  prm.r * (prm.g * (prm.r + prm.beta) + c * (1 - prm.alpha)) /
  (2 * (prm.r + prm.beta))
def profB1 (prm : Params) (c : ℝ) : ℝ := prof0star prm c

/-- Case B2, p. OA6. -/
def denomB2 (prm : Params) : ℝ :=
  prm.alpha ^ 2 * (prm.r + prm.beta) ^ 2 - prm.beta * (2 * prm.r + prm.beta)
def sB2 (prm : Params) (c : ℝ) : ℝ :=
  (c * (prm.alpha ^ 2 * (prm.r + prm.beta) ^ 2 - prm.r * prm.beta -
    prm.alpha * prm.beta * (prm.r + prm.beta)) -
    prm.g * prm.beta * (prm.r + prm.beta) ^ 2) / denomB2 prm
def lB2 (prm : Params) (c : ℝ) : ℝ :=
  prm.r * (c * (1 - prm.alpha) *
    (prm.alpha ^ 2 * (prm.r + prm.beta) - prm.beta) - prm.g * prm.r * prm.beta) /
  denomB2 prm
def profB2 (prm : Params) (c : ℝ) : ℝ :=
  prm.beta * (prm.g * (prm.r + prm.beta) - c * (1 - prm.alpha)) ^ 2 /
  (2 * prm.g * (prm.beta * (2 * prm.r + prm.beta) -
    prm.alpha ^ 2 * (prm.r + prm.beta) ^ 2))

/-- Best values for the p ≤ r and p > r regions, p. OA7, while c < C0. -/
def profAstar (prm : Params) (c : ℝ) : ℝ :=
  if c ≤ CA1 prm then profA1 prm c
  else if c < CA2 prm then profA2 prm c else profA3 prm c
def profBstar (prm : Params) (c : ℝ) : ℝ :=
  if prm.alpha < A2 prm then profB2 prm c else profB1 prm c

end SolarNonOwn.BizChoice


