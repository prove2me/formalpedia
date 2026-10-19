-- Prove2me | Definitions.Def_CrossLicensing_ExPost_Model
-- name    : CrossLicensing_ExPost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:42.47063+00:00
-- url     : https://prove2.me/theorems/5d49d499-bcea-493c-80ed-4d72e215d716
-- title:
--   Cross-licensing quantity game and supplier profit, equations (1)–(3)
-- statement:
--   Two manufacturers choose nonnegative quantities $q_1,q_2$ after fixed innovation levels $0\le T_1\le T_2$, a cross-licensing effectiveness $0\le\beta\le1$, and a nonnegative wholesale price $r$ are given. Their quantity-stage profits are
--
--   $$
--   \Pi_1=(1+T_1+\beta T_2-q_1-q_2-r)q_1,\qquad
--   \Pi_2=(1+T_2+\beta T_1-q_1-q_2-r)q_2.
--   $$
--
--   The quantity equilibrium is a pure Nash equilibrium of these payoffs over $[0,\infty)^2$. The supplier earns $r(q_1+q_2)$ at any quantity profile. The definitions also record the thresholds $r_1=1+T_1(2-\beta)-T_2(1-2\beta)$ and $r_2=1+\beta T_1+T_2$, together with the three-piece quantity and supplier-profit expressions of equations (2) and (3).
--
--   These objects fix a common model for the goal and both milestones. At $\beta=0$ the same game represents no cross-licensing. **Formalization Note** The paper fixes $T_2\ge T_1$ when printing (2); $r\ge0$ makes the intended supplier-price domain explicit.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), pp. 9–10, equations (1)–(3)

import Mathlib
import Definitions.Def_CrossLicensing_ExPost_Game

namespace CrossLicensing.ExPost

/-- Standing range for the ex-post comparison on pp. 9–11. -/
def Standing (β T₁ T₂ r : ℝ) : Prop :=
  0 ≤ β ∧ β ≤ 1 ∧ 0 ≤ T₁ ∧ T₁ ≤ T₂ ∧ 0 ≤ r

/-- Manufacturer 1's quantity-stage profit, equation (1). -/
def payoff1 (β T₁ T₂ r q₁ q₂ : ℝ) : ℝ :=
  (1 + T₁ + β * T₂ - q₁ - q₂ - r) * q₁

/-- Manufacturer 2's quantity-stage profit, equation (1). -/
def payoff2 (β T₁ T₂ r q₂ q₁ : ℝ) : ℝ :=
  (1 + T₂ + β * T₁ - q₂ - q₁ - r) * q₂

/-- Nash equilibrium of the quantity game (1), with both quantities nonnegative. -/
def IsQuantityNE (β T₁ T₂ r : ℝ) (q : ℝ × ℝ) : Prop :=
  IsNE (Set.Ici 0) (Set.Ici 0) (payoff1 β T₁ T₂ r) (payoff2 β T₁ T₂ r) q

/-- First wholesale-price threshold in (2). -/
def r₁ (β T₁ T₂ : ℝ) : ℝ :=
  1 + T₁ * (2 - β) - T₂ * (1 - 2 * β)

/-- Second wholesale-price threshold in (2). -/
def r₂ (β T₁ T₂ : ℝ) : ℝ :=
  1 + T₁ * β + T₂

/-- The three-piece quantity profile displayed in equation (2). -/
noncomputable def quantityFormula (β T₁ T₂ r : ℝ) : ℝ × ℝ :=
  if r ≤ r₁ β T₁ T₂ then
    ((1 - r + T₁ * (2 - β) + T₂ * (-1 + 2 * β)) / 3,
     (1 - r + T₁ * (-1 + 2 * β) + T₂ * (2 - β)) / 3)
  else if r ≤ r₂ β T₁ T₂ then
    (0, (1 - r + β * T₁ + T₂) / 2)
  else (0, 0)

/-- The supplier's profit at any quantity profile, before substituting equilibrium. -/
def supplierProfit (r : ℝ) (q : ℝ × ℝ) : ℝ := r * (q.1 + q.2)

/-- The three-piece supplier-profit expression in equation (3). -/
noncomputable def supplierProfitFormula (β T₁ T₂ r : ℝ) : ℝ :=
  if r ≤ r₁ β T₁ T₂ then
    (2 - 2 * r + (T₁ + T₂) * (1 + β)) * r / 3
  else if r ≤ r₂ β T₁ T₂ then
    (1 - r + β * T₁ + T₂) * r / 2
  else 0

end CrossLicensing.ExPost


