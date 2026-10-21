-- Prove2me | Definitions.Def_MemoryScreen_Menu_Model
-- name    : MemoryScreen_Menu_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:09.401903+00:00
-- url     : https://prove2.me/theorems/e5718a7d-0fa0-425e-b9a5-25420a4948a9
-- title:
--   Two-type screening program (6) and perfect-memory objective (4)
-- statement:
--   There are two buyer types, $\alpha_H>\alpha_L$, with prior probability $\theta\in(0,1)$ of the high type, seller marginal cost $c\ge0$, and transaction-cost density $f$. A menu offers two tariffs $(T_H,p_H)$ and $(T_L,p_L)$. If the true type is $\alpha$ and the buyer's later belief is $\widetilde\alpha$, her payoff from tariff $(T,p)$ is
--
--   $$EU(T,p;\alpha,\widetilde\alpha)=\int_{-\infty}^{\widetilde\alpha-p}(\alpha-b-p)f(b)\,db-T.$$
--
--   Program (6) maximizes expected seller profit over menus satisfying both types' participation constraints and incentive constraints. On a deviation, the buyer adopts the belief associated with the chosen contract. The definition also records the perfect-memory objective (4), the reduced limited-memory objective from the proof of Proposition 1, and $p_L^*=c+\theta(\alpha_H-\alpha_L)/(1-\theta)$.
--
--   **Formalization Note.** The model has one transaction period. Integrals from the support's lower endpoint are represented as integrals from $-\infty$, with $f$ zero below the support. Feasibility uses the weak inequalities printed in (6).
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), pp. 6–11 (PDF 7–12), §2, §3.1, §3.2.1, eqs. (4)–(6)

import Mathlib
import Definitions.Def_MemoryScreen_Menu_CostLaw

open MeasureTheory

namespace MemoryScreen.Menu

/-- Parameters of the two-type screening model, including the common cost law. -/
structure Params extends CostLaw where
  αH : ℝ
  αL : ℝ
  θ : ℝ
  c : ℝ

/-- The standing assumptions of §2, with the finite first moment needed for the payoffs. -/
def Params.Standing (P : Params) : Prop :=
  P.αL < P.αH ∧ 0 < P.θ ∧ P.θ < 1 ∧ 0 ≤ P.c ∧ P.toCostLaw.Valid

/-- The transaction-cost CDF. -/
noncomputable def F (P : Params) (x : ℝ) : ℝ := P.toCostLaw.cdf x

/-- Equation (5): ex ante payoff at true type `α` with stage-two belief `αt`. -/
noncomputable def EU (P : Params) (T p α αt : ℝ) : ℝ :=
  (∫ b in Set.Iic (αt - p), (α - b - p) * P.f b) - T

/-- A menu of two two-part tariffs. -/
structure Menu where
  TH : ℝ
  pH : ℝ
  TL : ℝ
  pL : ℝ

/-- The seller's objective in program (6). -/
noncomputable def profit (P : Params) (M : Menu) : ℝ :=
  P.θ * (M.TH + ∫ b in Set.Iic (P.αH - M.pH), (M.pH - P.c) * P.f b) +
    (1 - P.θ) * (M.TL + ∫ b in Set.Iic (P.αL - M.pL), (M.pL - P.c) * P.f b)

/-- The two IR and two limited-memory IC constraints of program (6). -/
noncomputable def Feasible (P : Params) (M : Menu) : Prop :=
  0 ≤ EU P M.TH M.pH P.αH P.αH ∧
    0 ≤ EU P M.TL M.pL P.αL P.αL ∧
    EU P M.TL M.pL P.αH P.αL ≤ EU P M.TH M.pH P.αH P.αH ∧
    EU P M.TH M.pH P.αL P.αH ≤ EU P M.TL M.pL P.αL P.αL

/-- Maximal profit among all menus feasible for program (6). -/
noncomputable def IsOptimal (P : Params) (M : Menu) : Prop :=
  Feasible P M ∧ ∀ M' : Menu, Feasible P M' → profit P M' ≤ profit P M

/-- The low type's marginal price in Proposition 1. -/
noncomputable def pStarL (P : Params) : ℝ :=
  P.c + P.θ / (1 - P.θ) * (P.αH - P.αL)

/-- The perfect-memory reduced objective, equation (4). -/
noncomputable def perfectObj (P : Params) (pH pL : ℝ) : ℝ :=
  P.θ * ((∫ b in Set.Iic (P.αH - pH), (P.αH - b - P.c) * P.f b) -
    ∫ b in (P.αL - pL)..(P.αH - pL), F P b) +
    (1 - P.θ) * ∫ b in Set.Iic (P.αL - pL), (P.αL - b - P.c) * P.f b

/-- A global maximizer with strict derivative signs on a local interval. -/
noncomputable def PeakedAt (G : ℝ → ℝ) (pB lo hi : ℝ) : Prop :=
  lo < pB ∧ pB < hi ∧ (∀ p : ℝ, G p ≤ G pB) ∧
    (∀ p ∈ Set.Ioo lo pB, 0 < deriv G p) ∧
    (∀ p ∈ Set.Ioo pB hi, deriv G p < 0)

/-- The objective after binding IR_L and IC_H,L, from the proof of Proposition 1. -/
noncomputable def reducedObj (P : Params) (pH pL : ℝ) : ℝ :=
  P.θ * ((∫ b in Set.Iic (P.αH - pH), (P.αH - b - P.c) * P.f b) -
    (P.αH - P.αL) * F P (P.αL - pL)) +
    (1 - P.θ) * ∫ b in Set.Iic (P.αL - pL), (P.αL - b - P.c) * P.f b

/-- The fees that make IR_L and IC_H,L bind at prescribed marginal prices. -/
noncomputable def bindingMenu (P : Params) (pH pL : ℝ) : Menu :=
  let TL := ∫ b in Set.Iic (P.αL - pL), (P.αL - b - pL) * P.f b
  { TH := (∫ b in Set.Iic (P.αH - pH), (P.αH - b - pH) * P.f b) -
      (∫ b in Set.Iic (P.αL - pL), (P.αH - b - pL) * P.f b) + TL,
    pH := pH, TL := TL, pL := pL }

end MemoryScreen.Menu


