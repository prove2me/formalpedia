-- Prove2me | Definitions.Def_BundledPay_Base_Model
-- name    : BundledPay_Base_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:49.928781+00:00
-- url     : https://prove2.me/theorems/0f794db0-eee4-4ce8-a699-6c4c29416da3
-- title:
--   §4.1–4.3 — hospital–physician care intensity and payment model
-- statement:
--   A hospital and physicians jointly determine the fraction $I$ of patients on the intensive pathway. Their efforts $i_h,i_p\in[0,1]$ and integration $\Psi\in(0,1)$ give
--
--   $$I=(1-i_h)\Psi+(1-\Psi)i_p.$$
--
--   Hospital pathway costs are $c_1>c_2$ and physician fees are $r_{1,p}>r_{2,p}$. Fee-for-service and bundled payoffs are exactly equations (2) and (3), including the quadratic quality penalties around $I_0$ and gainsharing $(1-I)T$. The model defines Nash equilibria in both effort games and subgame-perfect equilibria when the hospital first chooses $T\ge0$. It also defines total fee-for-service payer payment, the hospital's break-even bundled payment, payer savings, and the thresholds $\bar\Psi$, $\Psi_+$ and $\Psi_0$.
--
--   The base-model results set the hospital's quality weight $w_q$ to zero; the definition retains it for the paper's general model.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, pp. 10–14, §4.1–4.3, Table 1 and eqs. (1)–(3); p. 37, eq. (48)

import Mathlib
import Definitions.Def_BundledPay_Base_GenericGame

namespace BundledPay.Base

structure Params where
  rh : ℝ
  c1 : ℝ
  c2 : ℝ
  r1p : ℝ
  r2p : ℝ
  wb : ℝ
  wq : ℝ
  I0 : ℝ
  psi : ℝ

/-- Standing assumptions from §4.1–4.2 and Table 1. -/
def Params.Standing (P : Params) : Prop :=
  P.c2 < P.c1 ∧ P.r2p < P.r1p ∧ 0 < P.wb ∧
    0 ≤ P.I0 ∧ P.I0 ≤ 1 ∧ 0 < P.psi ∧ P.psi < 1

def Params.dc (P : Params) : ℝ := P.c1 - P.c2
def Params.drp (P : Params) : ℝ := P.r1p - P.r2p

/-- Care intensity, equation (1). -/
def intensity (P : Params) (ih ip : ℝ) : ℝ :=
  (1 - ih) * P.psi + (1 - P.psi) * ip

/-- Fee-for-service payoffs, equation (2). -/
def hospFFS (P : Params) (ih ip : ℝ) : ℝ :=
  P.rh - P.c1 * intensity P ih ip - P.c2 * (1 - intensity P ih ip) -
    P.wq * (intensity P ih ip - P.I0) ^ 2

def physFFS (P : Params) (ih ip : ℝ) : ℝ :=
  P.r1p * intensity P ih ip + P.r2p * (1 - intensity P ih ip) -
    P.wb * (intensity P ih ip - P.I0) ^ 2

/-- Bundled-payment payoffs, equation (3). -/
def hospBP (P : Params) (rBP T ih ip : ℝ) : ℝ :=
  rBP - (P.c1 + P.r1p) * intensity P ih ip -
    (P.c2 + P.r2p) * (1 - intensity P ih ip) -
    P.wq * (intensity P ih ip - P.I0) ^ 2 -
    (1 - intensity P ih ip) * T

def physBP (P : Params) (T ih ip : ℝ) : ℝ :=
  P.r1p * intensity P ih ip + P.r2p * (1 - intensity P ih ip) -
    P.wb * (intensity P ih ip - P.I0) ^ 2 +
    (1 - intensity P ih ip) * T

/-- Pure Nash equilibrium of the simultaneous fee-for-service effort game. -/
def IsNashFFS (P : Params) (ih ip : ℝ) : Prop :=
  IsNash (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
    (hospFFS P) (physFFS P) ih ip

/-- Pure Nash equilibrium of the bundled-payment continuation game at `T`. -/
def IsNashBP (P : Params) (rBP T ih ip : ℝ) : Prop :=
  IsNash (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)
    (hospBP P rBP T) (physBP P T) ih ip

/-- The hospital chooses gainsharing `T ≥ 0`; `σ` selects a Nash equilibrium after
every feasible choice, and the chosen `T` maximizes the hospital's payoff. -/
def IsSPNE (P : Params) (rBP : ℝ) (σ : ℝ → ℝ × ℝ) (T : ℝ) : Prop :=
  IsTwoStageSPNE (Set.Ici (0 : ℝ)) (IsNashBP P rBP)
    (hospBP P rBP) σ T

/-- Total payer payment under FFS, equation (48). -/
def rFFS (P : Params) (ih ip : ℝ) : ℝ :=
  P.rh + P.r1p * intensity P ih ip + P.r2p * (1 - intensity P ih ip)

/-- Bundled payment at which the hospital breaks even relative to a FFS profile. -/
def breakEvenBP (P : Params) (ihF ipF T ih ip : ℝ) : ℝ :=
  hospFFS P ihF ipF - hospBP P 0 T ih ip

/-- The payer's potential savings at the hospital's break-even bundled payment. -/
def savings (P : Params) (ihF ipF T ih ip : ℝ) : ℝ :=
  rFFS P ihF ipF - breakEvenBP P ihF ipF T ih ip

noncomputable def psiBar (P : Params) : ℝ :=
  1 - P.I0 - P.drp / (2 * P.wb)

noncomputable def psiPlus (P : Params) : ℝ :=
  (2 * P.wb * (1 - P.I0) + P.dc) / (4 * P.wb)

noncomputable def psi0 (P : Params) : ℝ :=
  (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb * (P.dc + P.drp))

noncomputable def Tsharp (P : Params) : ℝ :=
  (-2 * P.wb * (1 - P.I0) + P.dc + 2 * P.drp) / 2

noncomputable def ipSharp (P : Params) : ℝ :=
  (2 * (1 + P.I0) * P.wb - P.dc) / (4 * P.wb * (1 - P.psi))

end BundledPay.Base


