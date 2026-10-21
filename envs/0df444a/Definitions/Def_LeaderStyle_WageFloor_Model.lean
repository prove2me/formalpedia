-- Prove2me | Definitions.Def_LeaderStyle_WageFloor_Model
-- name    : LeaderStyle_WageFloor_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:36.356535+00:00
-- url     : https://prove2.me/theorems/930ba991-baea-4fdc-a446-487afeaefe18
-- title:
--   §§3–4 — binary-effort employment model, six leadership styles, feasible contracts and cost
-- statement:
--   The model has a risk-neutral worker choosing high or low effort, a selfish leader who follows an announced action rule, and a principal minimizing expected wage payments. A contract consists of base salary $w$, high-output bonus $b$, and fixed leader wage $w_l$. High effort produces high output with probability $\rho$, while low effort always produces low output. Six styles specify praise, scolding, or no action after each output.
--
--   A contract is feasible when high effort is incentive compatible, the worker's expected utility is at least $\underline u$, the base salary satisfies $w\ge\underline w$, and the leader's fixed wage covers $\underline u_l$ plus her expected action cost. The principal's expected payment is
--
--   $$w+\rho b+w_l.$$
--
--   Strict preference compares a feasible contract of one style with every feasible contract of another; optimality requires a feasible contract whose cost is no greater than any feasible contract of any of the six styles. Conditions (F), (FF), (U), and (U′) are the paper's parameter inequalities.
--
--   **Formalization Note** The floor is a real number and constrains the base salary. The paper also mentions the limiting convention $\underline w=-\infty$, which this type does not represent. The model concerns §4's selfish, compliant leader. Positivity, probability, cost ordering, reservation utility, and $r+s<c/\rho$ are bundled as the standing assumptions.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), pp. 7–17 (PDF 9–19), §3 and §4.1–§4.4

import Mathlib

namespace LeaderStyle.WageFloor

/-- Parameters of the binary-effort employment model in §§3–4. -/
structure Params where
  c : ℝ
  rho : ℝ
  r : ℝ
  s : ℝ
  kFh : ℝ
  kFl : ℝ
  kUh : ℝ
  kUl : ℝ
  ur : ℝ
  wf : ℝ
  ul : ℝ

/-- The standing assumptions of §§3–4. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ 0 < P.rho ∧ P.rho < 1 ∧ 0 < P.r ∧ 0 < P.s ∧
  0 < P.kFh ∧ P.kFh ≤ P.kFl ∧ 0 < P.kUl ∧ P.kUl ≤ P.kUh ∧
  0 ≤ P.ur ∧ P.r + P.s < P.c / P.rho

inductive Action | none | praise | scold
  deriving DecidableEq

/-- The monetary benchmark 0 and the five leadership styles of §3. -/
inductive Style | none | F | FF | U | UU | FU
  deriving DecidableEq

def Style.onHigh : Style → Action
  | .none => .none
  | .F => .praise
  | .FF => .praise
  | .U => .none
  | .UU => .scold
  | .FU => .praise

def Style.onLow : Style → Action
  | .none => .none
  | .F => .none
  | .FF => .praise
  | .U => .scold
  | .UU => .scold
  | .FU => .scold

/-- The worker's nonmonetary payoff from an action. -/
def actionValue (P : Params) : Action → ℝ
  | .none => 0
  | .praise => P.r
  | .scold => -P.s

/-- The leader's cost of an action following high output. -/
def costHigh (P : Params) : Action → ℝ
  | .none => 0
  | .praise => P.kFh
  | .scold => P.kUh

/-- The leader's cost of an action following low output. -/
def costLow (P : Params) : Action → ℝ
  | .none => 0
  | .praise => P.kFl
  | .scold => P.kUl

def utilHigh (P : Params) (S : Style) (w b : ℝ) : ℝ :=
  w + P.rho * (b + actionValue P S.onHigh) +
    (1 - P.rho) * actionValue P S.onLow - P.c

def utilLow (P : Params) (S : Style) (w : ℝ) : ℝ :=
  w + actionValue P S.onLow

def leaderCost (P : Params) (S : Style) : ℝ :=
  P.rho * costHigh P S.onHigh + (1 - P.rho) * costLow P S.onLow

structure Contract where
  w : ℝ
  b : ℝ
  wl : ℝ

/-- The four contract constraints when the selfish leader follows the announced style. -/
def Feasible (P : Params) (S : Style) (x : Contract) : Prop :=
  utilLow P S x.w ≤ utilHigh P S x.w x.b ∧
  P.ur ≤ utilHigh P S x.w x.b ∧
  P.wf ≤ x.w ∧
  P.ul ≤ x.wl - leaderCost P S

/-- Total expected wage cost to the principal under high effort. -/
def cost (P : Params) (x : Contract) : ℝ :=
  x.w + P.rho * x.b + x.wl

/-- A feasible contract for A costs strictly less than every feasible B contract. -/
def Prefers (P : Params) (A B : Style) : Prop :=
  ∃ x, Feasible P A x ∧ ∀ y, Feasible P B y → cost P x < cost P y

/-- A feasible contract attains minimum cost across all six styles. -/
def IsOptimalStyle (P : Params) (A : Style) : Prop :=
  ∃ x, Feasible P A x ∧
    ∀ (B : Style) (y : Contract), Feasible P B y → cost P x ≤ cost P y

/-- Condition (F), p. 12. -/
def condF (P : Params) : Prop := P.kFh < P.r

/-- Condition (FF), p. 13. -/
def condFF (P : Params) : Prop :=
  P.rho * P.kFh + (1 - P.rho) * P.kFl < min P.r (P.ur - P.wf)

/-- Condition (U), p. 15. -/
def condU (P : Params) : Prop :=
  (1 - P.rho) * P.kUl + max (P.s - (P.wf - P.ur)) 0 < P.rho * P.s

/-- Condition (U′), p. 18. -/
def condU' (P : Params) : Prop :=
  (1 - P.rho) * (P.s + P.kUl) < P.wf - P.ur

end LeaderStyle.WageFloor


