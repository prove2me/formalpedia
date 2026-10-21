-- Prove2me | Definitions.Def_SalesTrust_Sharing_Model
-- name    : SalesTrust_Sharing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:21.535319+00:00
-- url     : https://prove2.me/theorems/ce61134f-b45b-4eca-9687-7aac60216df1
-- title:
--   §3–§4, pp. 6–16 — repeated manufacturer–retailer screening with linear demand: menus, static program (1)–(2), dynamic IR (6) and IC (7), optimal menus, δ̃
-- statement:
--   The model of Shamir and Yehezkel: a manufacturer sells to a retailer in every period of an infinitely repeated game, and the retailer privately observes the demand state of each period.
--
--   **Primitives.** Demand is high ($H$) with probability $p$ and low ($L$) with probability $1-p$, i.i.d. across periods. The inverse demand in state $\theta$ is $P(q;\theta) = V_\theta - q$ with $V_H > V_L$, so the retailer's revenue from quantity $q$ is
--   $$\pi_R(q;\theta) = (V_\theta - q)\,q, \qquad \Delta(q) = \pi_R(q;H) - \pi_R(q;L).$$
--   Both firms discount with the common factor $\delta$. The **standing assumptions** are $0<p<1$, $V_L < V_H$, $pV_H < V_L$ and $0 \le \delta < 1$.
--
--   **Menus and payoffs.** A menu is $\{(q_H,T_H),(q_L,T_L)\}$: quantity $q_\theta$ for the transfer $T_\theta$. The retailer's and the manufacturer's ex-ante per-period profits are
--   $$\Pi_R = p\,(\pi_R(q_H;H) - T_H) + (1-p)\,(\pi_R(q_L;L) - T_L), \qquad \Pi_M = pT_H + (1-p)T_L.$$
--
--   **Static benchmark.** $q^S_L = \frac{V_L}{2} - \frac{p}{1-p}\frac{V_H - V_L}{2}$ (equation (4)), and the static menu is $(q^S_H, T^S_H) = (V_H/2,\ V_H^2/4 - (V_L - pV_H)(V_H - V_L)/(2(1-p)))$, $(q^S_L, T^S_L) = (q^S_L,\ V_L^2/4 - p^2(V_H-V_L)^2/(4(1-p)^2))$ (equations (4)–(5)). The static program maximizes $\Pi_M$ subject to the participation constraints $IR^S_\theta$, $\pi_R(q_\theta;\theta) - T_\theta \ge 0$ (1), and the incentive constraints $IC^S_\theta$, $\pi_R(q_\theta;\theta) - T_\theta \ge \pi_R(q_{\tilde\theta};\theta) - T_{\tilde\theta}$ for $\tilde\theta \ne \theta$ (2).
--
--   **Dynamic constraints.** A deviation is punished by reversion to the static menu, worth $p\Delta(q^S_L)$ per period to the retailer. The dynamic participation constraints (6) and incentive constraints (7) are
--   $$IR^D_\theta:\ \pi_R(q_\theta;\theta) - T_\theta + \tfrac{\delta}{1-\delta}\Pi_R \ \ge\ \tfrac{\delta}{1-\delta}\,p\Delta(q^S_L),$$
--   $$IC^D_\theta:\ \pi_R(q_\theta;\theta) - T_\theta + \tfrac{\delta}{1-\delta}\Pi_R \ \ge\ \pi_R(q_{\tilde\theta};\theta) - T_{\tilde\theta} + \tfrac{\delta}{1-\delta}\,p\Delta(q^S_L).$$
--   Without sales information the manufacturer maximizes $\Pi_M$ subject to $IR^D_\theta$ and the static $IC^S_\theta$ (program (8)–(9)); with sales information, subject to $IR^D_\theta$ and $IC^D_\theta$ (program (17)–(18)). A menu is **optimal** for a program if it satisfies its constraints and maximizes $\Pi_M$ among all menus that do.
--
--   **Closed forms.** The file also records the binding transfers (27) and (29) as functions of $(q_H,q_L)$, the menus of Propositions 1 and 2 ((11)–(12) and (20)–(21)), and the threshold $\tilde\delta = 1/(1+\sqrt{1+p})$ of (22).
--
--   These objects are the common vocabulary of every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers. The demand is linear (the paper's results are stated for the linear model). Menus carry the nonnegativity condition $q_H, q_L \ge 0$, an addition that does not bind at the optima. Transfers are unrestricted reals. $\delta < 1$ is added to the paper's $0 \le \delta \le 1$ because the constraints divide by $1-\delta$. $pV_H < V_L$ is footnote 2 of the paper (the manufacturer sells in both states). Constraints are weak inequalities, as printed.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), pp. 6–17 (PDF 7–18), §3, §4, (1)–(2), (4)–(9), (11)–(12), (17)–(18), (20)–(22); Online Supplement p. 6 (PDF 40), (27), (29)

import Mathlib

namespace SalesTrust.Sharing

noncomputable section

/-- The primitives of the model (Shamir–Yehezkel §3, pp. 6–8): the probability `p` of the
high demand state, the intercepts `VH`, `VL` of the linear inverse demand `P(q; θ) = V_θ − q`,
and the common discount factor `δ`. -/
structure Params where
  /-- probability of the high demand state `H` -/
  p : ℝ
  /-- demand intercept in state `H` -/
  VH : ℝ
  /-- demand intercept in state `L` -/
  VL : ℝ
  /-- common discount factor -/
  δ : ℝ

/-- Standing assumptions: `0 < p < 1` (p. 6), `V_L < V_H` (p. 6), `p V_H < V_L` (footnote 2,
p. 8: the manufacturer sells in both states, `q^S_L > 0`), and `0 ≤ δ < 1` (p. 8 allows `δ = 1`;
`δ < 1` is needed because (6)–(7) divide by `1 − δ`). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ P.p < 1 ∧ P.VL < P.VH ∧ P.p * P.VH < P.VL ∧ 0 ≤ P.δ ∧ P.δ < 1

/-- Retailer revenue `π_R(q; θ) = (V_θ − q) q` with `V = V_θ` (linear demand, p. 6). -/
def piR (V q : ℝ) : ℝ := (V - q) * q

/-- The gap `Δ(q) = π_R(q; H) − π_R(q; L)` (p. 6). -/
def gap (P : Params) (q : ℝ) : ℝ := piR P.VH q - piR P.VL q

/-- The static low-state quantity `q^S_L = V_L/2 − (p/(1−p)) (V_H − V_L)/2`, (4), p. 8. -/
def qSL (P : Params) : ℝ := P.VL / 2 - P.p / (1 - P.p) * ((P.VH - P.VL) / 2)

/-- The static expected rent `p Δ(q^S_L)` (p. 9: `Π^S_R = p Δ(q^S_L)`), the per-period value the
retailer gets after a breakdown. -/
def staticRent (P : Params) : ℝ := P.p * gap P (qSL P)

/-- A screening menu `{(q_H, T_H), (q_L, T_L)}` (p. 7). -/
@[ext] structure Menu where
  qH : ℝ
  TH : ℝ
  qL : ℝ
  TL : ℝ

/-- The retailer's ex-ante per-period profit
`Π_R = p (π_R(q_H; H) − T_H) + (1 − p)(π_R(q_L; L) − T_L)` (p. 7). -/
def retailerProfit (P : Params) (m : Menu) : ℝ :=
  P.p * (piR P.VH m.qH - m.TH) + (1 - P.p) * (piR P.VL m.qL - m.TL)

/-- The manufacturer's ex-ante per-period profit `Π_M = p T_H + (1 − p) T_L` (p. 7). -/
def mfrProfit (P : Params) (m : Menu) : ℝ := P.p * m.TH + (1 - P.p) * m.TL

/-- Continuation value `δ/(1−δ) · Π_R` of staying on the dynamic menu (left side of (6), (7)). -/
def cont (P : Params) (m : Menu) : ℝ := P.δ / (1 - P.δ) * retailerProfit P m

/-- Punishment value `δ/(1−δ) · p Δ(q^S_L)` of reverting to the static menu forever
(right side of (6); (7) prints it as `δp/(1−δ) Δ(q^S_L)`). -/
def punish (P : Params) : ℝ := P.δ / (1 - P.δ) * staticRent P

/-- Static participation constraints `IR^S_θ`, (1), p. 8. -/
def IRS (P : Params) (m : Menu) : Prop :=
  0 ≤ piR P.VH m.qH - m.TH ∧ 0 ≤ piR P.VL m.qL - m.TL

/-- Static incentive compatibility constraints `IC^S_θ`, (2), p. 8 (also (9), p. 11):
first `IC^S_H`, then `IC^S_L`. -/
def ICS (P : Params) (m : Menu) : Prop :=
  piR P.VH m.qL - m.TL ≤ piR P.VH m.qH - m.TH ∧
  piR P.VL m.qH - m.TH ≤ piR P.VL m.qL - m.TL

/-- Dynamic participation constraints `IR^D_θ`, (6), p. 10 (also (8), (17)):
first `IR^D_H`, then `IR^D_L`. -/
def IRD (P : Params) (m : Menu) : Prop :=
  punish P ≤ piR P.VH m.qH - m.TH + cont P m ∧
  punish P ≤ piR P.VL m.qL - m.TL + cont P m

/-- Dynamic incentive compatibility constraints `IC^D_θ`, (7), p. 10 (also (18)):
first `IC^D_H`, then `IC^D_L`. -/
def ICD (P : Params) (m : Menu) : Prop :=
  piR P.VH m.qL - m.TL + punish P ≤ piR P.VH m.qH - m.TH + cont P m ∧
  piR P.VL m.qH - m.TH + punish P ≤ piR P.VL m.qL - m.TL + cont P m

/-- Quantities are nonnegative. -/
def Quantities (m : Menu) : Prop := 0 ≤ m.qH ∧ 0 ≤ m.qL

/-- Feasible menus of the static program (1)–(2), §3.3. -/
def FeasibleS (P : Params) (m : Menu) : Prop := Quantities m ∧ IRS P m ∧ ICS P m

/-- Feasible menus of the dynamic program without sales information, (8)–(9), §4.1. -/
def FeasibleNE (P : Params) (m : Menu) : Prop := Quantities m ∧ IRD P m ∧ ICS P m

/-- Feasible menus of the dynamic program with sales information, (17)–(18), §4.2. -/
def FeasibleE (P : Params) (m : Menu) : Prop := Quantities m ∧ IRD P m ∧ ICD P m

/-- `m` maximizes `p T_H + (1 − p) T_L` over the static program. -/
def IsOptimalS (P : Params) (m : Menu) : Prop :=
  FeasibleS P m ∧ ∀ m', FeasibleS P m' → mfrProfit P m' ≤ mfrProfit P m

/-- `m` maximizes `p T_H + (1 − p) T_L` over the no-sharing dynamic program (8)–(9). -/
def IsOptimalNE (P : Params) (m : Menu) : Prop :=
  FeasibleNE P m ∧ ∀ m', FeasibleNE P m' → mfrProfit P m' ≤ mfrProfit P m

/-- `m` maximizes `p T_H + (1 − p) T_L` over the sharing dynamic program (17)–(18). -/
def IsOptimalE (P : Params) (m : Menu) : Prop :=
  FeasibleE P m ∧ ∀ m', FeasibleE P m' → mfrProfit P m' ≤ mfrProfit P m

/-- The threshold `δ̃ = 1 / (1 + √(1 + p))`, (22), p. 17. -/
def deltaTilde (P : Params) : ℝ := 1 / (1 + Real.sqrt (1 + P.p))

/-- `T^S_H = V_H²/4 − (V_L − p V_H)(V_H − V_L)/(2(1 − p))`, (5), p. 8. -/
def TSH (P : Params) : ℝ :=
  P.VH ^ 2 / 4 - (P.VL - P.p * P.VH) * (P.VH - P.VL) / (2 * (1 - P.p))

/-- `T^S_L = V_L²/4 − p²(V_H − V_L)²/(4(1 − p)²)`, (5), p. 8. -/
def TSL (P : Params) : ℝ :=
  P.VL ^ 2 / 4 - P.p ^ 2 * (P.VH - P.VL) ^ 2 / (4 * (1 - P.p) ^ 2)

/-- The static menu (4)–(5), p. 8. -/
def menuS (P : Params) : Menu := ⟨P.VH / 2, TSH P, qSL P, TSL P⟩

/-- Transfers (27) (Online Supplement p. 6) solving `IR^D_L` and `IC^S_H` with equality:
`T^{D,ne}_L = π_R(q_L; L) + δp(Δ(q_L) − Δ(q^S_L))`. -/
def TneL (P : Params) (qL : ℝ) : ℝ :=
  piR P.VL qL + P.δ * P.p * (gap P qL - gap P (qSL P))

/-- `T^{D,ne}_H = π_R(q_H; H) − Δ(q_L) + δp(Δ(q_L) − Δ(q^S_L))`, (27). -/
def TneH (P : Params) (qH qL : ℝ) : ℝ :=
  piR P.VH qH - gap P qL + P.δ * P.p * (gap P qL - gap P (qSL P))

/-- Transfers (29) (Online Supplement p. 6) solving `IR^D_L` and `IC^D_H` with equality:
`T^{D,e}_L = π_R(q_L; L) + δp/(1+δp) (Δ(q_L) − Δ(q^S_L))`. -/
def TeL (P : Params) (qL : ℝ) : ℝ :=
  piR P.VL qL + P.δ * P.p / (1 + P.δ * P.p) * (gap P qL - gap P (qSL P))

/-- `T^{D,e}_H = π_R(q_H; H) − Δ(q_L) + 2δp/(1+δp) (Δ(q_L) − Δ(q^S_L))`, (29). -/
def TeH (P : Params) (qH qL : ℝ) : ℝ :=
  piR P.VH qH - gap P qL + 2 * P.δ * P.p / (1 + P.δ * P.p) * (gap P qL - gap P (qSL P))

/-- The no-sharing dynamic menu of Proposition 1, (11)–(12), p. 12. -/
def menuNE (P : Params) : Menu :=
  ⟨P.VH / 2,
   TSH P - P.δ * P.p * (1 - P.δ * P.p) * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p)),
   qSL P + P.δ * (P.p / (1 - P.p)) * ((P.VH - P.VL) / 2),
   TSL P + P.δ * P.p ^ 2 * (2 * (1 - P.δ * P.p) + P.δ) * (P.VH - P.VL) ^ 2
     / (4 * (1 - P.p) ^ 2)⟩

/-- The sharing dynamic menu of Proposition 2, (20)–(21), p. 16. -/
def menuE (P : Params) : Menu :=
  ⟨P.VH / 2,
   TSH P - (1 + P.p) / (1 + P.δ * P.p) ^ 2 *
     (P.δ * P.p * (1 - P.δ * P.p) * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p))),
   qSL P + (1 + P.p) / (1 + P.δ * P.p) * (P.δ * P.p / (1 - P.p)) * ((P.VH - P.VL) / 2),
   TSL P + (1 + P.p) / (1 + P.δ * P.p) ^ 2 *
     (P.δ * P.p ^ 2 * (2 + P.δ * (1 - P.p)) * (P.VH - P.VL) ^ 2 / (4 * (1 - P.p) ^ 2))⟩

end

end SalesTrust.Sharing


