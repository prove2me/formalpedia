-- Prove2me | Definitions.Def_Teletriage_OneShot_Model
-- name    : Teletriage_OneShot_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:50.599516+00:00
-- url     : https://prove2.me/theorems/593046f6-0a8c-4abb-bc05-142aa5bc3e14
-- title:
--   §3.2.1, §3.3, §4.1, pp. 7–11 — one-shot open-access patient choice among PCP, ED and error-prone teletriage; thresholds b0, b̲0, b̄0, β⁰, α⁰
-- statement:
--   This is the one-shot, open-access model of Çakıcı and Mills for a patient with a single illness of uncertain severity.
--
--   **Costs and states.** A patient is either sick ($S$) or critical ($C$) and holds a **belief** $b\in[0,1]$, the probability that she is critical. Visiting the primary care provider (PCP) costs the copay $c_P$; going to the emergency department (ED) costs $c_E$; calling the teletriage line costs $c_T$. A critical patient who visits the PCP is sent on to the ED (she **double-dips**), so the expected cost of the PCP at belief $b$ is $c_P+b\,c_E$. Without teletriage the patient's cost is, by (1),
--   $$V_0(b)=\min\{c_E,\;c_P+b\,c_E\}.$$
--
--   **Teletriage.** Teletriage predicts *sick* (PS) or *critical* (PC) with **undertriage rate** $\alpha=\Pr(PS\mid C)$ and **overtriage rate** $\beta=\Pr(PC\mid S)$. A patient with belief $b$ receives PS with probability $\alpha b+(1-\beta)(1-b)$ and PC with probability $(1-\alpha)b+\beta(1-b)$, and updates her belief by Bayes' rule, (10):
--   $$b_{PS}=\frac{\alpha b}{\alpha b+(1-\beta)(1-b)},\qquad b_{PC}=\frac{(1-\alpha)b}{(1-\alpha)b+\beta(1-b)}.$$
--   After a call she can no longer call again and takes the action that is optimal for her posterior without teletriage. Her cost with teletriage available is (11):
--   $$\tilde V_0(b)=\min\bigl\{c_E,\;c_P+b\,c_E,\;c_T+(\alpha b+(1-\beta)(1-b))V_0(b_{PS})+((1-\alpha)b+\beta(1-b))V_0(b_{PC})\bigr\}.$$
--
--   **Actions and probabilities.** The optimal action without teletriage is the ED when $c_E\le c_P+b c_E$ and the PCP otherwise; with teletriage it is the argmin of (11). From the action at $b$ (and, after a call, the actions at $b_{PS}$ and $b_{PC}$) one obtains the probabilities $\pi^{ED}(b)$, $\pi^{DD}(b)$ that a patient with belief $b$ ends up at the ED, resp. double-dips, without teletriage, and $\tilde\pi^{ED}(b)$, $\tilde\pi^{DD}(b)$ with it. For beliefs distributed uniformly on $[l,u]$, the population quantities are the averages $\pi=\frac1{u-l}\int_l^u\pi(s)\,ds$.
--
--   **Thresholds.** The model's thresholds are $b_0=1-c_P/c_E$ (§4.1), the two thresholds of (14)
--   $$\underline b_0=\frac{\beta b_0+\frac{c_T}{c_P}(1-b_0)}{\beta b_0+(1-\alpha)(1-b_0)},\qquad \bar b_0=\frac{(1-\beta)b_0-\frac{c_T}{c_P}(1-b_0)}{(1-\beta)b_0+\alpha(1-b_0)},$$
--   the auxiliary thresholds $\underline{\underline b}_0=\frac{\beta b_0}{\beta b_0+(1-\alpha)(1-b_0)}$ and $\bar{\bar b}_0=\frac{(1-\beta)b_0}{(1-\beta)b_0+\alpha(1-b_0)}$ of the proof of Proposition 2, and the error-rate thresholds (15)–(16)
--   $$\beta^0=\frac{u-\frac{u^2}{2}-\bigl(b_0-\frac{b_0^2}{2}\bigr)}{u-\frac{u^2}{2}-\bigl(l-\frac{l^2}{2}\bigr)},\qquad \alpha^0=\frac{b_0^2-l^2}{u^2-l^2}.$$
--
--   **Standing assumptions.** $0<c_P<c_E$, $0\le c_T$ and $\alpha,\beta\in[0,1]$. Teletriage is **informative** when $\alpha+\beta<1$ (Proposition 1).
--
--   This definition is the common substrate of every statement of the mission: the goal (Proposition 3) and its milestones are all about these objects.
--
--   **Formalization Note** All quantities are real numbers. The three added standing assumptions are $0<c_P$ (the thresholds (14) divide by $c_P$), $c_P<c_E$ (stated in passing on p. 12; it makes $b_0\in(0,1)$) and $0\le c_T$ (a copayment; with $c_T<0$ the display of $\tilde\pi^{ED}$ on p. 11 fails). Ties in the argmin are broken ED ≻ teletriage ≻ PCP, and ED over PCP without teletriage, which is the convention of the displays on p. 11. The probabilities $\pi^{ED},\pi^{DD},\tilde\pi^{ED},\tilde\pi^{DD}$ are computed from the optimal actions, never defined by the closed forms of p. 11. Lean's division returns $0$ on a zero denominator; $b_{PS}$ and $b_{PC}$ are only ever used multiplied by the probability of the corresponding prediction, so a junk posterior never affects a cost or a probability. The average $\frac1{u-l}\int_l^u g$ is the paper's $\int_0^1 g(s)f(s)\,ds$ with the Uniform$[l,u]$ density $f$.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), pp. 6–11 (PDF 6–11), §3.2, §3.2.1, §3.3, §4.1, (1), (10), (11), (14)–(16); proof of Proposition 2, p. ec1 (PDF 26)

import Mathlib

namespace Teletriage.OneShot

/-- Parameters of the one-shot open-access model of §3.2.1 and §3.3 (one illness type, §4):
copays `cP` (PCP), `cE` (ED), `cT` (teletriage), undertriage rate `α = Pr(PS | C)` and
overtriage rate `β = Pr(PC | S)`. -/
structure Params where
  cP : ℝ
  cE : ℝ
  cT : ℝ
  α : ℝ
  β : ℝ

/-- Standing assumptions: `0 < cP < cE`, `0 ≤ cT`, and `α, β ∈ [0, 1]`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.cP ∧ P.cP < P.cE ∧ 0 ≤ P.cT ∧ 0 ≤ P.α ∧ P.α ≤ 1 ∧ 0 ≤ P.β ∧ P.β ≤ 1

/-- Teletriage is informative in the sense of Proposition 1: `α + β < 1`. -/
def Params.Informative (P : Params) : Prop := P.α + P.β < 1

/-- Probability of the prediction "sick" for a patient with belief `b` (Table 2). -/
def probPS (P : Params) (b : ℝ) : ℝ := P.α * b + (1 - P.β) * (1 - b)

/-- Probability of the prediction "critical" for a patient with belief `b` (Table 2). -/
def probPC (P : Params) (b : ℝ) : ℝ := (1 - P.α) * b + P.β * (1 - b)

/-- Posterior belief after the prediction "sick", (10). -/
noncomputable def bPS (P : Params) (b : ℝ) : ℝ := P.α * b / probPS P b

/-- Posterior belief after the prediction "critical", (10). -/
noncomputable def bPC (P : Params) (b : ℝ) : ℝ := (1 - P.α) * b / probPC P b

/-- Expected cost of visiting the open-access PCP at belief `b`: `cP + b cE`. -/
def costPCP (P : Params) (b : ℝ) : ℝ := P.cP + b * P.cE

/-- Value without teletriage, (1): `V0(b) = min {cE, cP + b cE}`. -/
noncomputable def V0 (P : Params) (b : ℝ) : ℝ := min P.cE (costPCP P b)

/-- Expected cost of calling teletriage at belief `b`, the third term of (11). -/
noncomputable def costTT (P : Params) (b : ℝ) : ℝ :=
  P.cT + probPS P b * V0 P (bPS P b) + probPC P b * V0 P (bPC P b)

/-- The patient's actions in the one-shot model. -/
inductive Action
  | PCP
  | ED
  | TT

/-- Optimal action without teletriage (argmin of (1)), ED on a tie. -/
noncomputable def actNoTT (P : Params) (b : ℝ) : Action :=
  if P.cE ≤ costPCP P b then .ED else .PCP

/-- Optimal action with teletriage (argmin of (11)), ties broken ED ≻ TT ≻ PCP. -/
noncomputable def actTT (P : Params) (b : ℝ) : Action :=
  if P.cE ≤ costPCP P b ∧ P.cE ≤ costTT P b then .ED
  else if costTT P b ≤ costPCP P b then .TT else .PCP

/-- `π^ED(b)` without teletriage, computed from the optimal action. -/
noncomputable def piED (P : Params) (b : ℝ) : ℝ :=
  match actNoTT P b with
  | .ED => 1
  | .PCP => b
  | .TT => 0

/-- `π^DD(b)` without teletriage, computed from the optimal action. -/
noncomputable def piDD (P : Params) (b : ℝ) : ℝ :=
  match actNoTT P b with
  | .ED => 0
  | .PCP => b
  | .TT => 0

/-- `π̃^ED(b)` with teletriage: after a call the patient follows the no-teletriage rule at
her posterior (she cannot call twice). -/
noncomputable def piEDtt (P : Params) (b : ℝ) : ℝ :=
  match actTT P b with
  | .TT => probPS P b * piED P (bPS P b) + probPC P b * piED P (bPC P b)
  | .ED => 1
  | .PCP => b

/-- `π̃^DD(b)` with teletriage, computed as for `piEDtt`. -/
noncomputable def piDDtt (P : Params) (b : ℝ) : ℝ :=
  match actTT P b with
  | .TT => probPS P b * piDD P (bPS P b) + probPC P b * piDD P (bPC P b)
  | .ED => 0
  | .PCP => b

/-- Population average `∫₀¹ g(s) f(s) ds` under the Uniform[l, u] belief density
`f = 1/(u − l)` on `(l, u)`. -/
noncomputable def avg (g : ℝ → ℝ) (l u : ℝ) : ℝ := (u - l)⁻¹ * ∫ s in l..u, g s

/-- `b0 = 1 − cP/cE`, §4.1. -/
noncomputable def b0 (P : Params) : ℝ := 1 - P.cP / P.cE

/-- `b̲0` of (14). -/
noncomputable def bLow (P : Params) : ℝ :=
  (P.β * b0 P + P.cT / P.cP * (1 - b0 P)) / (P.β * b0 P + (1 - P.α) * (1 - b0 P))

/-- `b̄0` of (14). -/
noncomputable def bHigh (P : Params) : ℝ :=
  ((1 - P.β) * b0 P - P.cT / P.cP * (1 - b0 P)) / ((1 - P.β) * b0 P + P.α * (1 - b0 P))

/-- `b̲̲0`, proof of Proposition 2. -/
noncomputable def bLowLow (P : Params) : ℝ :=
  P.β * b0 P / (P.β * b0 P + (1 - P.α) * (1 - b0 P))

/-- `b̿0`, proof of Proposition 2. -/
noncomputable def bHighHigh (P : Params) : ℝ :=
  (1 - P.β) * b0 P / ((1 - P.β) * b0 P + P.α * (1 - b0 P))

/-- `β⁰` of (15). -/
noncomputable def betaSup0 (P : Params) (l u : ℝ) : ℝ :=
  ((u - u ^ 2 / 2) - (b0 P - b0 P ^ 2 / 2)) / ((u - u ^ 2 / 2) - (l - l ^ 2 / 2))

/-- `α⁰` of (16). -/
noncomputable def alphaSup0 (P : Params) (l u : ℝ) : ℝ := (b0 P ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)

end Teletriage.OneShot


