-- Prove2me | Definitions.Def_FrictionInvest_Benefit_Model
-- name    : FrictionInvest_Benefit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:21.705994+00:00
-- url     : https://prove2.me/theorems/fd83afb3-1d9e-4bf3-b2ee-043f7b1ffaaa
-- title:
--   §3, pp. 91–95 — capital-constrained firm and cost-reduction investment
-- statement:
--   A firm sells a quantity $q$ at unit price $p$ into demand $\xi\sim U[0,a]$. It starts with capital $y_1$ and unit production cost $c_1$. Investing an amount $A$ lowers the cost to $c_2=c_1-\beta A>0$ and leaves capital $y_2=y_1-A\ge0$. Sales revenue is $p\min(q,\xi)$.
--
--   For production cost $c$ and capital $y$, the loan principal is $cq-y$ when positive. The bank's expected receipt is the uniform-demand expectation in equation (2). Its face value $F(q)$ is the lower root of that equation in the borrowing region. The expected bankruptcy cost is $K(q)=\mathbb E[\gamma p\min(q,\xi)\mathbf 1_{p\min(q,\xi)\le F(q)}]$, with $\gamma\in[0,1]$. Production profit is
--   $$J_\gamma(c,y,q)=\mathbb E[p\min(q,\xi)]-cq-K(q).$$
--   A feasible quantity either needs no loan or satisfies the bank's lending conditions; an equilibrium quantity maximizes $J_\gamma$ over all feasible nonnegative quantities.
--
--   The marginal return is $\mathrm{MRR}(q)=p(1-q/a)-c$. The marginal financing cost $\mathrm{MCE}$, operational effect $\Delta R_1$, friction effect $\Delta R_2$, and investment's net benefit $\Pi$ complete the model. $\Delta R_2$ is the four-integral formula (8), and $\Pi$ subtracts $A$ exactly once. These definitions support the paper's structural results.
--
--   **Formalization Note** The face value uses the lower closed-form root of (2). For self-financed production, $F=0$ and $\mathrm{MCE}=0$; the positive-loan formula is extended continuously there. Expectations are normalized interval integrals under $U[0,a]$. The reduced cost and remaining-capital restrictions are bundled in the standing predicate.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, pp. 91–95 (PDF 4–8), §3, Assumptions 1–3 and equations (1)–(8)

import Mathlib

namespace FrictionInvest.Benefit

/-- Data of the firm's investment and production problem (§3, p. 91). -/
structure Params where
  p : ℝ
  a : ℝ
  c1 : ℝ
  y1 : ℝ
  A : ℝ
  β : ℝ

def Params.c2 (P : Params) : ℝ := P.c1 - P.β * P.A
def Params.y2 (P : Params) : ℝ := P.y1 - P.A

/-- Positivity, the reduced positive production cost, and nonnegative capital after investment. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ 0 < P.a ∧ 0 < P.c1 ∧ 0 < P.A ∧ 0 < P.β ∧ 0 < P.c2 ∧ P.A ≤ P.y1

/-- Sales revenue at quantity `q` and realized demand `ξ`. -/
def revenue (P : Params) (q ξ : ℝ) : ℝ := P.p * min q ξ

/-- The bank's expected receipt, the left side of equation (2). -/
noncomputable def bankReceipt (P : Params) (γ q F : ℝ) : ℝ :=
  (1 / P.a) * ∫ ξ in (0)..P.a,
    (min (revenue P q ξ) F - γ * revenue P q ξ *
      (if revenue P q ξ ≤ F then 1 else 0))

/-- The smaller solution of (2) in the lending region; zero if production is self financed. -/
noncomputable def faceValue (P : Params) (γ c y q : ℝ) : ℝ :=
  if c * q ≤ y then 0 else
    P.a * P.p / (1 + γ) *
      (1 - Real.sqrt (1 - 2 * (1 + γ) * (c * q - y) / (P.a * P.p)))

/-- Quantities at which the firm either needs no loan or satisfies Assumptions 2 and 3. -/
def Feasible (P : Params) (γ c y q : ℝ) : Prop :=
  0 ≤ q ∧ (c * q ≤ y ∨
    (2 * (1 + γ) * (c * q - y) < P.a * P.p ∧
      faceValue P γ c y q < q * P.p))

/-- Expected bankruptcy cost `K(q)` under uniform demand, equation (4). -/
noncomputable def bankCost (P : Params) (γ c y q : ℝ) : ℝ :=
  (1 / P.a) * ∫ ξ in (0)..P.a,
    γ * revenue P q ξ *
      (if revenue P q ξ ≤ faceValue P γ c y q then 1 else 0)

/-- Expected production profit before paying the investment amount, equation (4). -/
noncomputable def expProfit (P : Params) (γ c y q : ℝ) : ℝ :=
  (1 / P.a) * (∫ ξ in (0)..P.a, revenue P q ξ) - c * q - bankCost P γ c y q

/-- A feasible quantity maximizing expected profit over every feasible production quantity. -/
def IsEqQuantity (P : Params) (γ c y q : ℝ) : Prop :=
  Feasible P γ c y q ∧
    ∀ q' : ℝ, Feasible P γ c y q' → expProfit P γ c y q' ≤ expProfit P γ c y q

/-- Marginal rate of return on production, equation (5). -/
noncomputable def mrr (P : Params) (c q : ℝ) : ℝ := P.p * (1 - q / P.a) - c

/-- Marginal cost of external funds. Its continuous extension is zero without a loan. -/
noncomputable def mce (P : Params) (γ c y q : ℝ) : ℝ :=
  γ * c * faceValue P γ c y q /
    (P.a * P.p - (1 + γ) * faceValue P γ c y q)

/-- Friction effect `ΔR₂`, exactly the four integrals of equation (8). -/
noncomputable def frictionEffect (P : Params) (γ q0 qA : ℝ) : ℝ :=
  (∫ q in q0..(P.a * (P.p - P.c1) / P.p), mrr P P.c1 q)
  - (∫ q in qA..(P.a * (P.p - P.c2) / P.p), mrr P P.c2 q)
  + (∫ q in (0)..q0, mce P γ P.c1 P.y1 q)
  - (∫ q in (0)..qA, mce P γ P.c2 P.y2 q)

/-- Operational effect `ΔR₁` at the perfect-market optima. -/
noncomputable def opEffect (P : Params) (q0' qA' : ℝ) : ℝ :=
  expProfit P 0 P.c2 P.y2 qA' - expProfit P 0 P.c1 P.y1 q0'

/-- Investment's net benefit `Π`, after paying `A` once. -/
noncomputable def netBenefit (P : Params) (γ q0 qA : ℝ) : ℝ :=
  (expProfit P γ P.c2 P.y2 qA - P.A) - expProfit P γ P.c1 P.y1 q0

end FrictionInvest.Benefit


