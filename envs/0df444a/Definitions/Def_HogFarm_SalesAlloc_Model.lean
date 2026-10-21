-- Prove2me | Definitions.Def_HogFarm_SalesAlloc_Model
-- name    : HogFarm_SalesAlloc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:19.590806+00:00
-- url     : https://prove2.me/theorems/64982797-45d2-418a-9efe-cb4dfc647376
-- title:
--   §5–§6 model: prices, stock, Bellman value and break-even levels
-- statement:
--   The model has a weekly contract quantity $q$, underweight discount $\alpha$, discount factor $\beta$, prices $P_t=(p^C_t,p^1_t,p^2_t,c^H_t,c^P_t)$, and newly available hogs $W_t$. Decisions $y^i_t$ go to the contract and $z^i_t$ are held. All decisions are nonnegative, $y^1_t+y^2_t\le q$ and $y^i_t+z^i_t\le s^i_t$. Open-market sales are $s^i_t-y^i_t-z^i_t$. The reward is
--
--   $$r_t=p^C_t(y^2_t+(1-\alpha)y^1_t)+\sum_{i=1}^2p^i_t(s^i_t-y^i_t-z^i_t)-c^H_t(z^1_t+z^2_t)-c^P_t(q-y^1_t-y^2_t).$$
--
--   Held hogs of either class become regular-weight stock next week. The Bellman value $V_t$ maximizes this reward plus discounted continuation value and has terminal value zero. The net holding value $G_t(Z)$ is the continuation value minus feeding cost. Break-even levels are the first total holdings where every forward increment of $G_t$ falls below a chosen sales margin.
--
--   These definitions supply the common model for the policy theorem and its milestones. **Formalization Note** The information state can encode history. Boundedness, measurability, nonnegativity, positive contract size and horizon, and $0<\beta\le1$ are disclosed additions; Assumption 1 and corrected bound A* are separate predicates.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), pp. 9, 12–17 (PDF 9, 12–17), §5–§6, Assumption 1, eqs. (4), (5), (7a)–(7c), (8a)–(8b)

import Mathlib

namespace HogFarm.SalesAlloc

open MeasureTheory ProbabilityTheory

/-- Observed prices and costs (5). -/
structure Prices where
  pC : ℝ
  p1 : ℝ
  p2 : ℝ
  cH : ℝ
  cP : ℝ

/-- The farm in §5. The exogenous state can contain the entire observed history;
time-indexed Markov kernels thus also represent adapted, nonstationary data. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  T : ℕ
  q : ℝ
  α : ℝ
  β : ℝ
  κ : ℕ → Kernel Ω Ω
  price : ℕ → Ω → Prices
  W1 : ℕ → Ω → ℝ
  W2 : ℕ → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The single-period reward (7c), with open-market sales `sᵢ-yᵢ-zᵢ`. -/
def reward (P : Prices) (q α s1 s2 y1 y2 z1 z2 : ℝ) : ℝ :=
  P.pC * (y2 + (1 - α) * y1) +
    (P.p1 * (s1 - y1 - z1) + P.p2 * (s2 - y2 - z2)) -
    (P.cH * z1 + P.cH * z2) - P.cP * (q - y1 - y2)

/-- Constraints (7a), including decision nonnegativity on p. 40. -/
def Feasible (q s1 s2 y1 y2 z1 z2 : ℝ) : Prop :=
  0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ z1 ∧ 0 ≤ z2 ∧
    y1 + y2 ≤ q ∧ y1 + z1 ≤ s1 ∧ y2 + z2 ≤ s2

/-- Bellman value with `n` periods remaining. Held hogs enter the next
period as regular-weight hogs, as in (4). -/
noncomputable def valueAux (M : Model Ω) : ℕ → ℕ → ℝ → ℝ → Ω → ℝ
  | 0, _, _, _, _ => 0
  | n + 1, t, s1, s2, ω =>
      sSup {v : ℝ | ∃ y1 y2 z1 z2 : ℝ,
        Feasible M.q s1 s2 y1 y2 z1 z2 ∧
        v = reward (M.price t ω) M.q M.α s1 s2 y1 y2 z1 z2 +
          M.β * ∫ ω', valueAux M n (t + 1) (M.W1 (t + 1) ω')
            (M.W2 (t + 1) ω' + z1 + z2) ω' ∂(M.κ t ω)}

/-- `Vₜ` of (7a); the terminal value `V_{T+1}` is zero. -/
noncomputable def value (M : Model Ω) (t : ℕ) (s1 s2 : ℝ) (ω : Ω) : ℝ :=
  valueAux M (M.T + 1 - t) t s1 s2 ω

/-- Discounted expected next-period value at total holding `Z`. -/
noncomputable def cont (M : Model Ω) (t : ℕ) (ω : Ω) (Z : ℝ) : ℝ :=
  M.β * ∫ ω', value M (t + 1) (M.W1 (t + 1) ω')
    (M.W2 (t + 1) ω' + Z) ω' ∂(M.κ t ω)

/-- Action value (7b). -/
noncomputable def actionValue (M : Model Ω) (t : ℕ) (ω : Ω)
    (s1 s2 y1 y2 z1 z2 : ℝ) : ℝ :=
  reward (M.price t ω) M.q M.α s1 s2 y1 y2 z1 z2 + cont M t ω (z1 + z2)

/-- Optimality means feasible attainment of the Bellman value. -/
def IsOptimal (M : Model Ω) (t : ℕ) (ω : Ω)
    (s1 s2 y1 y2 z1 z2 : ℝ) : Prop :=
  Feasible M.q s1 s2 y1 y2 z1 z2 ∧
    actionValue M t ω s1 s2 y1 y2 z1 z2 = value M t s1 s2 ω

/-- Holding value net of feeding cost; increments are Table 2's H-margin. -/
noncomputable def holdGain (M : Model Ω) (t : ℕ) (ω : Ω) (Z : ℝ) : ℝ :=
  cont M t ω Z - (M.price t ω).cH * Z

/-- All forward holding increments at `Z` have marginal value at most `v`. -/
def MarginLE (G : ℝ → ℝ) (v Z : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → G (Z + δ) - G Z ≤ v * δ

/-- First nonnegative holding level at which the H-margin falls to `v`. -/
noncomputable def breakEvenOf (G : ℝ → ℝ) (v : ℝ) : ℝ :=
  sInf {Z : ℝ | 0 ≤ Z ∧ MarginLE G v Z}

/-- A finite stock cannot exceed `cap`; a crossing beyond it is
operationally equivalent to no crossing. -/
noncomputable def levelOf (G : ℝ → ℝ) (cap v : ℝ) : ℝ :=
  sInf (insert cap {Z : ℝ | 0 ≤ Z ∧ MarginLE G v Z})

/-- The one-period objective isolated in Proposition 1's Step 2 proof. -/
def onePeriodObjective (P : Prices) (q α s1 s2 : ℝ) (G : ℝ → ℝ)
    (y1 y2 z1 z2 : ℝ) : ℝ :=
  P.pC * (y2 + (1 - α) * y1) +
    P.p1 * (s1 - y1 - z1) + P.p2 * (s2 - y2 - z2) -
    P.cP * (q - y1 - y2) + G (z1 + z2)

/-- Feasible attainment of the isolated one-period objective. -/
def OnePeriodOptimal (P : Prices) (q α s1 s2 : ℝ) (G : ℝ → ℝ)
    (y1 y2 z1 z2 : ℝ) : Prop :=
  Feasible q s1 s2 y1 y2 z1 z2 ∧
  ∀ a b c d : ℝ, Feasible q s1 s2 a b c d →
    onePeriodObjective P q α s1 s2 G a b c d ≤
      onePeriodObjective P q α s1 s2 G y1 y2 z1 z2

/-- Standing assumptions from pp. 9–15, with the disclosed nonnegative,
bounded, measurable data and positive horizon. -/
def Model.Standing (M : Model Ω) : Prop :=
  0 < M.T ∧ 0 < M.q ∧ 0 < M.α ∧ M.α < 1 ∧ 0 < M.β ∧ M.β ≤ 1 ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℕ, ∀ ω : Ω,
    let P := M.price t ω
    0 ≤ P.p1 ∧ P.p1 ≤ P.p2 ∧ 0 ≤ P.pC ∧ 0 ≤ P.cH ∧ 0 ≤ P.cP ∧
    0 ≤ M.W1 t ω ∧ 0 ≤ M.W2 t ω ∧
    P.p1 ≤ B ∧ P.p2 ≤ B ∧ P.pC ≤ B ∧ P.cH ≤ B ∧ P.cP ≤ B ∧
    M.W1 t ω ≤ B ∧ M.W2 t ω ≤ B) ∧
  (∀ t : ℕ, Measurable (fun ω => (M.price t ω).pC) ∧
    Measurable (fun ω => (M.price t ω).p1) ∧
    Measurable (fun ω => (M.price t ω).p2) ∧
    Measurable (fun ω => (M.price t ω).cH) ∧
    Measurable (fun ω => (M.price t ω).cP) ∧
    Measurable (M.W1 t) ∧ Measurable (M.W2 t) ∧ IsMarkovKernel (M.κ t))

/-- Assumption 1, p. 14, at each nonterminal period and information state. -/
noncomputable def Model.Assumption1 (M : Model Ω) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t < M.T → ∀ ω : Ω,
    (∫ ω', (M.price (t + 1) ω').pC ∂(M.κ t ω)) - (M.price t ω).pC ≤
      (M.price t ω).cH ∧
    (∫ ω', (M.price (t + 1) ω').p2 ∂(M.κ t ω)) - (M.price t ω).p2 ≤
      (M.price t ω).cH

/-- Corrected no-arbitrage bound A*: it also controls the next-period
penalty, which Assumption 1 does not. -/
noncomputable def Model.AStar (M : Model Ω) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t < M.T → ∀ ω : Ω,
    M.β * ∫ ω', max ((M.price (t + 1) ω').pC + (M.price (t + 1) ω').cP)
      (M.price (t + 1) ω').p2 ∂(M.κ t ω) ≤
      max ((M.price t ω).pC + (M.price t ω).cP) (M.price t ω).p2 +
        (M.price t ω).cH

end HogFarm.SalesAlloc


