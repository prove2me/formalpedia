-- Prove2me | Definitions.Def_ViceGoals_Personal_Model
-- name    : ViceGoals_Personal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:41.122272+00:00
-- url     : https://prove2.me/theorems/b1bce248-e37a-40da-baac-e8571684da0e
-- title:
--   Present-biased vice-good consumers and personal goals
-- statement:
--   A unit mass of identical consumers values quantity $q\ge0$ at $vq-q^2/2$. One unit causes delayed harm $h\ge0$, discounted by $\beta\in(0,1)$ when consuming and undiscounted when planning. With a personal goal $G\ge0$, consumption above the goal incurs $\lambda(q-G)^2$ for $\lambda>0$. The firm's marginal cost is zero. The standing model has $v>0$.
--
--   The benchmark period-4 and period-2 utilities are
--
--   $$U_4^B=vq-q^2/2-\beta hq-pq,\qquad U_2^B=vq-q^2/2-hq-pq.$$
--
--   With a goal, $U_4=U_4^B-\lambda(q-G)^2\mathbf1_{q>G}$ and $U_3=U_2^B-\lambda(q-G)^2\mathbf1_{q>G}$. Period-4 quantity and period-3 goal are global maximizers over their nonnegative domains. Demand equals the chosen quantity exactly when anticipated planning utility is nonnegative, including indifference. Equilibrium prices maximize revenue over nonnegative prices.
--
--   The named thresholds are $\bar p^B=v-h(2-\beta)$, $\bar p=v-h-h(1-\beta)/\sqrt{1+2\lambda}$, and the paper's $h_0,h_1$. These definitions carry the consumer and firm optimization problems used by all subsequent results.
--
--   **Formalization Note** Aggregate demand equals individual demand because the consumer mass is one; $c=0$ and the quadratic coefficient is $1/2$.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), pp. 7–14 (PDF 8–15), §3 and §4.1–4.2

import Mathlib
import Definitions.Def_ViceGoals_Personal_Monopoly

namespace ViceGoals.Personal

structure Params where
  v : ℝ
  beta : ℝ
  h : ℝ
  lam : ℝ

def Params.Standing (m : Params) : Prop :=
  0 < m.v ∧ 0 < m.beta ∧ m.beta < 1 ∧ 0 ≤ m.h ∧ 0 < m.lam

/-- The disutility applies precisely when consumption exceeds the goal. -/
noncomputable def penalty (m : Params) (G q : ℝ) : ℝ :=
  if G < q then m.lam * (q - G) ^ 2 else 0

/-- Period-4 utility without a goal. -/
noncomputable def U4B (m : Params) (p q : ℝ) : ℝ :=
  m.v * q - q ^ 2 / 2 - m.beta * m.h * q - p * q

/-- Period-2 utility without a goal. -/
noncomputable def U2B (m : Params) (p q : ℝ) : ℝ :=
  m.v * q - q ^ 2 / 2 - m.h * q - p * q

/-- A nonnegative quantity maximizing period-4 benchmark utility. -/
def IsOptQtyB (m : Params) (p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → U4B m p q' ≤ U4B m p q

/-- Unit-mass demand, with purchase on indifference at the planning stage. -/
def IsDemandB (m : Params) (p Q : ℝ) : Prop :=
  ∃ q, IsOptQtyB m p q ∧ Q = if 0 ≤ U2B m p q then q else 0

/-- Period-4 utility with a personal goal. -/
noncomputable def U4 (m : Params) (G p q : ℝ) : ℝ :=
  U4B m p q - penalty m G q

/-- Period-3 utility with a personal goal. -/
noncomputable def U3 (m : Params) (G p q : ℝ) : ℝ :=
  U2B m p q - penalty m G q

/-- A nonnegative quantity maximizing period-4 utility at a fixed goal. -/
def IsOptQty (m : Params) (G p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → U4 m G p q' ≤ U4 m G p q

/-- A nonnegative goal maximizing the anticipated period-3 utility. -/
def IsOptGoal (m : Params) (p G : ℝ) : Prop :=
  0 ≤ G ∧ ∃ q, IsOptQty m G p q ∧
    ∀ G' q' : ℝ, 0 ≤ G' → IsOptQty m G' p q' → U3 m G' p q' ≤ U3 m G p q

/-- Unit-mass goal-conditioned demand, buying on indifference at period 2. -/
def IsDemandGoal (m : Params) (p Q : ℝ) : Prop :=
  ∃ G q, IsOptGoal m p G ∧ IsOptQty m G p q ∧
    Q = if 0 ≤ U3 m G p q then q else 0

def IsEqPriceB (m : Params) (p : ℝ) : Prop :=
  IsMonopolyPrice (IsDemandB m) p

def IsEqPriceGoal (m : Params) (p : ℝ) : Prop :=
  IsMonopolyPrice (IsDemandGoal m) p

/-- Benchmark reservation price, p. 10. -/
def pbarB (m : Params) : ℝ := m.v - m.h * (2 - m.beta)

/-- Personal-goal reservation price, p. 12. -/
noncomputable def pbar (m : Params) : ℝ :=
  m.v - m.h - m.h * (1 - m.beta) / Real.sqrt (1 + 2 * m.lam)

/-- Threshold separating the two positive goal-price regimes, p. 14. -/
noncomputable def h0 (m : Params) : ℝ :=
  m.v * ((1 + 2 * m.lam) * Real.sqrt (1 + 2 * m.lam)) /
    (2 * (1 + Real.sqrt (1 + 2 * m.lam) +
      m.lam * (2 + Real.sqrt (1 + 2 * m.lam))) -
      m.beta * (2 + 4 * m.lam + Real.sqrt (1 + 2 * m.lam)))

/-- The price-comparison threshold in Proposition 1, p. 14. -/
noncomputable def h1 (m : Params) : ℝ :=
  m.v * (1 + 2 * m.lam) /
    (4 - 3 * m.beta + 6 * m.lam - 4 * m.beta * m.lam)

end ViceGoals.Personal


