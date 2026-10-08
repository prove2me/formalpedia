-- Prove2me | Definitions.Def_LostSalesBalancing_DualBalancing_Model
-- name    : LostSalesBalancing_DualBalancing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:57.389845+00:00
-- url     : https://prove2.me/theorems/bbb6669d-8b21-4709-a3d6-0317400a141b
-- title:
--   §2–§3.2, pp. 4–9 — the lost-sales model: recursion (3), marginal costs (4)–(5), C(P), truncated position (6), T_H (7), independent demands, dual balancing
-- statement:
--   This file sets up the finite-horizon lost-sales inventory model of Levi, Janakiraman and Nagarajan (§2–§3.2).
--
--   **Data.** Periods are $t=1,\ldots,T$. The lead time $L\ge1$ is a known integer: an order $Q_s\ge0$ placed in period $s$ arrives at the beginning of period $s+L$. Before the horizon there are $x_0\ge0$ units on hand and nonnegative pipeline orders $q_{1-L},\ldots,q_0$; we write $Q_j=q_j$ for $j\le0$. The cost rates are a holding cost $h_t\ge0$, a lost-sales penalty $p_t\ge0$ and an ordering cost $c_t\ge0$ per unit, where $c_t$ and $p_t$ are non-increasing in $t$ and $h_t$ is arbitrary.
--
--   **Dynamics.** Along a demand path $d_1,\ldots,d_T$, the on-hand inventory $I_t$ at the beginning of period $t$ (after the arrival, before demand) satisfies $I_1=x_0+Q_{1-L}$ and, as in (3),
--   $$
--   I_{t+1}=(I_t-d_t)^+ + Q_{t+1-L}.
--   $$
--   Unmet demand $(d_t-I_t)^+$ is lost. The truncated inventory position (6) of period $s$ with respect to period $t$ is $Y_{st}=I_s+\sum_{j=s+1-L}^{t}Q_j$.
--
--   **Marginal costs.** With $D_{[a,b]}=\sum_{j=a}^{b}d_j$, the marginal holding cost (4) of the units ordered in period $s$, with the ordering cost incorporated, and the lost-sales penalty (5) incurred in period $s+L$ are
--   $$
--   H_s=c_sQ_s+\sum_{t=s+L}^{T}h_t\Bigl(Q_s-\bigl(D_{[s+L,t]}-(I_{s+L-1}-d_{s+L-1})^+\bigr)^+\Bigr)^+,\qquad \Pi_s=p_{s+L}(d_{s+L}-I_{s+L})^+,
--   $$
--   and the cost of a policy is $C(P)=\sum_{s=1}^{T-L}(H^P_s+\Pi^P_s)$. Its expectation $E[C(P)]$ is taken in $[0,\infty]$.
--
--   **Comparison sets.** For two order sequences $B$ and $P$ on the same demand path, $t\in\mathcal T_H$ (7) means $Y^B_{st}<Y^P_{st}$ for every $s\in[t,t+L]$; for $t\in[1,T-L]$ its negation is $t\in\mathcal T_\Pi$ (8).
--
--   **Stochastic layer.** On a probability space with a filtration $(\mathcal F_t)$, where $\mathcal F_t$ is the information at the beginning of period $t$, the demand $D_t\ge0$ is $\mathcal F_{t+1}$-measurable and a feasible policy orders $Q_t\ge0$ that is $\mathcal F_t$-measurable. *Independent demands* means: every $D_t$ is integrable and, for every $t$, $\mathcal F_t$ is independent of $(D_t,\ldots,D_T)$. A *dual-balancing policy* $B$ is feasible, orders nothing after period $T-L$, has integrable $H^B_t$ and $\Pi^B_t$, and balances
--   $$
--   E[H^B_t\mid\mathcal F_t]=E[\Pi^B_t\mid\mathcal F_t]\quad\text{almost surely},\qquad t=1,\ldots,T-L.
--   $$
--
--   These objects are shared by every statement of the mission: the sample-path comparisons (11), Lemmas 3.2–3.4, and the stochastic statements Lemmas 3.1, 3.5, 3.6 and Theorem 3.1.
--
--   **Formalization Note** Periods are integers. The structure `Instance` and the functions `cumDemand`, `order`, `DemandProcess` and `IsFeasiblePolicy` are reused from the published `LeviBalancing.DualBalancing` definitions; their backlogging-specific objects are not used. The paper first assumes stationary $h,p>0$ and $c=0$, and Theorem 3.1 states the generality used here (time-dependent holding costs, non-increasing ordering and lost-sales costs). Rates are only required to be $\ge0$. The paper says "independent demands" while allowing the information set to contain more than past demands; we state independence as $\mathcal F_t$ independent of $(D_t,\ldots,D_T)$ for every $t$, which for $\mathcal F_t=\sigma(D_1,\ldots,D_{t-1})$ is exactly mutual independence of $D_1,\ldots,D_T$. Integrability of $H^B_t$, $\Pi^B_t$ is required so that conditional expectations are genuine (Mathlib assigns $0$ to the conditional expectation of a non-integrable function). The cost $C(P)$ is the paper's marginal accounting (p. 6): it omits the holding cost of units ordered before period 1 and the lost sales in periods $1,\ldots,L$, which are the same for every policy.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript pp. 4–9, §2–§3.2, (3)–(8)

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
import Definitions.Def_LeviBalancing_DualBalancing_Policy

noncomputable section

namespace LostSalesBalancing.DualBalancing

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open LeviBalancing.DualBalancing

/-- Data for §2 and Theorem 3.1: positive lead time, nonnegative initial stock,
nonnegative holding costs, and non-increasing ordering and lost-sales rates. -/
structure LSInstance extends Instance where
  c : ℤ → ℝ
  L_pos : 1 ≤ L
  ni0_nonneg : 0 ≤ ni0
  c_nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → 0 ≤ c t
  c_anti : ∀ s t : ℤ, 1 ≤ s → s ≤ t → t ≤ (T : ℤ) → c t ≤ c s
  p_anti : ∀ s t : ℤ, 1 ≤ s → s ≤ t → t ≤ (T : ℤ) → p t ≤ p s

/-- The pathwise inventory recursion (3). Index zero stores the on-hand stock at the
beginning of period one, after arrival of the initial pipeline order. -/
def onHandNat (I : LSInstance) (d Q : ℤ → ℝ) : ℕ → ℝ
  | 0 => I.ni0 + order I.toInstance Q (1 - (I.L : ℤ))
  | n + 1 => max (onHandNat I d Q n - d ((n : ℤ) + 1)) 0 +
      order I.toInstance Q ((n : ℤ) + 2 - I.L)

/-- On-hand stock at the start of positive period `t`. -/
def onHand (I : LSInstance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  onHandNat I d Q (t - 1).toNat

/-- The unmet units of demand in period `t`. -/
def lostUnits (I : LSInstance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  max (d t - onHand I d Q t) 0

/-- The marginal holding cost (4), including the linear ordering cost `c_s Q_s`. -/
def holdingLS (I : LSInstance) (d Q : ℤ → ℝ) (s : ℤ) : ℝ :=
  I.c s * order I.toInstance Q s +
  ∑ t ∈ Icc (s + I.L) (I.T : ℤ), I.h t *
    max (order I.toInstance Q s -
      max (cumDemand d (s + I.L) t -
        max (onHand I d Q (s + I.L - 1) - d (s + I.L - 1)) 0) 0) 0

/-- The lost-sales penalty (5) associated with the order period `s`, incurred at `s + L`. -/
def lostLS (I : LSInstance) (d Q : ℤ → ℝ) (s : ℤ) : ℝ :=
  I.p (s + I.L) * lostUnits I d Q (s + I.L)

/-- Policy cost `C(P)` of §3.1, summing marginal holding and lost-sales costs. -/
def costLS (I : LSInstance) (d Q : ℤ → ℝ) : ℝ :=
  ∑ s ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), (holdingLS I d Q s + lostLS I d Q s)

/-- Truncated inventory position (6), with orders from the initial pipeline where needed. -/
def truncPos (I : LSInstance) (d Q : ℤ → ℝ) (s t : ℤ) : ℝ :=
  onHand I d Q s + ∑ j ∈ Icc (s + 1 - I.L) t, order I.toInstance Q j

/-- The event `t ∈ T_H` of (7), pathwise. For `t ∈ [1,T-L]` its negation is (8). -/
def InTH (I : LSInstance) (d QB QP : ℤ → ℝ) (t : ℤ) : Prop :=
  ∀ s ∈ Icc t (t + I.L), truncPos I d QB s t < truncPos I d QP s t

/-- Random marginal holding cost. -/
def randHoldingLS {Ω : Type*} (I : LSInstance) (D Q : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => holdingLS I (fun j => D j ω) (fun j => Q j ω) t

/-- Random lost-sales penalty. -/
def randLostLS {Ω : Type*} (I : LSInstance) (D Q : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => lostLS I (fun j => D j ω) (fun j => Q j ω) t

/-- The sample-path event `t ∈ T_H`. -/
def setTH {Ω : Type*} (I : LSInstance) (D QB QP : ℤ → Ω → ℝ) (t : ℤ) : Set Ω :=
  {ω | InTH I (fun j => D j ω) (fun j => QB j ω) (fun j => QP j ω) t}

/-- Expected marginal cost in `[0,∞]`; infinite expectation is represented by infinity. -/
def expectedCostLS {Ω : Type*} [MeasurableSpace Ω] (I : LSInstance) (μ : Measure Ω)
    (D Q : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (costLS I (fun j => D j ω) (fun j => Q j ω)) ∂μ

/-- Independent demands with finite means. Each beginning-of-period information set is
independent of the joint future demand vector, allowing extra exogenous information. -/
structure IndependentDemands {Ω : Type*} [m : MeasurableSpace Ω] (I : LSInstance)
    (ℱ : Filtration ℤ m) (μ : Measure Ω) (DP : DemandProcess ℱ μ I.T) : Prop where
  integrable : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → Integrable (DP.D t) μ
  indep_future : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) →
    Indep (ℱ t) (⨆ j ∈ {j : ℤ | t ≤ j ∧ j ≤ (I.T : ℤ)},
      MeasurableSpace.comap (DP.D j) inferInstance) μ

/-- The dual-balancing rule of §3.1, represented as a property of a feasible order process.
Integrability prevents the conditional-expectation junk value for nonintegrable costs. -/
structure IsDualBalancingLS {Ω : Type*} [m : MeasurableSpace Ω] (I : LSInstance)
    (ℱ : Filtration ℤ m) (μ : Measure Ω) (D B : ℤ → Ω → ℝ) : Prop where
  feasible : IsFeasiblePolicy I.toInstance ℱ B
  zero_after : ∀ t : ℤ, (I.T : ℤ) - I.L < t → t ≤ (I.T : ℤ) → ∀ ω, B t ω = 0
  integrable_holding : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    Integrable (randHoldingLS I D B t) μ
  integrable_lost : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    Integrable (randLostLS I D B t) μ
  balance : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    μ[randHoldingLS I D B t | ℱ t] =ᵐ[μ] μ[randLostLS I D B t | ℱ t]

end LostSalesBalancing.DualBalancing

end


