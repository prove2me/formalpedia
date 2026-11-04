-- Prove2me | Definitions.Def_AIMInventory_UnknownBound_AIM
-- name    : AIMInventory_UnknownBound_AIM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:05.734219+00:00
-- url     : https://prove2.me/theorems/b6e8c075-62d7-4ed5-9090-c0a38983a52c
-- title:
--   §3.1: the expanding-projection AIM policy and newsvendor benchmark
-- statement:
--   Consider an i.i.d. path of nonnegative demands with law $P$. For holding cost $h>0$ and shortage cost $b>0$, let $Q(y)$ be the expected single-period newsvendor cost at level $y\ge0$, and let $y^{NV}$ be the least level at which the demand distribution reaches the critical fraction $b/(b+h)$.
--
--   Given $\delta>0$ and an initial target $\hat y^\delta_1$, the modified AIM target is updated after period $t\ge1$ by
--
--   $$\hat y^\delta_{t+1}=P_{[0,t^{\delta/2}]}\!\left(\hat y^\delta_t-\frac{H_t(\hat y^\delta_t)}{\max\{b,h\}\sqrt t}\right),\qquad H_t(y)=\begin{cases}h,&D_t<y,\\-b,&D_t\ge y.\end{cases}$$
--
--   The projection clips its argument to $[0,t^{\delta/2}]$. In the perishable case the implemented level is exactly the target. The definitions also identify the rounds before and after $t=(y^{NV})^{2/\delta}$, as used in the paper's proof.
--
--   **Formalization Note** Demand path coordinate zero is paper period one, so target period $t$ reads only coordinates below $t-1$. The definition accepts any initial real target; the theorem statements require $\hat y^\delta_1\in[0,1]$. The shared demand-law structure requires a positive finite mean, although only finiteness is needed here. $Q$ converts a real level to a nonnegative level; all levels used by the theorems are nonnegative.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, pp. 5–7, 11–12, Eq. (1), Eq. (3)–(5), §3.1; https://doi.org/10.1287/moor.1080.0355

import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section

open scoped NNReal

namespace AIMInventory.UnknownBound

/-- The paper's one-period newsvendor cost, used only at nonnegative levels. -/
def cost (P : CappedBaseStock.DemandLaw) (h b y : ℝ) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law h b (Real.toNNReal y)

/-- The newsvendor quantity of the demand law. -/
def newsvendor (P : CappedBaseStock.DemandLaw) (h b : ℝ) : ℝ :=
  (LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law h b : ℝ)

/-- The radius of the projection interval at step `t`. -/
def radius (δ : ℝ) (t : ℕ) : ℝ := Real.rpow (t : ℝ) (δ / 2)

/-- Equation (4), modified in Section 3.1. -/
def stepSize (b h : ℝ) (t : ℕ) : ℝ :=
  1 / (max b h * Real.sqrt (t : ℝ))

/-- Equation (5). The event determining this signal is observable from censored
sales in the perishable inventory system. -/
def signal (h b y : ℝ) (d : ℝ≥0) : ℝ :=
  if (d : ℝ) < y then h else -b

/-- Projection onto the closed interval from zero to `a`. -/
def project (a z : ℝ) : ℝ := max (min z a) 0

/-- A zero-based implementation: index zero is the paper's first period.
After observing demand `d t`, the update projects onto `[0,(t+1)^(δ/2)]`. -/
def modAimRun (δ b h y₁ : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℝ
  | 0 => y₁
  | t + 1 =>
      let y := modAimRun δ b h y₁ d t
      project (radius δ (t + 1))
        (y - stepSize b h (t + 1) * signal h b y (d t))

/-- The paper's one-based target and implemented level in the perishable case.
The target in period `t` uses only demands from periods strictly before `t`. -/
def modAimTarget (δ b h y₁ : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  modAimRun δ b h y₁ d (t - 1)

/-- Rounds below the threshold in the proof of Theorem 7, Equation (10). -/
def earlyRounds (δ y : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun t => (t : ℝ) < Real.rpow y (2 / δ))

/-- Rounds at or above the threshold in the proof of Theorem 7, Equation (11). -/
def lateRounds (δ y : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun t => Real.rpow y (2 / δ) ≤ (t : ℝ))

end AIMInventory.UnknownBound


