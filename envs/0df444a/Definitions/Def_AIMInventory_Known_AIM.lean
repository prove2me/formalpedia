-- Prove2me | Definitions.Def_AIMInventory_Known_AIM
-- name    : AIMInventory_Known_AIM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:10.219146+00:00
-- url     : https://prove2.me/theorems/2370de75-34fc-4f7e-8a1f-1af23878e075
-- title:
--   §2.1–2.2: the cost Q of (1), the censored estimate (5), and the AIM run (3)–(4), perishable and non-perishable
-- statement:
--   This file sets up the lost-sales inventory model of Huh and Rusmevichientong (§2.1, pp. 5–6) and their Adaptive Inventory Management (AIM) algorithm (§2.2, p. 7).
--
--   **Demand and cost.** Demands $D_1, D_2, \dots$ are nonnegative, independent and identically distributed with law $P$ (finite, strictly positive mean; the published `CappedBaseStock.DemandLaw`). For holding cost $h>0$ and lost-sales penalty $b>0$, the expected one-period cost of the order-up-to level $y \ge 0$ is
--   $$Q(y) = h\,E[y-D]^+ + b\,E[D-y]^+ ,$$
--   which is the published `backorderCost` at $y$. The function
--   $$g(y) = h\,P\{D < y\} - b\,P\{D \ge y\}$$
--   is recorded as `leftDeriv`.
--
--   **AIM.** Fix an upper bound $\bar y > 0$, a scale $\gamma > 0$ and a starting level $\hat y_1 \in [0,\bar y]$. Let $P_{[0,\bar y]}(z) = \max\{\min\{z,\bar y\},0\}$, let $\epsilon_t = \gamma \bar y/(\max\{b,h\}\sqrt t)$, and let $H_t(\hat y_t) = h$ if $D_t < \hat y_t$ and $H_t(\hat y_t) = -b$ if $D_t \ge \hat y_t$. Set $y_1 = \hat y_1$, $x_1 = 0$, and for $t \ge 1$
--   $$\hat y_{t+1} = P_{[0,\bar y]}\big(\hat y_t - \epsilon_t H_t(\hat y_t)\big), \qquad y_{t+1} = \max\{\hat y_{t+1}, x_{t+1}\},$$
--   where the on-hand inventory is $x_{t+1} = 0$ when excess inventory is perishable and $x_{t+1} = [y_t - D_t]^+$ when it is carried over. The target $\hat y_t$, the implemented level $y_t$ and the on-hand inventory $x_t$ are functions of the demand path; each depends only on $D_1,\dots,D_{t-1}$. Finally, the expected running-average cost of the run is
--   $$E\Big[\frac1T\sum_{t=1}^T Q(y_t)\Big],$$
--   the expectation being over the i.i.d. demand path.
--
--   The estimate $H_t$ uses only censored information: whether the period ended with positive inventory (perishable case), or with at most $y_t-\hat y_t$ units (non-perishable case).
--
--   **Formalization Note** The demand path is zero-based: the paper's $D_t$ is `d (t - 1)`. Indices $t \ge 1$ follow the paper; index $0$ of each sequence is unused and set equal to index $1$ (or to $0$ for $x$). Levels are real numbers and $Q(y)$ is `backorderCost` evaluated at $\max\{y,0\}$; only $y \ge 0$ is ever used. The two cases are the constructors of `Regime`.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, pp. 5–7, §2.1 (items (i)–(iv), Eq. (1)), §2.2 (Eqs. (3)–(5))

import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
open MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace AIMInventory.Known

/-- The expected one-period cost `Q(y) = h·E[y − D]⁺ + b·E[D − y]⁺` of (1), p. 6, at a real
level `y`; it is the published `backorderCost` evaluated at `max y 0` (only `y ≥ 0` is used). -/
def Q (P : CappedBaseStock.DemandLaw) (h b : ℝ) (y : ℝ) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law h b (Real.toNNReal y)

/-- `h · P{D < y} − b · P{D ≥ y}`, the left derivative of `Q` stated in §2.4, p. 10. -/
def leftDeriv (P : CappedBaseStock.DemandLaw) (h b : ℝ) (y : ℝ) : ℝ :=
  h * (P.law {d : ℝ≥0 | (d : ℝ) < y}).toReal - b * (P.law {d : ℝ≥0 | y ≤ (d : ℝ)}).toReal

/-- The projection `P_{[0,ȳ]}(z) = max{min{z, ȳ}, 0}` of p. 7. -/
def projInterval (ybar z : ℝ) : ℝ := max (min z ybar) 0

/-- The step size `ϵ_t = γȳ / (max{b,h} √t)` of (4), p. 7. -/
def stepSize (γ ybar b h : ℝ) (t : ℕ) : ℝ := γ * ybar / (max b h * Real.sqrt t)

/-- The censored gradient estimate (5), p. 7: `H = h` if `D < ŷ`, and `H = −b` if `D ≥ ŷ`. -/
def gradEst (h b : ℝ) (D yhat : ℝ) : ℝ := if D < yhat then h else -b

/-- Whether excess inventory is scrapped (perishable) or carried over (non-perishable). -/
inductive Regime
  | perishable
  | nonPerishable

/-- Next period's on-hand inventory, item (iv) of p. 6: `x_{t+1} = 0` (perishable) or
`x_{t+1} = [y_t − D_t]⁺` (non-perishable). -/
def nextOnHand : Regime → ℝ → ℝ → ℝ
  | .perishable, _, _ => 0
  | .nonPerishable, y, D => max (y - D) 0

/-- The AIM run (3)–(5), p. 7, as a function of the demand path `d` (zero-based: the paper's
`D_t` is `d (t - 1)`). The value at `t ≥ 1` is the pair `(ŷ_t, y_t)`; `y_1 = ŷ_1 = yhat1`, and for
`t ≥ 1`, `ŷ_{t+1} = P_{[0,ȳ]}(ŷ_t − ϵ_t H_t(ŷ_t))`, `y_{t+1} = max{ŷ_{t+1}, x_{t+1}}`. Index `0`
is unused and is set equal to index `1`. -/
def aimState (r : Regime) (ybar γ b h yhat1 : ℝ) (d : CappedBaseStock.DemandPath) :
    ℕ → ℝ × ℝ
  | 0 => (yhat1, yhat1)
  | 1 => (yhat1, yhat1)
  | (t + 2) =>
      let s := aimState r ybar γ b h yhat1 d (t + 1)
      let D : ℝ := (d t : ℝ)
      let yhatNext := projInterval ybar (s.1 - stepSize γ ybar b h (t + 1) * gradEst h b D s.1)
      (yhatNext, max yhatNext (nextOnHand r s.2 D))

/-- The target level `ŷ_t` of the AIM algorithm. -/
def aimTarget (r : Regime) (ybar γ b h yhat1 : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  (aimState r ybar γ b h yhat1 d t).1

/-- The implemented order-up-to level `y_t` of the AIM algorithm. -/
def aimLevel (r : Regime) (ybar γ b h yhat1 : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  (aimState r ybar γ b h yhat1 d t).2

/-- The on-hand inventory `x_t` at the start of period `t ≥ 1`: `x_1 = 0`, and
`x_{t+1} = 0` or `[y_t − D_t]⁺`. -/
def onHand (r : Regime) (ybar γ b h yhat1 : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | (t + 2) => nextOnHand r (aimLevel r ybar γ b h yhat1 d (t + 1)) (d t : ℝ)

/-- The expected running-average cost `E[(1/T) Σ_{t=1}^T Q(y_t)]` of the AIM run under the
i.i.d. demand path law. -/
def avgExpectedCost (P : CappedBaseStock.DemandLaw) (r : Regime) (ybar γ b h yhat1 : ℝ)
    (T : ℕ) : ℝ :=
  ∫ d, (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, Q P h b (aimLevel r ybar γ b h yhat1 d t)
    ∂(CappedBaseStock.demandPathLaw P)

end AIMInventory.Known


