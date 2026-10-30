-- Prove2me | Definitions.Def_SmartExpediteAudit_PolicyM_Transient
-- name    : SmartExpediteAudit_PolicyM_Transient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:45.54261+00:00
-- url     : https://prove2.me/theorems/ac9f3ae8-a40b-4823-b654-601cfa8ea0c8
-- title:
--   Policy-M transient law from its event rates
-- statement:
--   Let $K\ge1$ be the number of service nodes, $\lambda>0$ the Poisson demand rate, and $\mu_k>0$ the exponential service rates. Use the published Policy-M routing and rates $q(x,y)$ and $q_{\rm out}(x)$ on the countable occupancy space $\mathbb N^K$. For nonnegative real time $t$, set
--
--   $$c=2\left(\lambda+\sum_{k=1}^K\mu_k\right),\qquad T(x,y)=\frac{q(x,y)}c+\mathbf1_{\{x=y\}}\left(1-\frac{q_{\rm out}(x)}c\right),$$
--   $$a_r(t)=e^{-ct}\frac{(ct)^r}{r!},\qquad P_t(x,n)=\sum_{r=0}^{\infty}a_r(t)T^r(x,n).$$
--
--   Here $T^0$ is the identity and $T^{r+1}(x,n)=\sum_yT^r(x,y)T(y,n)$, using the published countable-chain transition powers. These definitions supply the transient law needed for the limit in (8), p. 15. They never refer to the proposed equilibrium weights. The auxiliary clock allows holding epochs; the physical arrival, enabled-service and routing rates are unchanged.
--
--   **Formalization Note** The definitions are total real-valued expressions. Outside positive-rate valid-policy inputs, division and nonsummable-series defaults are not asserted to represent probabilities. The full goal concludes positivity of $c$, convergence of every defining series, stochasticity, the semigroup law and the correct right generator. No realization, stationarity or convergence predicate is assumed.
-- source:
--   Song et al., SSRN 3702068, September 28, 2020 version, https://ssrn.com/abstract=3702068, pp. 14–17, (5), (7), (8), Policy-M; uniformization encoding of the stated event clocks

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model
import Definitions.Def_mm_countable

open scoped NNReal

noncomputable section

namespace SmartExpediteAudit.PolicyM

open SmartExpedite.PolicyM

/-- A constant dominating all enabled Policy-M event rates, with a factor of two
for a strictly positive holding probability. This is an auxiliary clock rate,
not a change to any physical arrival or service rate. -/
def clockRate (K : ℕ) (lam : ℝ) (mu : ℕ → ℝ) : ℝ :=
  2 * (lam + ∑ k ∈ Finset.Icc 1 K, mu k)

/-- The uniformized kernel of the actual arrival/service rates, on the full
countable occupancy space. No stationarity, balance or convergence is assumed.
For valid policy parameters all physical transitions change the occupancy vector. -/
def uniformStep (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (x y : Fin K → ℕ) : ℝ :=
  rate K u lam mu x y / clockRate K lam mu +
    if x = y then 1 - outRate K lam mu x / clockRate K lam mu else 0

/-- Probability of exactly `r` epochs of the auxiliary Poisson clock by time `t`.
Time is nonnegative real, not an integer discretization. -/
def poissonMass (K : ℕ) (lam : ℝ) (mu : ℕ → ℝ) (t : ℝ≥0) (r : ℕ) : ℝ :=
  Real.exp (-(clockRate K lam mu * (t : ℝ))) *
    (clockRate K lam mu * (t : ℝ)) ^ r / (r.factorial : ℝ)

/-- Canonical continuous-time transition law obtained by independent Poisson
epochs and the published countable-chain transition powers. Its series and row
convergence, semigroup law and generator identification are conclusions of the
goal, never bundled hypotheses. This definition does not refer to `piM`. -/
def transient (K : ℕ) (u : ℕ → ℕ → ℕ∞) (lam : ℝ) (mu : ℕ → ℝ)
    (t : ℝ≥0) (x n : Fin K → ℕ) : ℝ :=
  ∑' r : ℕ, poissonMass K lam mu t r *
    MarkovMixing.stepPow (uniformStep K u lam mu) r x n

end SmartExpediteAudit.PolicyM


