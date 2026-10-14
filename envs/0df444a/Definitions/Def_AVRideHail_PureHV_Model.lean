-- Prove2me | Definitions.Def_AVRideHail_PureHV_Model
-- name    : AVRideHail_PureHV_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:59.234621+00:00
-- url     : https://prove2.me/theorems/b1f737b3-c81e-4470-a6ca-8c3c264ea2a8
-- title:
--   §3.1, §4, App. A.1, pp. 7–14, 38 — ride-hailing market: n̲(d), ū(d), p_i, r_i, w, equilibrium (13), Definition 1, (33)
-- statement:
--   This file sets up the pure human-driver (HV) ride-hailing market of Lian and van Ryzin.
--
--   A market is described by six real parameters: the coefficient $a$ and the elasticity $r$ of the pickup-time (ETA) function $t_1(s) = a s^{-r}$, where $s$ is the number of open (idle) cars; the mean trip time $t_2$; the riders' maximal value $V$ (rider values are uniform on $[0,V]$); and the intercept $w_0$ and slope $\alpha$ of the HV supply curve $w(n) = w_0 + \alpha n$, the hourly reservation earnings needed to attract a fleet of $n$ drivers.
--
--   From these the file defines:
--
--   1. the constant $\tilde a = r^{\frac{1}{r+1}} a^{\frac{1}{r+1}} + r^{-\frac{r}{r+1}} a^{\frac{1}{r+1}}$ (Lemma 1);
--   2. the minimal supply level needed to serve a demand rate $d$, $\underline{n}(d) = \tilde a\, d^{\frac{1}{r+1}} + t_2 d$ (equation (12));
--   3. the maximal utilization $\bar u(d) = d t_2 / \underline{n}(d)$ (equation (22));
--   4. for a demand scenario with potential demand mass $m$, the inverse demand $p(d) = V(1 - d/m)$ (equation (3)) and the market revenue $r(d) = d\, p(d)\, t_2$;
--   5. the minimal total driver cost $w(\underline{n}(d))\,\underline{n}(d)$;
--   6. an **equilibrium**: a demand rate $d \in [0, m]$ with
--   $$ r(d) = w(\underline{n}(d))\,\underline{n}(d) \qquad (13);$$
--   7. **stability** (Definition 1): there is no $\epsilon > 0$ with $r(d-\epsilon) < w(\underline{n}(d-\epsilon))\underline{n}(d-\epsilon)$ and $r(d+\epsilon) > w(\underline{n}(d+\epsilon))\underline{n}(d+\epsilon)$;
--   8. the **maximal stable equilibrium**: the greatest demand rate that is both an equilibrium and stable;
--   9. the **loose labor market** condition of a scenario, in the form (33) of Appendix B.1.1: $r(m/2) > w(\underline{n}(m/2))\,\underline{n}(m/2)$.
--
--   These objects are the whole vocabulary of the pure-HV analysis (Section 4 and Appendix B.1 of the paper) and of its comparison with markets containing autonomous vehicles.
--
--   **Formalization Note** All quantities are real numbers; no positivity is built into the structure, so every theorem states its parameter hypotheses explicitly. Powers are `Real.rpow`, with $0^0 = 1$ and $0^y = 0$ for $y \neq 0$: at $r = 0$ this gives $\tilde a = a$ and $\underline{n}(d) = (a + t_2)d$, as in the paper's equation (45). The value $\bar u(0) = 0/0$ is $0$, which is the paper's $\bar u(0) = 0$ (Lemma 2). In Definition 1, $\epsilon$ ranges over $0 < \epsilon \le d$ with $d + \epsilon \le m$, so that $d \pm \epsilon$ stays in the domain $[0, m]$ of the inverse demand (3); in particular $d = 0$ is vacuously stable, and it is maximality that excludes it when a positive stable equilibrium exists. The loose-market condition is the paper's restatement (33) of Assumption 2, which is strict; Assumption 2 itself, (18), is the non-strict version.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), pp. 7–14 and 38, (1)–(4), (12)–(13), (22), Definition 1, maximal stable equilibrium (p. 14), (33) (p. 42)

import Mathlib

namespace AVRideHail.PureHV

/-- The market's physical and economic parameters (§3.1, pp. 7–9): the ETA function
t₁(s) = a s^{−r} (4), the trip time t₂, the riders' maximal value V (values uniform on [0, V]),
and the HV supply curve w(n) = w₀ + α n (1). -/
structure MarketParams where
  a : ℝ
  r : ℝ
  t2 : ℝ
  V : ℝ
  w0 : ℝ
  alpha : ℝ

/-- ã of Lemma 1, p. 38. -/
noncomputable def aTilde (P : MarketParams) : ℝ :=
  P.r ^ (1 / (P.r + 1)) * P.a ^ (1 / (P.r + 1)) + P.r ^ (-P.r / (P.r + 1)) * P.a ^ (1 / (P.r + 1))

/-- The minimal supply level n̲(d) = ã d^{1/(r+1)} + t₂ d, (12) / Lemma 1. -/
noncomputable def nMin (P : MarketParams) (d : ℝ) : ℝ :=
  aTilde P * d ^ (1 / (P.r + 1)) + P.t2 * d

/-- The maximal utilization ū(d) = d t₂ / n̲(d), (22). -/
noncomputable def uBar (P : MarketParams) (d : ℝ) : ℝ := d * P.t2 / nMin P d

/-- The inverse demand p_i(d) = V (1 − d/m_i), (3), in a scenario of potential demand mass m. -/
noncomputable def priceFn (P : MarketParams) (m d : ℝ) : ℝ := P.V * (1 - d / m)

/-- Total market revenue r_i(d) = d p_i(d) t₂ (p. 12). -/
noncomputable def revenue (P : MarketParams) (m d : ℝ) : ℝ := d * priceFn P m d * P.t2

/-- The HV reservation earnings w(n) = w₀ + α n, (1). -/
noncomputable def wage (P : MarketParams) (n : ℝ) : ℝ := P.w0 + P.alpha * n

/-- The minimum total HV cost w(n̲(d)) n̲(d) of serving demand d, right side of (13). -/
noncomputable def hvCost (P : MarketParams) (d : ℝ) : ℝ := wage P (nMin P d) * nMin P d

/-- Equilibrium condition (13) at a demand rate d ∈ [0, m] (the domain of (3)). -/
def IsEquilibrium (P : MarketParams) (m d : ℝ) : Prop :=
  0 ≤ d ∧ d ≤ m ∧ revenue P m d = hvCost P d

/-- Definition 1, p. 13, with ε restricted so that d ± ε stays in [0, m] (see *Pins*). -/
def IsStable (P : MarketParams) (m d : ℝ) : Prop :=
  ¬ ∃ ε : ℝ, 0 < ε ∧ ε ≤ d ∧ d + ε ≤ m ∧
      revenue P m (d - ε) < hvCost P (d - ε) ∧ hvCost P (d + ε) < revenue P m (d + ε)

/-- The maximal stable equilibrium (p. 14): the greatest stable equilibrium demand rate. -/
def IsMaxStableEq (P : MarketParams) (m d : ℝ) : Prop :=
  IsGreatest {x | IsEquilibrium P m x ∧ IsStable P m x} d

/-- The loose labor market, Assumption 2 in the form (33) of App. B.1.1, p. 42. -/
def LooseMarket (P : MarketParams) (m : ℝ) : Prop :=
  hvCost P (m / 2) < revenue P m (m / 2)

end AVRideHail.PureHV


