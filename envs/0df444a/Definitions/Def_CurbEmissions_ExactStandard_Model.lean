-- Prove2me | Definitions.Def_CurbEmissions_ExactStandard_Model
-- name    : CurbEmissions_ExactStandard_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:38.434043+00:00
-- url     : https://prove2.me/theorems/9f329500-ad7d-43ac-b891-b4b361c3a474
-- title:
--   §3, §4.1.1, pp. 8–19 — two regulators, a monopolist with strategies D/U/S, R1's utility (2), base equilibrium, emissions, exact-standard Nash bargaining
-- statement:
--   This file sets up the model of Han, Hu and Dawande: a monopolist sells an energy-intensive product in two markets $M_1, M_2$, each governed by a regulator who sets a minimum efficiency standard.
--
--   **Parameters.** A parameter record consists of the unit cost $c$ (producing a unit of efficiency level $e$ costs $ce$), the consumers' marginal efficiency bonus $\gamma$, regulator $R_1$'s per-unit perceived environmental impact $h_1$, the market sizes $m_1, m_2$, the maximum consumer valuation $\bar u$, $R_1$'s benchmark efficiency $b$, and the fixed setup cost $r$ per product. The **standing assumptions** of §3 are
--   $$0<c,\quad \gamma<c,\quad 0<r,\quad 0<m_1,\ 0<m_2,\quad 0\le b,\quad h_1\ge \tfrac{c-\gamma}{2},\quad \bar u\ge \max\Big\{\tfrac{4r(m_1+m_2)}{m_1m_2},\ b(c-\gamma)\Big\}.$$
--
--   **Demand and the firm.** Valuations are uniform on $[0,\bar u]$ in both markets; a consumer with valuation $u$ facing price $p$ and efficiency $e$ buys when $u-p+\gamma e>0$, so the buying share is $1-(p-\gamma e)/\bar u$, clipped to $[0,1]$. Selling efficiency $e$ at price $p$ in a market of size $m$ yields operating profit $(p-ce)\,m\,\big(1-\tfrac{p-\gamma e}{\bar u}\big)$. The price $p^*=[(c+\gamma)e+\bar u]/2$ is fixed as a definition. At $p^*$, with $x(e)=\max\{0,\bar u-(c-\gamma)e\}$, the sales in a market of size $m$ are $m\,x(e)/(2\bar u)$ and the consumers' total net utility is $m\,x(e)^2/(8\bar u)$.
--
--   Regulator $R_2$ sets $s_2=0$. Given $R_1$'s standard $s_1$, the firm chooses among three strategies: $D$ (product at $s_1$ in $M_1$ and at $0$ in $M_2$, setup cost $2r$), $U$ (one product at $s_1$ in both markets, cost $r$), and $S$ (one product at $0$ in $M_2$ only, cost $r$). Its profit under each strategy is eq. (1) evaluated at $p^*$. A strategy is a **best response** at $s_1$ if no other strategy earns strictly more; ties are not broken.
--
--   **Regulators and emissions.** $R_1$'s utility (eq. (2)) is the consumer utility in $M_1$ minus $h_1\sum_i (b-e_i)\cdot \text{sales}_i$ over the markets served, and $R_2$'s utility is the consumer utility in $M_2$. Total emissions are $\sum_i (b-e_i)\cdot\text{sales}_i$.
--
--   **Base model outcome.** A pair $(s_1,\sigma)$ is a base-model outcome if $s_1\ge0$, $\sigma$ is a best response at $s_1$, and $R_1$'s utility at $(s_1,\sigma)$ is at least its utility at every standard $s_1'\ge 0$ paired with every best response there.
--
--   **Auxiliary objects of the proofs.** The unclipped polynomials $\pi_{1U}(s)=\frac{m_1}{8\bar u}(\bar u-(c-\gamma)s)^2-h_1(b-s)\frac{m_1+m_2}{2\bar u}(\bar u-(c-\gamma)s)$ and $\pi_{1D}(s)=\frac{m_1}{8\bar u}(\bar u-(c-\gamma)s)^2-h_1(b-s)\frac{m_1}{2\bar u}(\bar u-(c-\gamma)s)-\frac12 h_1bm_2$, the thresholds $\tau_U=\frac{\bar u-\sqrt{\bar u^2-4\bar ur/m_2}}{c-\gamma}$ and $\tau_S=\frac{\bar u-2\sqrt{\bar ur/m_1}}{c-\gamma}$, the standard $s_{1D}^*=\frac{2h_1\bar u-(c-\gamma)(\bar u-2h_1b)}{(c-\gamma)[4h_1-(c-\gamma)]}$, the root set $\{x:\pi_{1D}(s^*_{1D})=\pi_{1U}(\tfrac{\bar u-x}{c-\gamma})\}$ whose largest element is $\bar x$, **condition (1)** of Lemma A.1,
--   $$0<r\le\min\Big\{\frac{m_2\bar u}{4}-\frac{m_2[\bar u-b(c-\gamma)]^2}{\bar u(4-\frac{c-\gamma}{h_1})^2},\ \frac{m_1[\bar u-b(c-\gamma)]^2}{\bar u(4-\frac{c-\gamma}{h_1})^2},\ \frac{m_2}{4\bar u}(\bar u^2-\bar x^2)\Big\},$$
--   the arbitrator's objective $\pi_a$ of eq. (3), and $s_a^*=\frac{2h_1[\bar u+b(c-\gamma)]-(c-\gamma)\bar u}{(c-\gamma)[4h_1-(c-\gamma)]}$.
--
--   **Exact-standard negotiation (§4.1.1).** For a global standard $s_e$ and a transfer $t_h$ from $R_1$ to $R_2$, the firm offers one product at $s_e$ in both markets, and $\Pi_1(s_e,t_h)=\pi_1^U(s_e)-t_h$, $\Pi_2(s_e,t_h)=\pi_2^U(s_e)+t_h$, so $\Pi_1+\Pi_2=T_h(s_e)$ (eq. (4)). Given a disagreement point $(D_1,D_2)$, the feasibility set consists of the pairs with $s_e\ge0$, $\Pi_1\ge D_1$, $\Pi_2\ge D_2$ and $\Pi_1-D_1=\Pi_2-D_2$; the **Nash bargaining solutions** are the feasible pairs maximizing the Nash product $\Omega_h=(\Pi_1-D_1)(\Pi_2-D_2)$ over the feasibility set.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Everything is real-valued. The page's $c\ge\gamma$ is strengthened to $c>\gamma$ because every formula divides by $c-\gamma$; $m_1,m_2>0$ and $b\ge0$ are the implicit domains of market sizes and an efficiency level. The buying share is clipped to $[0,1]$ and the margin $\bar u-(c-\gamma)e$ at $0$: on $[0,\bar u/(c-\gamma)]$, which contains every standard the paper uses, all quantities equal the page's formulas, and above it the clip prevents a negative margin from squaring into a positive profit. Consumer utility and sales at $p^*$ are the page's closed forms, not integrals over valuations. The firm offers each product at the minimum efficiency its market allows (p. 11). The feasibility set is indexed by the pairs $(s_e,t_h)$ rather than by the utility pairs they produce. $\pi_{1U}$, $\pi_{1D}$ and $\pi_a$ are the unclipped polynomials of the proofs.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), pp. 8–19, §3, §3.1, §3.2, §4.1.1, eqs. (1)–(5); Online Appendix p. 1 (PDF 33), Lemma A.1(1); Online Appendix pp. 11–12 (PDF 43–44), proof of Lemma A.1

import Mathlib

namespace CurbEmissions.ExactStandard

/-- The primitives of the base model (§3, pp. 8–11): unit variable cost `c` (cost `c·e` per unit of
efficiency `e`), consumers' marginal efficiency bonus `gam` (γ), R1's per-unit perceived environmental
impact `h1`, market sizes `m1`, `m2`, maximum consumer valuation `ubar` (ū), R1's benchmark efficiency
`b`, and the firm's fixed setup cost `r` per product. -/
structure Params where
  c : ℝ
  gam : ℝ
  h1 : ℝ
  m1 : ℝ
  m2 : ℝ
  ubar : ℝ
  b : ℝ
  r : ℝ

/-- The standing assumptions of §3 (pp. 10–11): `r > 0`, `c > 0`, `h1 ≥ (c − γ)/2`,
`ū ≥ max{4r(m1+m2)/(m1 m2), b(c − γ)}`; the page's `c ≥ γ` is strengthened to `γ < c`, and the
implicit domains `m1, m2 > 0`, `b ≥ 0` are made explicit. -/
def Standing (P : Params) : Prop :=
  0 < P.c ∧ P.gam < P.c ∧ 0 < P.r ∧ 0 < P.m1 ∧ 0 < P.m2 ∧ 0 ≤ P.b ∧
  (P.c - P.gam) / 2 ≤ P.h1 ∧
  4 * P.r * (P.m1 + P.m2) / (P.m1 * P.m2) ≤ P.ubar ∧ P.b * (P.c - P.gam) ≤ P.ubar

/-- Share of a market buying a product of efficiency `e` at price `p` when valuations are uniform on
`[0, ū]`: a consumer with valuation `u` buys iff `u − p + γe > 0`; clipped to `[0, 1]`. -/
noncomputable def share (P : Params) (e p : ℝ) : ℝ :=
  min 1 (max 0 (1 - (p - P.gam * e) / P.ubar))

/-- Operating profit from selling a product of efficiency `e` at price `p` in a market of size `m`
(one summand of eq. (1), before setup costs). -/
noncomputable def priceObj (P : Params) (e m p : ℝ) : ℝ :=
  (p - P.c * e) * m * share P e p

/-- The price `p∗ = [(c + γ)e + ū]/2` (§3.1, p. 12). -/
noncomputable def pStar (P : Params) (e : ℝ) : ℝ :=
  ((P.c + P.gam) * e + P.ubar) / 2

/-- The margin `ū − (c − γ)e`, clipped at `0` (no sales once it is negative). -/
noncomputable def margin (P : Params) (e : ℝ) : ℝ :=
  max 0 (P.ubar - (P.c - P.gam) * e)

/-- Sales volume at `p∗` in a market of size `m`: `m (ū − (c − γ)e)/(2ū)` (p. 13), clipped. -/
noncomputable def sales (P : Params) (e m : ℝ) : ℝ :=
  m * margin P e / (2 * P.ubar)

/-- Total consumer net utility at `p∗` in a market of size `m`: `m (ū − (c − γ)e)²/(8ū)` (p. 13),
clipped. -/
noncomputable def consUtil (P : Params) (e m : ℝ) : ℝ :=
  m * margin P e ^ 2 / (8 * P.ubar)

/-- The firm's strategies of §3.1: `D` (differentiated products at `s1` in M1 and `s2` in M2),
`U` (one unified product at `s1` in both markets), `S` (one product at `s2`, in M2 only). -/
inductive Strategy
  | D
  | U
  | S
  deriving DecidableEq

/-- The firm's profit under each strategy, eq. (1) at the price `p∗`, with `s2 = 0`. -/
noncomputable def firmProfit (P : Params) (s1 : ℝ) : Strategy → ℝ
  | .D => priceObj P s1 P.m1 (pStar P s1) + priceObj P 0 P.m2 (pStar P 0) - 2 * P.r
  | .U => priceObj P s1 (P.m1 + P.m2) (pStar P s1) - P.r
  | .S => priceObj P 0 P.m2 (pStar P 0) - P.r

/-- `σ` is a profit-maximizing strategy of the firm given standard `s1` in M1 and `0` in M2
(ties are not broken). -/
def IsFirmBR (P : Params) (s1 : ℝ) (σ : Strategy) : Prop :=
  ∀ σ', firmProfit P s1 σ' ≤ firmProfit P s1 σ

/-- Regulator R1's utility, eq. (2): consumer utility in M1 minus `h1` times the excess emissions
`(b − e)·sales` over the markets served. -/
noncomputable def pi1 (P : Params) (s1 : ℝ) : Strategy → ℝ
  | .D => consUtil P s1 P.m1 - P.h1 * ((P.b - s1) * sales P s1 P.m1 + P.b * sales P 0 P.m2)
  | .U => consUtil P s1 P.m1 - P.h1 * (P.b - s1) * (sales P s1 P.m1 + sales P s1 P.m2)
  | .S => -(P.h1 * P.b * sales P 0 P.m2)

/-- Regulator R2's utility: consumer utility in M2. -/
noncomputable def pi2 (P : Params) (s1 : ℝ) : Strategy → ℝ
  | .D => consUtil P 0 P.m2
  | .U => consUtil P s1 P.m2
  | .S => consUtil P 0 P.m2

/-- Total (excess) emissions over both markets, `Σ_i (b − e_i)·sales_i` (p. 15). -/
noncomputable def emissions (P : Params) (s1 : ℝ) : Strategy → ℝ
  | .D => (P.b - s1) * sales P s1 P.m1 + P.b * sales P 0 P.m2
  | .U => (P.b - s1) * (sales P s1 P.m1 + sales P s1 P.m2)
  | .S => P.b * sales P 0 P.m2

/-- Base-model outcome (§3.2), with `s2 = 0`: `s1 ≥ 0`, `σ` is a firm best response at `s1`, and R1's
utility at `(s1, σ)` is at least its utility at every standard `s1' ≥ 0` paired with every firm best
response there. -/
def IsBaseEq (P : Params) (s1 : ℝ) (σ : Strategy) : Prop :=
  0 ≤ s1 ∧ IsFirmBR P s1 σ ∧
    ∀ s1' σ', 0 ≤ s1' → IsFirmBR P s1' σ' → pi1 P s1' σ' ≤ pi1 P s1 σ

/-- The threshold `τ_U = (ū − √(ū² − 4ūr/m2))/(c − γ)` of Lemma 1 (p. 12). -/
noncomputable def tauU (P : Params) : ℝ :=
  (P.ubar - Real.sqrt (P.ubar ^ 2 - 4 * P.ubar * P.r / P.m2)) / (P.c - P.gam)

/-- The threshold `τ_S = (ū − 2√(ūr/m1))/(c − γ)` of Lemma 1 (p. 12). -/
noncomputable def tauS (P : Params) : ℝ :=
  (P.ubar - 2 * Real.sqrt (P.ubar * P.r / P.m1)) / (P.c - P.gam)

/-- `π1U(s)` of the proof of Lemma A.1: R1's utility under `U` as an (unclipped) polynomial. -/
noncomputable def pi1URaw (P : Params) (s : ℝ) : ℝ :=
  P.m1 / (8 * P.ubar) * (P.ubar - (P.c - P.gam) * s) ^ 2
    - P.h1 * (P.b - s) * (P.m1 + P.m2) / (2 * P.ubar) * (P.ubar - (P.c - P.gam) * s)

/-- `π1D(s)` of the proof of Lemma A.1: R1's utility under `D` as an (unclipped) polynomial. -/
noncomputable def pi1DRaw (P : Params) (s : ℝ) : ℝ :=
  P.m1 / (8 * P.ubar) * (P.ubar - (P.c - P.gam) * s) ^ 2
    - P.h1 * (P.b - s) * P.m1 / (2 * P.ubar) * (P.ubar - (P.c - P.gam) * s)
    - P.h1 * P.b * P.m2 / 2

/-- `s∗1D = (2h1ū − (c − γ)(ū − 2h1b))/((c − γ)[4h1 − (c − γ)])` (Lemma A.1(1)). -/
noncomputable def s1DStar (P : Params) : ℝ :=
  (2 * P.h1 * P.ubar - (P.c - P.gam) * (P.ubar - 2 * P.h1 * P.b)) /
    ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)))

/-- The roots `x` of `π1D(s∗1D) = π1U((ū − x)/(c − γ))`; `x̄` is the largest (proof of Lemma A.1). -/
def xbarEqSet (P : Params) : Set ℝ :=
  {x | pi1URaw P ((P.ubar - x) / (P.c - P.gam)) = pi1DRaw P (s1DStar P)}

/-- Condition (1) of Lemma A.1, given `x̄`:
`0 < r ≤ min{m2ū/4 − m2[ū − b(c−γ)]²/(ū(4 − (c−γ)/h1)²), m1[ū − b(c−γ)]²/(ū(4 − (c−γ)/h1)²),
(m2/(4ū))(ū² − x̄²)}`. -/
def Cond1 (P : Params) (xbar : ℝ) : Prop :=
  0 < P.r ∧
  P.r ≤ min (min
    (P.m2 * P.ubar / 4 - P.m2 * (P.ubar - P.b * (P.c - P.gam)) ^ 2 /
        (P.ubar * (4 - (P.c - P.gam) / P.h1) ^ 2))
    (P.m1 * (P.ubar - P.b * (P.c - P.gam)) ^ 2 / (P.ubar * (4 - (P.c - P.gam) / P.h1) ^ 2)))
    (P.m2 / (4 * P.ubar) * (P.ubar ^ 2 - xbar ^ 2))

/-- The neutral arbitrator's objective `π_a(s_a)`, eq. (3). -/
noncomputable def piA (P : Params) (sa : ℝ) : ℝ :=
  (P.m1 + P.m2) / (8 * P.ubar) * (P.ubar - (P.c - P.gam) * sa) ^ 2
    - P.h1 * (P.b - sa) * (P.m1 + P.m2) / (2 * P.ubar) * (P.ubar - (P.c - P.gam) * sa)

/-- `s∗a = (2h1[ū + b(c − γ)] − (c − γ)ū)/((c − γ)[4h1 − (c − γ)])` (p. 16). -/
noncomputable def saStar (P : Params) : ℝ :=
  (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
    ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)))

/-- R1's utility `Π1(se, th)` under an exact global standard `se` (unified product in both markets)
after transferring `th` to R2 (§4.1.1). -/
noncomputable def Pi1 (P : Params) (se th : ℝ) : ℝ := pi1 P se .U - th

/-- R2's utility `Π2(se, th)` under an exact global standard `se` after receiving `th` (§4.1.1). -/
noncomputable def Pi2 (P : Params) (se th : ℝ) : ℝ := pi2 P se .U + th

/-- The regulators' total utility `T_h(se)` at an exact global standard, eq. (4). -/
noncomputable def Th (P : Params) (se : ℝ) : ℝ := pi1 P se .U + pi2 P se .U

/-- The feasibility set `𝓑(se, th)` of §4.1.1 (p. 18), as the set of pairs `(se, th)` with `se ≥ 0`,
`Π1 ≥ D1`, `Π2 ≥ D2` and the equal split `Π1 − D1 = Π2 − D2` (the sum constraint
`Π1 + Π2 = T_h(se)` holds by construction). -/
def BargFeasible (P : Params) (D1 D2 : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ D1 ≤ Pi1 P q.1 q.2 ∧ D2 ≤ Pi2 P q.1 q.2 ∧
       Pi1 P q.1 q.2 - D1 = Pi2 P q.1 q.2 - D2}

/-- The Nash product `Ω_h(se, th) = (Π1 − D1)(Π2 − D2)` (p. 19). -/
noncomputable def nashProduct (P : Params) (D1 D2 : ℝ) (q : ℝ × ℝ) : ℝ :=
  (Pi1 P q.1 q.2 - D1) * (Pi2 P q.1 q.2 - D2)

/-- The Nash bargaining solutions: feasible pairs maximizing the Nash product over the feasibility
set. -/
def NBS (P : Params) (D1 D2 : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ BargFeasible P D1 D2 ∧
       ∀ q' ∈ BargFeasible P D1 D2, nashProduct P D1 D2 q' ≤ nashProduct P D1 D2 q}

end CurbEmissions.ExactStandard


