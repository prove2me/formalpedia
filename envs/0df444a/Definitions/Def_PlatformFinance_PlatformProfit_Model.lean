-- Prove2me | Definitions.Def_PlatformFinance_PlatformProfit_Model
-- name    : PlatformFinance_PlatformProfit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:02.774202+00:00
-- url     : https://prove2.me/theorems/7f87b309-a5b5-4c8a-b4ea-24ee3fe4ffb6
-- title:
--   §3–§4, pp. 8–15, 19, 41 — uniform market size, payoffs (1)–(2), the platform's profits, the trade-credit and platform-financing games, their equilibria, and the thresholds δ₁, δ₂, δ_r, r₁, r₅, r₆
-- statement:
--   This module fixes the model of Huang, Lai, Wang and Xiao (§3, pp. 8–9) and the objects compared in §4.
--
--   A capital-constrained seller buys $q \ge 0$ units from a supplier with unit production cost $c>0$ and sells all of them on a platform at the market-clearing price $p=\tilde a-q$, where the market size $\tilde a$ is uniform on $[a-\delta,a+\delta]$. The platform keeps the share $\varphi\in[0,1)$ of the revenue. The supplier's and the platform's capital cost is the risk-free rate $r_f\ge 0$. Write $\mathbb E$ for the expectation over $\tilde a$,
--   $$
--   \mathbb E[f(\tilde a)]=\frac{1}{2\delta}\int_{a-\delta}^{a+\delta} f(x)\,dx .
--   $$
--
--   1. **Payoffs.** A seller who owes $W$ per unit at the end of the season earns $\mathbb E[((1-\varphi)(\tilde a-q)q-Wq)^+]$ ((1), p. 10): $W=w$ under trade credit and $W=w(1+r)$ under platform financing at loan rate $r$ (p. 12). Under trade credit the supplier earns $\mathbb E[\min\{(1-\varphi)(\tilde a-q)q,\,wq\}]-cq(1+r_f)$ ((2), p. 10) and the platform earns $\mathbb E[\varphi(\tilde a-q)q]$ (p. 12). Under platform financing the supplier earns $(w-c)q(1+r_f)$ (p. 13) and the platform, which lends $wq$ and bears the default risk, earns
--   $$
--   \Pi^P_p=\mathbb E\big[\varphi(\tilde a-q)q+\min\{(1-\varphi)(\tilde a-q)q,\;wq(1+r)\}-wq(1+r_f)\big]\quad\text{(pp. 13–14).}
--   $$
--   2. **Games and equilibria.** A profile is a wholesale price $w$ together with the seller's order rule $w\mapsto q(w)$. In a subgame-perfect equilibrium the seller's rule maximizes her expected profit over $q\ge 0$ at every price (on and off the equilibrium path), and orders zero when no order earns a positive profit; the supplier's price maximizes his profit given that rule, and is the least maximizer. The equilibrium-path platform profits are $\Pi^T_p$ and $\Pi^P_p$.
--   3. **Thresholds** (pp. 11, 13, 15, 19, 41):
--   $$
--   \delta_1=\frac{(5\sqrt{10}-14)((1-\varphi)a-c(1+r_f))}{8(1-\varphi)},\quad
--   \delta_2=\frac{(1-\varphi)a-c(1+r_f)}{(2+\sqrt6)(1-\varphi)},\quad
--   \delta_r=\frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)},
--   $$
--   $$
--   r_1=\frac{(1-\varphi)(a-(\sqrt6+2)\delta)}{c}-1,\qquad \bar c=\frac{a(1-\varphi)^2}{1+r_f},\qquad r_5=\min\{r_1,r_6\},
--   $$
--   $$
--   r_6=\frac{\sqrt{8a^2(2-\varphi)(1-\varphi)^3+\varphi^2\big(2a(1-\varphi)+c(1+r_f)\big)^2}-2a(1-\varphi)\varphi-c(4+r_f\varphi-\varphi)}{2c(2-\varphi)} .
--   $$
--   4. **Closed forms** of Lemmas 1–2 and Propositions 1–2: the seller's best response $q(W)=\frac{(1-\varphi)a-W}{2(1-\varphi)}$ if $W\le(1-\varphi)(a-2\delta)$ and $\frac{(1-\varphi)(a+\delta)-W}{3(1-\varphi)}$ otherwise; the trade-credit equilibrium $(w^T,q^T)$ and the platform-financing equilibrium $(w^P,q^P)$.
--
--   These objects are the vocabulary of every statement of the mission: the goal compares the platform's equilibrium profits $\Pi^T_p$ and $\Pi^P_p$.
--
--   **Formalization Note** The expectation is written as the normalized interval integral above rather than through a probability measure. The two tie-breaks (an indifferent seller orders zero; the supplier's equilibrium price is the least optimal one) are the paper's own boundary conventions (proofs of Propositions 1–2, pp. 31–33). In the $\delta>\delta_1$ branch of $w^T,q^T$ the module uses the proof's form $w^T=(1-\varphi)(a-\delta(S-2))$, $q^T=\delta(S-1)/3$ with $S=\sqrt{((\delta+3a)(1-\varphi)-3c(1+r_f))/(\delta(1-\varphi))}$ (p. 31), because the statement on p. 11 drops a factor $\delta$ under the root. The platform's trade-credit payoff is the expectation $\mathbb E[\varphi(\tilde a-q)q]$, not the page's closed form $\varphi(a-q)q$; the two agree.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, pp. 8–15, 19, 31–35, 41: §3, (1), (2), Lemmas 1–2, Propositions 1–2, the platform profits of pp. 12, 14, and the thresholds of Proposition 7's proof

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model

namespace PlatformFinance.PlatformProfit

/-- The platform's expected profit under trade credit when the seller orders `q`:
`E[φ(ã − q)q]` (p. 12). -/
noncomputable def platformPayoffT (a δ φ q : ℝ) : ℝ :=
  PlatformFinance.WinWin.uniformMean a δ (fun x => φ * (x - q) * q)

/-- The platform's expected profit under platform financing at rate `r`, upfront price `w` and
order `q`: `E[φ(ã − q)q + min{(1 − φ)(ã − q)q, wq(1 + r)} − wq(1 + r_f)]` (pp. 13–14). -/
noncomputable def platformPayoffP (a δ φ rf r w q : ℝ) : ℝ :=
  PlatformFinance.WinWin.uniformMean a δ (fun x => φ * (x - q) * q + min ((1 - φ) * (x - q) * q) (w * q * (1 + r)))
    - w * q * (1 + rf)

/-- The platform's equilibrium-path profit `Π^T_p` under trade credit. -/
noncomputable def platformProfitT (a δ φ : ℝ) (σ : PlatformFinance.WinWin.Profile) : ℝ :=
  platformPayoffT a δ φ (σ.order σ.w)

/-- The platform's equilibrium-path profit `Π^P_p` under platform financing at rate `r`. -/
noncomputable def platformProfitP (a δ φ rf r : ℝ) (σ : PlatformFinance.WinWin.Profile) : ℝ :=
  platformPayoffP a δ φ rf r σ.w (σ.order σ.w)

/-- `δ₁ = (5√10 − 14)((1 − φ)a − c(1 + r_f)) / (8(1 − φ))` (p. 11). -/
noncomputable def delta1 (a φ c rf : ℝ) : ℝ :=
  (5 * √10 - 14) * ((1 - φ) * a - c * (1 + rf)) / (8 * (1 - φ))

/-- `δ₂ = ((1 − φ)a − c(1 + r_f)) / ((2 + √6)(1 − φ))` (p. 15). -/
noncomputable def delta2 (a φ c rf : ℝ) : ℝ :=
  ((1 - φ) * a - c * (1 + rf)) / ((√6 + 2) * (1 - φ))

/-- `δ_r = (a(1 − φ) − c(1 + r)) / ((2 + √6)(1 − φ))` (p. 13). -/
noncomputable def deltaR (a φ c r : ℝ) : ℝ :=
  (a * (1 - φ) - c * (1 + r)) / ((2 + √6) * (1 - φ))

/-- `r₁ = (1 − φ)(a − (√6 + 2)δ)/c − 1` (p. 15). -/
noncomputable def r1 (a δ φ c : ℝ) : ℝ :=
  (1 - φ) * (a - (√6 + 2) * δ) / c - 1

/-- The cost threshold `a(1 − φ)²/(1 + r_f)` of Proposition 7 (p. 19). -/
noncomputable def cbar (a φ rf : ℝ) : ℝ :=
  a * (1 - φ) ^ 2 / (1 + rf)

/-- `r₆ = (√(8a²(2 − φ)(1 − φ)³ + φ²(2a(1 − φ) + c(1 + r_f))²) − 2a(1 − φ)φ − c(4 + r_fφ − φ))
/ (2c(2 − φ))` (proof of Proposition 7, p. 41). -/
noncomputable def r6 (a φ c rf : ℝ) : ℝ :=
  (√(8 * a ^ 2 * (2 - φ) * (1 - φ) ^ 3 + φ ^ 2 * (2 * a * (1 - φ) + c * (1 + rf)) ^ 2)
    - 2 * a * (1 - φ) * φ - c * (4 + rf * φ - φ)) / (2 * c * (2 - φ))

/-- `r₅ = min{r₁, r₆}` (proof of Proposition 7, p. 41). -/
noncomputable def r5 (a δ φ c rf : ℝ) : ℝ :=
  min (r1 a δ φ c) (r6 a φ c rf)

/-- The seller's best response (Lemma 1, p. 10) when she owes `W` per unit at the end. -/
noncomputable def qBR (a δ φ W : ℝ) : ℝ :=
  if W ≤ (1 - φ) * (a - 2 * δ) then ((1 - φ) * a - W) / (2 * (1 - φ))
  else ((1 - φ) * (a + δ) - W) / (3 * (1 - φ))

/-- `S = √(((δ + 3a)(1 − φ) − 3c(1 + r_f)) / (δ(1 − φ)))`, the radical of the trade-credit
equilibrium under high uncertainty (proof of Proposition 1, p. 31). -/
noncomputable def sqrtS (a δ φ c rf : ℝ) : ℝ :=
  √(((δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf)) / (δ * (1 - φ)))

/-- The trade-credit equilibrium wholesale price `w^T` (Proposition 1, p. 11; the `δ > δ₁` branch
in the form of the proof, p. 31). -/
noncomputable def wT (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta1 a φ c rf then ((1 - φ) * a + c * (1 + rf)) / 2
  else (1 - φ) * (a - δ * (sqrtS a δ φ c rf - 2))

/-- The trade-credit equilibrium order quantity `q^T` (Proposition 1, p. 11; the `δ > δ₁` branch
in the form of the proof, p. 31). -/
noncomputable def qT (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta1 a φ c rf then ((1 - φ) * a - c * (1 + rf)) / (4 * (1 - φ))
  else δ * (sqrtS a δ φ c rf - 1) / 3

/-- The platform-financing equilibrium wholesale price `w^P` at rate `r` (Proposition 2, p. 13). -/
noncomputable def wP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r))
  else ((1 - φ) * (a + δ) + c * (1 + r)) / (2 * (1 + r))

/-- The platform-financing equilibrium order quantity `q^P` at rate `r` (Proposition 2, p. 13). -/
noncomputable def qP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))
  else ((1 - φ) * (a + δ) - c * (1 + r)) / (6 * (1 - φ))

end PlatformFinance.PlatformProfit


