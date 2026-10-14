-- Prove2me | Definitions.Def_PlatformFinance_EndogRate_Model
-- name    : PlatformFinance_EndogRate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:00.579381+00:00
-- url     : https://prove2.me/theorems/982ffa01-e783-4b9c-8040-786194bc5483
-- title:
--   §3–§5, pp. 8–15, 21–22, 43 — uniform market size, platform-financing payoffs, its subgame-perfect equilibria, the thresholds δ2, δr, r̂1, and the closed forms w^P, q^P, (10), G1
-- statement:
--   This file sets up the platform-financing model of Huang, Lai, Wang and Xiao.
--
--   A capital-less third-party seller buys $q \ge 0$ units from a supplier with unit cost $c$ and sells all of them on a platform at the market-clearing price $p = \tilde a - q$, where the market size $\tilde a$ is uniform on $[a-\delta, a+\delta]$. The platform keeps a share $\varphi$ of the revenue. The supplier and the platform both have capital cost equal to the risk-free rate $r_f$. Under **platform financing** the platform lends the seller the procurement cost $wq$ at interest rate $r$; the supplier is paid upfront. The seller has limited liability: she repays $wq(1+r)$ if her revenue $(1-\varphi)pq$ covers it, and otherwise hands over all of her revenue.
--
--   1. **Expectation.** For $f:\mathbb R\to\mathbb R$, $\mathbb E[f(\tilde a)] = \frac{1}{2\delta}\int_{a-\delta}^{a+\delta} f(x)\,dx$.
--   2. **Payoffs** (pp. 12–14). With $W$ the amount owed per unit,
--   $$\Pi_s(W,q) = \mathbb E\big[((1-\varphi)(\tilde a-q)q - Wq)^+\big],\qquad \Pi^P_m(w,q) = (w-c)q(1+r_f),$$
--   $$\Pi^P_p(w,q) = \mathbb E\big[\varphi(\tilde a-q)q + \min\{(1-\varphi)(\tilde a-q)q,\; wq(1+r)\}\big] - wq(1+r_f).$$
--   3. **Equilibrium.** A profile is a price $w$ and an order rule $w'\mapsto q(w')$. It is a subgame-perfect equilibrium at rate $r$ if (i) for every price $w'$, $q(w')\ge 0$ maximizes $\Pi_s(w'(1+r),\cdot)$ over $q\ge 0$, and $q(w')=0$ when no order yields positive expected profit; (ii) $w$ maximizes $w'\mapsto \Pi^P_m(w', q(w'))$; (iii) every lower price gives the supplier strictly less. The platform's equilibrium profit is $\Pi^P_p(w, q(w))$.
--   4. **Thresholds** (pp. 13, 15): $\delta_r = \frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}$, $\delta_2 = \frac{(1-\varphi)a-c(1+r_f)}{(2+\sqrt6)(1-\varphi)}$, $\delta_3 = \frac{4(27-10\sqrt6)((1-\varphi)a-c(1+r_f))}{43(1-\varphi)}$, $r_1 = \frac{(1-\varphi)(a-(\sqrt6+2)\delta)}{c}-1$, $r_2 = \frac{1-\varphi}{c}\Big(a+3\delta-2\delta\sqrt{\tfrac{(1-\varphi)(\delta+3a)-3c(1+r_f)}{(1-\varphi)\delta}}\Big)-1$, and the seller's threshold rate $\hat r_1(\delta)$, equal to $r_f$ if $\delta\le\delta_2$, $r_1$ if $\delta_2<\delta\le\delta_3$, $r_2$ if $\delta>\delta_3$. The cost threshold of Proposition 8 is $\bar c = a(1-\varphi)^2/(1+r_f)$.
--   5. **Closed forms.** The seller's best response of Lemma 2, the equilibrium $w^P$, $q^P$ of Proposition 2, the no-default platform profit (10)
--   $$\Pi^P_p(r) = \frac{(a(1-\varphi)-c(1+r))\big(a(1-\varphi)(r(\varphi+2)-2r_f(1-\varphi)+3\varphi) - c(r+1)(r(\varphi-2)+2r_f(1-\varphi)-\varphi)\big)}{16(r+1)(1-\varphi)^2},$$
--   and $G_1(r) = c(1+r)^2\big(-a(1-\varphi)\varphi + c((1-\varphi)r_f-(2-\varphi)r-1)\big) + a^2(1-\varphi)^3(1+r_f)$ (p. 43).
--
--   These objects are what Proposition 8 and its milestones are stated about: the goal speaks of equilibria of the game, and the closed forms appear only in milestones.
--
--   **Formalization Note** The expectation is the normalized interval integral rather than an integral against a probability measure; every integrand is continuous, so no integrability junk arises once $\delta>0$. The seller's best response is written with the amount owed $W = w(1+r)$, so its branch condition $W \le (1-\varphi)(a-2\delta)$ is the page's $w \le (1-\varphi)(a-2\delta)/(1+r)$ multiplied by $1+r>0$. The two tie-breaks of the equilibrium are the paper's own conventions: the seller orders zero when indifferent at zero profit (proofs of Propositions 1–2, pp. 31, 33), and the supplier's equilibrium price is the least optimal one, which places the indifference point $\delta=\delta_r$ in the branch $\delta\le\delta_r$ as Proposition 2 does.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, pp. 8–9 (§3), 12–15 (§4.2, Lemma 2, Proposition 2, r̂1), 21–22 (§5), 35 (Π^P_p), 41 ((10)), 43 (G1)

import Mathlib

namespace PlatformFinance.EndogRate

/-! # Platform financing with an endogenous loan rate (Huang, Lai, Wang & Xiao, SSRN 4014045)

§3 (pp. 8–9), §4.2 (pp. 12–14), the threshold `r̂1` (p. 15), §5 (pp. 21–22) and the proof of
Proposition 8 (p. 43). The market size is `ã ~ U[a - δ, a + δ]`, the clearing price is `ã - q`,
the platform keeps a share `φ` of revenue, the supplier's unit cost is `c`, the risk-free rate
(capital cost of supplier and platform) is `rf`, and the platform lends at rate `r`. -/

/-- Expectation of `f(ã)` for `ã ~ U[a - δ, a + δ]`, written as `(2δ)⁻¹ ∫_{a-δ}^{a+δ} f`. -/
noncomputable def uniformMean (a δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * δ)⁻¹ * ∫ x in (a - δ)..(a + δ), f x

/-- The seller's expected profit `E[((1 - φ)(ã - q)q - W q)⁺]` when she owes `W` per unit at the
end of the season (p. 12: `W = w(1 + r)` under platform financing). -/
noncomputable def sellerPayoff (a δ φ W q : ℝ) : ℝ :=
  uniformMean a δ (fun x => max ((1 - φ) * (x - q) * q - W * q) 0)

/-- The supplier's profit under platform financing, `(w - c) q (1 + rf)` (p. 13). -/
def supplierPayoffP (c rf w q : ℝ) : ℝ := (w - c) * q * (1 + rf)

/-- The platform's profit under platform financing (pp. 13–14):
`E[φ(ã - q)q + min{(1 - φ)(ã - q)q, w q (1 + r)}] - w q (1 + rf)`. -/
noncomputable def platformPayoffP (a δ φ rf r w q : ℝ) : ℝ :=
  uniformMean a δ (fun x => φ * (x - q) * q + min ((1 - φ) * (x - q) * q) (w * q * (1 + r)))
    - w * q * (1 + rf)

/-- A strategy profile of the two-stage game: the supplier's wholesale price `w`, and the
seller's order rule, a function of the price she observes. -/
structure Profile where
  w : ℝ
  order : ℝ → ℝ

/-- The seller's rule is a best response at every price `w` (on and off the equilibrium path),
when she owes `owed w` per unit; if no order gives a positive expected profit she orders zero. -/
def IsSellerRule (a δ φ : ℝ) (owed : ℝ → ℝ) (order : ℝ → ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ order w ∧
    (∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ (owed w) q ≤ sellerPayoff a δ φ (owed w) (order w)) ∧
    ((∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ (owed w) q ≤ 0) → order w = 0)

/-- Subgame-perfect equilibrium of the platform-financing game at loan rate `r`: the seller's
rule is a best response to every upfront price `w` (she owes `w(1 + r)` per unit), the supplier's
price is optimal against that rule, and it is the least optimal price. -/
def IsSPEP (a δ φ c rf r : ℝ) (σ : Profile) : Prop :=
  IsSellerRule a δ φ (fun w => w * (1 + r)) σ.order ∧
  (∀ w' : ℝ, supplierPayoffP c rf w' (σ.order w') ≤ supplierPayoffP c rf σ.w (σ.order σ.w)) ∧
  (∀ w' : ℝ, w' < σ.w →
    supplierPayoffP c rf w' (σ.order w') < supplierPayoffP c rf σ.w (σ.order σ.w))

/-- The platform's equilibrium-path profit `Π^P_p` at rate `r` under the profile `σ`. -/
noncomputable def platformProfitP (a δ φ rf r : ℝ) (σ : Profile) : ℝ :=
  platformPayoffP a δ φ rf r σ.w (σ.order σ.w)

/-- `δ2 = ((1 - φ)a - c(1 + rf)) / ((2 + √6)(1 - φ))` (p. 15). -/
noncomputable def delta2 (a φ c rf : ℝ) : ℝ :=
  ((1 - φ) * a - c * (1 + rf)) / ((2 + √6) * (1 - φ))

/-- `δ3 = 4(27 - 10√6)((1 - φ)a - c(1 + rf)) / (43(1 - φ))` (p. 15). -/
noncomputable def delta3 (a φ c rf : ℝ) : ℝ :=
  4 * (27 - 10 * √6) * ((1 - φ) * a - c * (1 + rf)) / (43 * (1 - φ))

/-- `δr = (a(1 - φ) - c(1 + r)) / ((2 + √6)(1 - φ))` (p. 13). -/
noncomputable def deltaR (a φ c r : ℝ) : ℝ :=
  (a * (1 - φ) - c * (1 + r)) / ((2 + √6) * (1 - φ))

/-- `r1 = (1 - φ)(a - (√6 + 2)δ)/c - 1` (p. 15). -/
noncomputable def r1 (a δ φ c : ℝ) : ℝ :=
  (1 - φ) * (a - (√6 + 2) * δ) / c - 1

/-- `r2 = ((1 - φ)/c)(a + 3δ - 2δ √(((1 - φ)(δ + 3a) - 3c(1 + rf))/((1 - φ)δ))) - 1` (p. 15). -/
noncomputable def r2 (a δ φ c rf : ℝ) : ℝ :=
  (1 - φ) / c *
    (a + 3 * δ - 2 * δ * √(((1 - φ) * (δ + 3 * a) - 3 * c * (1 + rf)) / ((1 - φ) * δ))) - 1

/-- The seller's threshold rate `r̂1(δ)` (p. 15): `rf` if `δ ≤ δ2`, `r1` if `δ2 < δ ≤ δ3`,
`r2` if `δ > δ3`. -/
noncomputable def rhat1 (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta2 a φ c rf then rf
  else if δ ≤ delta3 a φ c rf then r1 a δ φ c
  else r2 a δ φ c rf

/-- The cost threshold `a(1 - φ)² / (1 + rf)` of Proposition 8 (p. 22). -/
noncomputable def cbar (a φ rf : ℝ) : ℝ := a * (1 - φ) ^ 2 / (1 + rf)

/-- The seller's best response of Lemma 2 (p. 13), written with the amount `W = w(1 + r)` she owes
per unit: `((1 - φ)a - W)/(2(1 - φ))` if `W ≤ (1 - φ)(a - 2δ)`, and
`((1 - φ)(a + δ) - W)/(3(1 - φ))` otherwise. -/
noncomputable def qBR (a δ φ W : ℝ) : ℝ :=
  if W ≤ (1 - φ) * (a - 2 * δ) then ((1 - φ) * a - W) / (2 * (1 - φ))
  else ((1 - φ) * (a + δ) - W) / (3 * (1 - φ))

/-- The equilibrium upfront wholesale price `w^P` of Proposition 2 (p. 13). -/
noncomputable def wP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r))
  else ((1 - φ) * (a + δ) + c * (1 + r)) / (2 * (1 + r))

/-- The equilibrium procurement quantity `q^P` of Proposition 2 (p. 13). -/
noncomputable def qP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))
  else ((1 - φ) * (a + δ) - c * (1 + r)) / (6 * (1 - φ))

/-- The platform's profit (10) in the no-default regime `δ ≤ δr` (pp. 35, 41, 43). -/
noncomputable def PiP0 (a φ c rf r : ℝ) : ℝ :=
  (a * (1 - φ) - c * (1 + r)) *
      (a * (1 - φ) * (r * (φ + 2) - 2 * rf * (1 - φ) + 3 * φ)
        - c * (r + 1) * (r * (φ - 2) + 2 * rf * (1 - φ) - φ))
    / (16 * (r + 1) * (1 - φ) ^ 2)

/-- `G1(r) = c(1 + r)²(-a(1 - φ)φ + c((1 - φ)rf - (2 - φ)r - 1)) + a²(1 - φ)³(1 + rf)`
(proof of Proposition 8, p. 43). -/
def G1 (a φ c rf r : ℝ) : ℝ :=
  c * (1 + r) ^ 2 * (-a * (1 - φ) * φ + c * ((1 - φ) * rf - (2 - φ) * r - 1))
    + a ^ 2 * (1 - φ) ^ 3 * (1 + rf)

end PlatformFinance.EndogRate


