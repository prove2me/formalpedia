-- Prove2me | Definitions.Def_PlatformFinance_WinWin_Model
-- name    : PlatformFinance_WinWin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:41.297686+00:00
-- url     : https://prove2.me/theorems/80c396a2-00f9-444a-8a08-d869e592a3a6
-- title:
--   §3–§4, pp. 8–15, 31–39 — uniform market size, payoffs (1)–(2), the trade-credit and platform-financing games, their equilibria, and the thresholds r̂₁, r̂₂
-- statement:
--   This file sets up the model of Huang, Lai, Wang and Xiao (§3, p. 8). A supplier with unit production cost $c>0$ sells to a capital-constrained third-party seller, who resells on an online platform. The market size $\tilde a$ is uniform on $[a-\delta,a+\delta]$ with $0<\delta<a$; the market clearing price is $p=\tilde a-q$, where $q$ is the procurement quantity, and all $q$ units are sold. The platform keeps the share $\varphi\in[0,1)$ of revenue. Supplier and platform both have capital cost equal to the risk-free rate $r_f\ge 0$, and $(1-\varphi)a>c(1+r_f)$.
--
--   **Expectation.** For a function $f$ of the market size,
--   $$\mathbb E[f(\tilde a)] = \frac{1}{2\delta}\int_{a-\delta}^{a+\delta} f(x)\,dx .$$
--
--   **Payoffs.** When the seller owes $W$ per unit at the end of the season ($W=w$ under trade credit, $W=w(1+r)$ under a platform loan at rate $r$), her limited-liability expected profit is (1), p. 10,
--   $$\Pi_s(W,q)=\mathbb E\big[((1-\varphi)(\tilde a-q)q-Wq)^+\big].$$
--   Under trade credit the supplier earns (2), p. 10, $\Pi^T_m(w,q)=\mathbb E[\min\{(1-\varphi)(\tilde a-q)q,\,wq\}]-cq(1+r_f)$; under platform financing he is paid upfront and earns $\Pi^P_m(w,q)=(w-c)q(1+r_f)$ (p. 13).
--
--   **Games and equilibria.** Both games are two-stage Stackelberg games: the supplier sets the wholesale price $w$, then the seller, having observed $w$, chooses $q\ge 0$. A strategy profile is a price $w$ together with an order rule $q(\cdot)$. A profile is a subgame-perfect equilibrium when
--   1. for every price $w$, $q(w)\ge 0$ maximizes the seller's payoff over $q\ge 0$, and $q(w)=0$ whenever no $q\ge 0$ earns a positive payoff;
--   2. the supplier's price maximizes his payoff against the rule $q(\cdot)$ over all real prices;
--   3. every strictly lower price earns the supplier strictly less (the equilibrium price is the least maximizer).
--
--   The equilibrium-path profits are $\Pi^T_s,\Pi^T_m$ (trade credit) and $\Pi^P_s,\Pi^P_m$ (platform financing).
--
--   **Thresholds and closed forms.** With $K_0=(1-\varphi)a-c(1+r_f)$ and $S=\sqrt{((\delta+3a)(1-\varphi)-3c(1+r_f))/(\delta(1-\varphi))}$, the file defines
--   $\delta_1=(5\sqrt{10}-14)K_0/(8(1-\varphi))$, $\delta_2=K_0/((\sqrt6+2)(1-\varphi))$, $\delta_3=4(27-10\sqrt6)K_0/(43(1-\varphi))$, $\delta_r=(a(1-\varphi)-c(1+r))/((2+\sqrt6)(1-\varphi))$, the rates $r_1,r_2$ (p. 15), $r_3$, $K$, $r_4$ (pp. 38–39), and the threshold functions
--   $$\hat r_1(\delta)=\begin{cases}r_f&\delta\le\delta_2\\ r_1&\delta_2<\delta\le\delta_3\\ r_2&\delta>\delta_3\end{cases}\qquad \hat r_2(\delta)=\begin{cases}r_f&\delta\le\delta_2\\ r_3&\delta_2<\delta\le\delta_1\\ r_4&\delta>\delta_1.\end{cases}$$
--   It also defines the seller's best response $q(W)$ of Lemma 1, the trade-credit equilibrium $(w^T,q^T)$ of Proposition 1 and the platform-financing equilibrium $(w^P,q^P)$ of Proposition 2.
--
--   **Formalization Note.** The expectation is the normalized interval integral above, not an integral against a probability measure; every integrand used is continuous. The two tie-break clauses of the equilibrium are the paper's own conventions (the seller orders nothing when indifferent, pp. 31, 33; the boundary $\delta=\delta_1$ is assigned to the low price, p. 32). Two printed slips are corrected here: $r_3$ uses $(2ac+8c\delta)$ under the inner root where p. 38 prints $(2ac+8\delta)$; the $\delta>\delta_1$ branch of $w^T,q^T$ uses the proof's form $w^T=(1-\varphi)(a-\delta(S-2))$, $q^T=\delta(S-1)/3$ (p. 31) where p. 11 omits a factor $\delta$ under the root.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, pp. 8–15 and 31–39, §3–§4 (model p. 8; (1), (2) p. 10; p. 13; thresholds pp. 11, 13, 15, 18, 38–39)

import Mathlib

namespace PlatformFinance.WinWin

/-- Expectation over the uniform market size `ã ~ U[a - δ, a + δ]` (§3, p. 8), written as the
interval integral `(2δ)⁻¹ ∫_{a-δ}^{a+δ} f`. -/
noncomputable def uniformMean (a δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * δ)⁻¹ * ∫ x in (a - δ)..(a + δ), f x

/-- The seller's expected profit (1), p. 10, when she owes `W` per unit at the end of the season
(`W = w` under trade credit, `W = w(1 + r)` under platform financing, p. 12):
`E[((1 - φ)(ã - q)q - Wq)⁺]`. -/
noncomputable def sellerPayoff (a δ φ W q : ℝ) : ℝ :=
  uniformMean a δ (fun x => max ((1 - φ) * (x - q) * q - W * q) 0)

/-- The trade-credit supplier's expected profit (2), p. 10:
`E[min{(1 - φ)(ã - q)q, wq}] - cq(1 + r_f)`. -/
noncomputable def supplierPayoffT (a δ φ c rf w q : ℝ) : ℝ :=
  uniformMean a δ (fun x => min ((1 - φ) * (x - q) * q) (w * q)) - c * q * (1 + rf)

/-- The platform-financing supplier's profit, p. 13: `(w - c)q(1 + r_f)`. -/
def supplierPayoffP (c rf w q : ℝ) : ℝ :=
  (w - c) * q * (1 + rf)

/-- A strategy profile of the two-stage game: the supplier's wholesale price `w`, and the
seller's order rule, a function of the wholesale price she observes. -/
structure Profile where
  w : ℝ
  order : ℝ → ℝ

/-- `order` is a best-response rule of the seller when she owes `owed w` per unit at price `w`:
for every `w` (on or off the equilibrium path) `order w ≥ 0` maximizes the seller's expected
profit over `q ≥ 0`, and if no `q ≥ 0` earns a positive profit she orders `0`
(seller tie-break, proofs of Propositions 1 and 2, pp. 31, 33). -/
def IsSellerRule (a δ φ : ℝ) (owed : ℝ → ℝ) (order : ℝ → ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ order w ∧
    (∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ (owed w) q ≤ sellerPayoff a δ φ (owed w) (order w)) ∧
    ((∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ (owed w) q ≤ 0) → order w = 0)

/-- Subgame-perfect equilibrium of the trade-credit game (§4.1, pp. 9–11), solved by backward
induction: the seller best-responds to every deferred wholesale price, the supplier's price
maximizes his expected profit (2) against the seller's rule, and it is the least such price
(supplier tie-break, the paper's convention at `δ = δ₁`, p. 32). -/
def IsSPET (a δ φ c rf : ℝ) (σ : Profile) : Prop :=
  IsSellerRule a δ φ (fun w => w) σ.order ∧
  (∀ w' : ℝ, supplierPayoffT a δ φ c rf w' (σ.order w') ≤
    supplierPayoffT a δ φ c rf σ.w (σ.order σ.w)) ∧
  (∀ w' : ℝ, w' < σ.w → supplierPayoffT a δ φ c rf w' (σ.order w') <
    supplierPayoffT a δ φ c rf σ.w (σ.order σ.w))

/-- Subgame-perfect equilibrium of the platform-financing game with loan rate `r`
(§4.2, pp. 12–13): the seller owes `w(1 + r)` per unit, the supplier is paid `w` upfront, and
the supplier's price is the least maximizer of `(w - c)q(w)(1 + r_f)`. -/
def IsSPEP (a δ φ c rf r : ℝ) (σ : Profile) : Prop :=
  IsSellerRule a δ φ (fun w => w * (1 + r)) σ.order ∧
  (∀ w' : ℝ, supplierPayoffP c rf w' (σ.order w') ≤ supplierPayoffP c rf σ.w (σ.order σ.w)) ∧
  (∀ w' : ℝ, w' < σ.w → supplierPayoffP c rf w' (σ.order w') <
    supplierPayoffP c rf σ.w (σ.order σ.w))

/-- Equilibrium-path profit of the seller under trade credit, `Π^T_s`. -/
noncomputable def sellerProfitT (a δ φ : ℝ) (σ : Profile) : ℝ :=
  sellerPayoff a δ φ σ.w (σ.order σ.w)

/-- Equilibrium-path profit of the supplier under trade credit, `Π^T_m`. -/
noncomputable def supplierProfitT (a δ φ c rf : ℝ) (σ : Profile) : ℝ :=
  supplierPayoffT a δ φ c rf σ.w (σ.order σ.w)

/-- Equilibrium-path profit of the seller under platform financing, `Π^P_s`. -/
noncomputable def sellerProfitP (a δ φ r : ℝ) (σ : Profile) : ℝ :=
  sellerPayoff a δ φ (σ.w * (1 + r)) (σ.order σ.w)

/-- Equilibrium-path profit of the supplier under platform financing, `Π^P_m`. -/
def supplierProfitP (c rf : ℝ) (σ : Profile) : ℝ :=
  supplierPayoffP c rf σ.w (σ.order σ.w)

/-- `K₀ = (1 - φ)a - c(1 + r_f)`, the expected unit margin of the supply chain (p. 8). -/
def K0 (a φ c rf : ℝ) : ℝ :=
  (1 - φ) * a - c * (1 + rf)

/-- `S = √(((δ + 3a)(1 - φ) - 3c(1 + r_f)) / (δ(1 - φ)))` (proof of Proposition 1, p. 31). -/
noncomputable def Sroot (a δ φ c rf : ℝ) : ℝ :=
  Real.sqrt (((δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf)) / (δ * (1 - φ)))

/-- `δ₁ = (5√10 - 14)((1 - φ)a - c(1 + r_f)) / (8(1 - φ))` (p. 11). -/
noncomputable def delta1 (a φ c rf : ℝ) : ℝ :=
  (5 * Real.sqrt 10 - 14) * K0 a φ c rf / (8 * (1 - φ))

/-- `δ₂ = ((1 - φ)a - c(1 + r_f)) / ((2 + √6)(1 - φ))` (p. 15). -/
noncomputable def delta2 (a φ c rf : ℝ) : ℝ :=
  K0 a φ c rf / ((Real.sqrt 6 + 2) * (1 - φ))

/-- `δ₃ = 4(27 - 10√6)((1 - φ)a - c(1 + r_f)) / (43(1 - φ))` (p. 15). -/
noncomputable def delta3 (a φ c rf : ℝ) : ℝ :=
  4 * (27 - 10 * Real.sqrt 6) * K0 a φ c rf / (43 * (1 - φ))

/-- `δ_r = (a(1 - φ) - c(1 + r)) / ((2 + √6)(1 - φ))` (p. 13). -/
noncomputable def deltaR (a φ c r : ℝ) : ℝ :=
  (a * (1 - φ) - c * (1 + r)) / ((2 + Real.sqrt 6) * (1 - φ))

/-- `r₁ = (1 - φ)(a - (√6 + 2)δ)/c - 1` (p. 15). -/
noncomputable def r1 (a δ φ c : ℝ) : ℝ :=
  (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) / c - 1

/-- `r₂ = ((1 - φ)/c)(a + 3δ - 2δ S) - 1` (p. 15). -/
noncomputable def r2 (a δ φ c rf : ℝ) : ℝ :=
  (1 - φ) / c * (a + 3 * δ - 2 * δ * Sroot a δ φ c rf) - 1

/-- `r₃` (p. 38), with `(2ac + 8cδ)` under the inner root (the page prints `8δ`, a slip:
`r₃` is the smaller root in `r` of `2(1+r_f)((a+δ)(1-φ) - c(1+r))² = 3(1+r)(a(1-φ) - c(1+r_f))²`). -/
noncomputable def r3 (a δ φ c rf : ℝ) : ℝ :=
  (3 * a ^ 2 * (1 - φ) ^ 2 + 3 * c ^ 2 * (rf + 1) ^ 2 - 2 * c * (a - 2 * δ) * (rf + 1) * (1 - φ)
      - 4 * c ^ 2 * (rf + 1)
      - Real.sqrt 3 * (a * (1 - φ) - c * (1 + rf)) *
        Real.sqrt (3 * a ^ 2 * (1 - φ) ^ 2 + 3 * c ^ 2 * (rf + 1) ^ 2
          + (2 * a * c + 8 * c * δ) * (rf + 1) * (1 - φ)))
    / (4 * c ^ 2 * (rf + 1))

/-- `K = 2√(((δ + 3a)(1 - φ) - 3c(1 + r_f))³ / (δ(1 - φ))) - (9a + 2δ)(1 - φ) + 9c(1 + r_f)`
(p. 38). -/
noncomputable def Kfun (a δ φ c rf : ℝ) : ℝ :=
  2 * Real.sqrt ((((δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf)) ^ 3) / (δ * (1 - φ)))
    - (9 * a + 2 * δ) * (1 - φ) + 9 * c * (1 + rf)

/-- `r₄` (p. 39). -/
noncomputable def r4 (a δ φ c rf : ℝ) : ℝ :=
  (9 * c * (1 + rf) * ((a + δ) * (1 - φ) - c) + 2 * δ * (1 - φ) * Kfun a δ φ c rf
      - 2 * Real.sqrt (δ ^ 2 * (1 - φ) ^ 2 * (Kfun a δ φ c rf) ^ 2
          + 9 * c * δ * (a + δ) * (1 + rf) * (1 - φ) ^ 2 * Kfun a δ φ c rf))
    / (9 * c ^ 2 * (1 + rf))

/-- The seller's threshold interest rate `r̂₁(δ)` (p. 15). -/
noncomputable def rhat1 (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta2 a φ c rf then rf
  else if δ ≤ delta3 a φ c rf then r1 a δ φ c
  else r2 a δ φ c rf

/-- The supplier's threshold interest rate `r̂₂(δ)` (p. 18 and p. 39). -/
noncomputable def rhat2 (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta2 a φ c rf then rf
  else if δ ≤ delta1 a φ c rf then r3 a δ φ c rf
  else r4 a δ φ c rf

/-- The seller's best response of Lemma 1 (p. 10) when she owes `W` per unit. -/
noncomputable def qBR (a δ φ W : ℝ) : ℝ :=
  if W ≤ (1 - φ) * (a - 2 * δ) then ((1 - φ) * a - W) / (2 * (1 - φ))
  else ((1 - φ) * (a + δ) - W) / (3 * (1 - φ))

/-- The trade-credit equilibrium wholesale price of Proposition 1 (p. 11), with the proof's
form of the `δ > δ₁` branch (p. 31, `w₂`): `(1 - φ)(a - δ(S - 2))`. -/
noncomputable def wT (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta1 a φ c rf then ((1 - φ) * a + c * (1 + rf)) / 2
  else (1 - φ) * (a - δ * (Sroot a δ φ c rf - 2))

/-- The trade-credit equilibrium order quantity of Proposition 1 (p. 11), with the proof's
form of the `δ > δ₁` branch: `δ(S - 1)/3`. -/
noncomputable def qT (a δ φ c rf : ℝ) : ℝ :=
  if δ ≤ delta1 a φ c rf then K0 a φ c rf / (4 * (1 - φ))
  else δ * (Sroot a δ φ c rf - 1) / 3

/-- The platform-financing equilibrium wholesale price of Proposition 2 (p. 13). -/
noncomputable def wP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a + c * (1 + r)) / (2 * (1 + r))
  else ((1 - φ) * (a + δ) + c * (1 + r)) / (2 * (1 + r))

/-- The platform-financing equilibrium order quantity of Proposition 2 (p. 13). -/
noncomputable def qP (a δ φ c r : ℝ) : ℝ :=
  if δ ≤ deltaR a φ c r then ((1 - φ) * a - c * (1 + r)) / (4 * (1 - φ))
  else ((1 - φ) * (a + δ) - c * (1 + r)) / (6 * (1 - φ))

end PlatformFinance.WinWin


