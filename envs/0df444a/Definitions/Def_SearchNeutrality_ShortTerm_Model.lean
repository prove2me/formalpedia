-- Prove2me | Definitions.Def_SearchNeutrality_ShortTerm_Model
-- name    : SearchNeutrality_ShortTerm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:55.729336+00:00
-- url     : https://prove2.me/theorems/5d4a7a5e-4b51-4e30-9377-0720529a8a53
-- title:
--   §3, pp. 8–15 — two consumer types, prominence search with cost c ~ U[0,1], demands (1)–(2), profits, optimal rankings, equilibria with and without search neutrality, consumer surplus, Condition 1
-- statement:
--   The model of Zou and Zhou. A retail platform sells its own product $F$ and hosts a third-party seller of product $T$; marginal costs are zero. A unit mass of consumers has unit demand; a product either matches a consumer (value $1$) or not (value $0$).
--
--   1. **Types.** A fraction $N_f=\alpha$ of consumers are of type $f$ and $N_t=1-\alpha$ of type $t$. A type-$f$ consumer is matched by $F$ with probability $\rho_H$ and by $T$ with probability $\rho_L$; a type-$t$ consumer the reverse, where $1>\rho_H>\rho_L>0$.
--   2. **Rankings.** A ranking assigns to each type its *prominent* product (shown first); the other product is non-prominent. "$F$ prominent for all" sends both types to $F$; the *neutral* ranking makes $F$ prominent for type $f$ and $T$ prominent for type $t$.
--   3. **Demand.** Prices are $p_F,p_T\in[0,1]$. For a type with prominent product $1$ and non-prominent product $2$, match probabilities $\rho_1,\rho_2$ and prices $p_1,p_2$, the per-consumer demands are equations (1)–(2) of the paper:
--   $$
--   d_1=\begin{cases}\rho_1(1-\rho_2^2p_1+\rho_2^2p_2),&p_1>p_2,\\ \rho_1,&p_1\le p_2,\end{cases}\qquad
--   d_2=\begin{cases}\rho_2^2(1-\rho_1+\rho_1p_1-p_2),&p_1>p_2,\\ (1-\rho_1)\rho_2^2(1-p_2),&p_1\le p_2.\end{cases}
--   $$
--   Total demand $D_j$ for product $j$ under a ranking is the mass-weighted sum over the two types.
--   4. **Profits.** The platform earns $\pi_F=p_FD_F+r\,p_TD_T$ (its own sales plus the commission $r$ on the third party's revenue), and the third-party seller earns $\pi_T=(1-r)p_TD_T$.
--   5. **Ranking without neutrality.** A ranking rule maps each price pair to a ranking. It is *optimal* if at every price pair in $[0,1]^2$ and for every type it picks a prominent product that maximizes the platform's expected profit from one consumer of that type, $p_F d_F+r\,p_T d_T$ (ties broken arbitrarily).
--   6. **Equilibria.** A *price equilibrium under a fixed ranking* is a Nash equilibrium in prices on $[0,1]^2$. An *equilibrium without search neutrality* (NS) is a price pair and an optimal ranking rule such that no seller gains from a unilateral price deviation in $[0,1]$, the profit after the deviation being evaluated at the ranking the rule picks at the deviated prices (sellers price first, then the platform ranks). An *equilibrium with search neutrality* (S) is a price equilibrium under the neutral ranking.
--   7. **Consumer surplus.** Searching the prominent product is free; searching the other costs $c\sim U[0,1]$. A consumer with search cost $c$ obtains
--   $$
--   \rho_1\bigl(1-p_1+(\rho_2(p_1-p_2)-c)^+\bigr)+(1-\rho_1)(\rho_2(1-p_2)-c)^+ ,
--   $$
--   and total consumer surplus is $CS=\alpha\,\mathbb E_c[CS_f]+(1-\alpha)\,\mathbb E_c[CS_t]$, the expectation being the integral over $c\in[0,1]$.
--   8. **Condition 1.** $r\le 0.64\,\rho_L/\rho_H$ and $\rho_L\le 0.975$.
--
--   These objects are the common ground of every statement of the mission: the equilibria with and without search neutrality and the consumer surplus they produce.
--
--   **Formalization Note** Prices outside $[0,1]$ are never used: equilibrium prices and all deviations are restricted to $[0,1]$. The demands are the paper's equations (1)–(2), not re-derived from the search process. Consumer surplus is the interval integral $\int_0^1$ over the search cost of a continuous integrand, so there is no integrability junk value; it is not defined by the paper's closed-form displays, which are separate theorems.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), pp. 8–15, §3.1–§3.4, equations (1)–(2), §4.1.1 profits, Condition 1 (p. 15); Appendix pp. 43–44 (consumer surplus)

import Mathlib

namespace SearchNeutrality.ShortTerm

/-! Zou & Zhou, *Self-Preferencing and Search Neutrality in Online Retail Platforms*, authors'
manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), §3 (pp. 8–14), p. 15 (profits,
Condition 1) and the Appendix (pp. 43–44, consumer surplus).
The same objects, with the same names, as `SearchNeutrality.Commission.Model` of the companion
mission (drafts cannot import drafts). -/

/-- The two products (p. 8): `F`, sold by the platform, and `T`, sold by the third-party seller. -/
inductive Product
  | F
  | T
  deriving DecidableEq

instance : Fintype Product := ⟨{.F, .T}, fun x => by cases x <;> simp⟩

/-- The two consumer types (p. 8): type `f` on average prefers `F`, type `t` prefers `T`. -/
inductive CType
  | f
  | t
  deriving DecidableEq

instance : Fintype CType := ⟨{.f, .t}, fun x => by cases x <;> simp⟩

/-- The other product. -/
def Product.other : Product → Product
  | .F => .T
  | .T => .F

/-- Match probabilities (p. 8): `ρ_fF = ρ_tT = ρ_H` and `ρ_fT = ρ_tF = ρ_L`. -/
def matchProb (ρH ρL : ℝ) : CType → Product → ℝ
  | .f, .F => ρH
  | .f, .T => ρL
  | .t, .F => ρL
  | .t, .T => ρH

/-- Masses of the two types (p. 8): `N_f = α`, `N_t = 1 - α`. -/
def mass (α : ℝ) : CType → ℝ
  | .f => α
  | .t => 1 - α

/-- The price of a product given the price pair `(p_F, p_T)`. -/
def price (pF pT : ℝ) : Product → ℝ
  | .F => pF
  | .T => pT

/-- A ranking (p. 9): for each consumer type, the product shown first (the prominent product);
the other product is non-prominent. -/
abbrev Ranking := CType → Product

/-- Product `F` prominent for all consumers. -/
def fPrimeAll : Ranking := fun _ => .F

/-- The search-neutral ranking (p. 10): `F` prominent for type `f`, `T` prominent for type `t`. -/
def neutral : Ranking
  | .f => .F
  | .t => .T

/-- Demand (1), p. 13, per consumer (`D_k1 / N_k`): the prominent product's demand, where `ρ1, ρ2`
are the type's match probabilities and `p1, p2` the prices of its prominent and non-prominent
product. -/
noncomputable def promDemand (ρ1 ρ2 p1 p2 : ℝ) : ℝ :=
  if p1 > p2 then ρ1 * (1 - ρ2 ^ 2 * p1 + ρ2 ^ 2 * p2) else ρ1

/-- Demand (2), p. 13, per consumer (`D_k2 / N_k`): the non-prominent product's demand. -/
noncomputable def nonpromDemand (ρ1 ρ2 p1 p2 : ℝ) : ℝ :=
  if p1 > p2 then ρ2 ^ 2 * (1 - ρ1 + ρ1 * p1 - p2) else (1 - ρ1) * ρ2 ^ 2 * (1 - p2)

/-- Per-consumer demand for product `j` from a type-`k` consumer whose prominent product is
`prom`, by (1)–(2). -/
noncomputable def typeDemand (ρH ρL pF pT : ℝ) (k : CType) (prom j : Product) : ℝ :=
  if j = prom then
    promDemand (matchProb ρH ρL k prom) (matchProb ρH ρL k prom.other)
      (price pF pT prom) (price pF pT prom.other)
  else
    nonpromDemand (matchProb ρH ρL k prom) (matchProb ρH ρL k prom.other)
      (price pF pT prom) (price pF pT prom.other)

/-- Total demand `D_j` for product `j` under the ranking `σ`: the mass-weighted sum over types. -/
noncomputable def demand (ρH ρL α : ℝ) (σ : Ranking) (pF pT : ℝ) (j : Product) : ℝ :=
  ∑ k : CType, mass α k * typeDemand ρH ρL pF pT k (σ k) j

/-- The platform's profit (p. 15): `π_F = p_F D_F + r p_T D_T`. -/
noncomputable def platformProfit (ρH ρL r α : ℝ) (σ : Ranking) (pF pT : ℝ) : ℝ :=
  pF * demand ρH ρL α σ pF pT .F + r * pT * demand ρH ρL α σ pF pT .T

/-- The third-party seller's profit (p. 15): `π_T = (1 - r) p_T D_T`. -/
noncomputable def sellerProfit (ρH ρL r α : ℝ) (σ : Ranking) (pF pT : ℝ) : ℝ :=
  (1 - r) * pT * demand ρH ρL α σ pF pT .T

/-- The platform's expected profit from one type-`k` consumer when `prom` is her prominent
product (p. 10: "for each consumer the platform will choose the ranking to maximize its expected
profit from her"). -/
noncomputable def platformTypeProfit (ρH ρL r pF pT : ℝ) (k : CType) (prom : Product) : ℝ :=
  pF * typeDemand ρH ρL pF pT k prom .F + r * pT * typeDemand ρH ρL pF pT k prom .T

/-- A ranking rule `σ` (prices ↦ ranking) is optimal for the platform without search neutrality
(p. 10) when at every price pair in `[0,1]²` and for every type it picks a prominent product that
maximizes the platform's per-consumer profit. Ties may be broken arbitrarily. -/
def IsOptimalRankingRule (ρH ρL r : ℝ) (σ : ℝ → ℝ → Ranking) : Prop :=
  ∀ pF ∈ Set.Icc (0 : ℝ) 1, ∀ pT ∈ Set.Icc (0 : ℝ) 1, ∀ k : CType, ∀ prom : Product,
    platformTypeProfit ρH ρL r pF pT k prom ≤ platformTypeProfit ρH ρL r pF pT k (σ pF pT k)

/-- Nash equilibrium in prices `p_F, p_T ∈ [0,1]` (p. 8) with the ranking held fixed at `σ₀`:
seller `F` (the platform) maximizes `π_F` and seller `T` maximizes `π_T`, each over `[0,1]`. -/
def IsPriceEquilibrium (ρH ρL r α : ℝ) (σ₀ : Ranking) (pF pT : ℝ) : Prop :=
  pF ∈ Set.Icc (0 : ℝ) 1 ∧ pT ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1, platformProfit ρH ρL r α σ₀ q pT ≤ platformProfit ρH ρL r α σ₀ pF pT) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1, sellerProfit ρH ρL r α σ₀ pF q ≤ sellerProfit ρH ρL r α σ₀ pF pT)

/-- Equilibrium without search neutrality (§3.3, p. 11: prices first, then the platform ranks),
i.e. a subgame-perfect equilibrium: `σ` is an optimal ranking rule at every price pair, the prices
lie in `[0,1]`, and no seller gains by a unilateral price deviation `q ∈ [0,1]`, evaluated at the
ranking `σ` chooses at the deviated prices. -/
def IsNSEquilibrium (ρH ρL r α pF pT : ℝ) (σ : ℝ → ℝ → Ranking) : Prop :=
  IsOptimalRankingRule ρH ρL r σ ∧
  pF ∈ Set.Icc (0 : ℝ) 1 ∧ pT ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
    platformProfit ρH ρL r α (σ q pT) q pT ≤ platformProfit ρH ρL r α (σ pF pT) pF pT) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
    sellerProfit ρH ρL r α (σ pF q) pF q ≤ sellerProfit ρH ρL r α (σ pF pT) pF pT)

/-- Equilibrium with search neutrality (p. 10): a price equilibrium under the neutral ranking. -/
def IsSEquilibrium (ρH ρL r α pF pT : ℝ) : Prop :=
  IsPriceEquilibrium ρH ρL r α neutral pF pT

/-- Realized expected surplus of a consumer with search cost `c` for her non-prominent product,
whose prominent product (searched for free) has match probability `ρ1` and price `p1`, and whose
non-prominent product has match probability `ρ2` and price `p2` (Appendix, p. 43, the expression
of `CS_f^{NS}` written for an arbitrary ranking). -/
def typeSurplus (ρ1 ρ2 p1 p2 c : ℝ) : ℝ :=
  ρ1 * (1 - p1 + max (ρ2 * (p1 - p2) - c) 0) + (1 - ρ1) * max (ρ2 * (1 - p2) - c) 0

/-- Total consumer surplus (Appendix, p. 44) under the ranking `σ`:
`CS = α E_c[CS_f] + (1 - α) E_c[CS_t]` with `c ~ U[0,1]` (p. 9), the expectation being the
integral over `c ∈ [0,1]`. -/
noncomputable def consumerSurplus (ρH ρL α : ℝ) (σ : Ranking) (pF pT : ℝ) : ℝ :=
  ∑ k : CType, mass α k *
    ∫ c in (0 : ℝ)..1,
      typeSurplus (matchProb ρH ρL k (σ k)) (matchProb ρH ρL k (σ k).other)
        (price pF pT (σ k)) (price pF pT (σ k).other) c

/-- Condition 1 (p. 15), the low-commission region assumed throughout §4.1:
`r ≤ 0.64 ρ_L / ρ_H` and `ρ_L ≤ 0.975`. -/
def Condition1 (ρH ρL r : ℝ) : Prop :=
  r ≤ (64 / 100 : ℝ) * ρL / ρH ∧ ρL ≤ (975 / 1000 : ℝ)

end SearchNeutrality.ShortTerm


