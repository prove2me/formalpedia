-- Prove2me | Definitions.Def_SearchNeutrality_Commission_Model
-- name    : SearchNeutrality_Commission_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:52.790646+00:00
-- url     : https://prove2.me/theorems/0d6f92b4-b634-4b1c-8702-99ca5517661d
-- title:
--   §3, pp. 8–15 — two consumer types, prominence search with cost c ~ U[0,1], demands (1)–(2), profits, optimal ranking rules, equilibria with and without search neutrality, consumer surplus
-- statement:
--   This file sets up the retail-platform model of Zou and Zhou (§3, pp. 8–15).
--
--   **Products and consumers.** A platform sells its own product $F$ and hosts a third-party seller of product $T$; marginal costs are zero. A unit mass of consumers has unit demand. A consumer of type $k\in\{f,t\}$ values product $j$ at $1$ with probability $\rho_{kj}$ and at $0$ otherwise, where
--   $$\rho_{fF}=\rho_{tT}=\rho_H,\qquad \rho_{fT}=\rho_{tF}=\rho_L .$$
--   Type $f$ has mass $N_f=\alpha$ and type $t$ has mass $N_t=1-\alpha$. Prices are $p_F,p_T\in[0,1]$, and the platform keeps a commission $r$ of the third party's revenue.
--
--   **Rankings and search.** A ranking assigns to each type its *prominent* product; the other product is non-prominent. Searching the prominent product is free; searching the non-prominent one costs $c$, uniform on $[0,1]$. The *neutral* ranking makes $F$ prominent for type $f$ and $T$ prominent for type $t$; the ranking "$F$ prominent for all" is also named.
--
--   **Demands (1)–(2), p. 13.** For a type whose prominent product $1$ and non-prominent product $2$ have match probabilities $\rho_1,\rho_2$ and prices $p_1,p_2$, the demands per consumer are
--   $$d_1=\begin{cases}\rho_1(1-\rho_2^2p_1+\rho_2^2p_2),& p_1>p_2,\\ \rho_1,& p_1\le p_2,\end{cases}\qquad d_2=\begin{cases}\rho_2^2(1-\rho_1+\rho_1p_1-p_2),& p_1>p_2,\\ (1-\rho_1)\rho_2^2(1-p_2),& p_1\le p_2.\end{cases}$$
--   The total demand $D_j$ under a ranking is the mass-weighted sum over the two types. Profits are $\pi_F=p_FD_F+r\,p_TD_T$ for the platform and $\pi_T=(1-r)p_TD_T$ for the third-party seller (p. 15).
--
--   **Optimal ranking rules.** Without search neutrality the platform, after seeing the prices, chooses for each consumer the ranking that maximizes its expected profit from her (p. 10). A *ranking rule* $\sigma$ maps a price pair to a ranking; it is *optimal* if at every price pair in $[0,1]^2$ and for every type it selects a prominent product maximizing the platform's per-consumer profit $p_Fd_F+r\,p_Td_T$ (ties broken arbitrarily).
--
--   **Equilibria.**
--   1. A *price equilibrium under a fixed ranking* $\sigma_0$ is a pair $(p_F,p_T)\in[0,1]^2$ from which neither seller gains by a unilateral price change within $[0,1]$.
--   2. An *equilibrium with search neutrality* is a price equilibrium under the neutral ranking.
--   3. An *equilibrium without search neutrality* is a triple $(p_F,p_T,\sigma)$ with $\sigma$ an optimal ranking rule, $(p_F,p_T)\in[0,1]^2$, and no seller gaining by a unilateral deviation $q\in[0,1]$ when the ranking is the one $\sigma$ chooses at the deviated prices. This is the subgame-perfect equilibrium of the timing on p. 11 (prices first, ranking second).
--
--   **Consumer surplus.** A consumer with prominent product $(\rho_1,p_1)$, non-prominent product $(\rho_2,p_2)$ and search cost $c$ obtains
--   $$\rho_1\bigl[1-p_1+(\rho_2(p_1-p_2)-c)^+\bigr]+(1-\rho_1)\bigl(\rho_2(1-p_2)-c\bigr)^+ ,$$
--   and the total consumer surplus is $\alpha\,\mathbb E_c[CS_f]+(1-\alpha)\,\mathbb E_c[CS_t]$ with $c\sim U[0,1]$ (Appendix, pp. 43–44).
--
--   These objects are the common ground of Proposition 4, Lemma 1 and Proposition 5.
--
--   **Formalization Note** The expectation over $c$ is the interval integral $\int_0^1$; the integrand is continuous in $c$, so no integrability side condition arises. The same objects, with the same names, are defined in the sub-namespace `SearchNeutrality.ShortTerm` of the companion mission, because draft items cannot import each other.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), pp. 8–15, §3.1–§3.4, (1)–(2), profits p. 15; consumer surplus Appendix pp. 43–44

import Mathlib

namespace SearchNeutrality.Commission

/-! Zou & Zhou, *Self-Preferencing and Search Neutrality in Online Retail Platforms*, authors'
manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), §3 (pp. 8–14) and p. 15.
The same objects, with the same names, as `SearchNeutrality.ShortTerm.Model` of the companion
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

end SearchNeutrality.Commission


