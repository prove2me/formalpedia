-- Prove2me | Definitions.Def_drug_market_model
-- name    : drug_market_model
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T13:34:35.870467+00:00
-- url     : https://prove2.me/theorems/1048b689-78b8-4e05-8c1c-fa3af553562e
-- title:
--   Drug-market vertical network: primitives
-- statement:
--   Primitives of the vertically related illegal drug market (Nogueira Júnior 2019, ch. 3). Consumers are uniformly distributed on $[0,1]$ with unit demand; the two retail points of sale sit at the endpoints ($a=0$, $1-b=1$). A consumer at $x$ gets utility $u - p_i - t\,|x-\theta_i| - z\,(v_a+v_b+v_r)$, where $p_i$ is the retail price, $t>0$ the transport cost, and $z\,(v_a+v_b+v_r)$ the disutility from total violence (retail violence $v_a,v_b$ and police repression $v_r$), which is a non-rival, non-excludable bad and therefore cancels in the choice between outlets. Hotelling demands are $D_a=\tfrac12+(p_b-p_a)/(2t)$ and $D_b=1-D_a$. The police succeed against retailer $i$ with probability $q^{v_i/v_r}$ and against wholesaler $i$ with probability $q^{1/v_{ri}}$, where $q\in(0,1)$ measures repression effectiveness; a caught agent pays cost $s>0$. Retailer $i$'s expected profit is $(1-q^{v_i/v_r})(p_i-w_i)D_i - s\,q^{v_i/v_r} - v_i$, with $w_i$ the wholesale price. Wholesaler $i$'s expected profit is $(1-q^{1/v_{ri}})(w_i-c)D_i - s\,D_i\,q^{1/v_{ri}}$, with constant marginal cost $c$ and demand evaluated at the retail price equilibrium. All functions are total on $\mathbb{R}$; the economic parameter regime is imposed as hypotheses in the theorems.
-- source:
--   Gilberto José Nogueira Júnior, *Mercado de Drogas e Repressão: Efeitos da Intervenção Governamental sobre a Violência gerada pelo Mercado de Drogas numa Rede Verticalmente Relacionada*, MSc dissertation, UFPE/PIMES, 2019, Chapter 3. Equations (3.1)–(3.7), (3.13)–(3.16), (3.42)–(3.45).

import Mathlib

noncomputable section

namespace DrugMarket



/-- Consumer utility at point of sale `a = 0` (eq. 3.2, with `a = 0`). -/
def utilA (u z t p_a v_a v_b v_r x : ℝ) : ℝ :=
  u - p_a - t * |x| - z * (v_a + v_b + v_r)

/-- Consumer utility at point of sale `1 - b = 1` (eq. 3.3, with `b = 0`). -/
def utilB (u z t p_b v_a v_b v_r x : ℝ) : ℝ :=
  u - p_b - t * |1 - x| - z * (v_a + v_b + v_r)

/-- Hotelling demand of retailer A (eq. 3.7, `a = b = 0`). -/
def demandA (t p_a p_b : ℝ) : ℝ := (1 : ℝ) / 2 + (p_b - p_a) / (2 * t)

/-- Hotelling demand of retailer B (eq. 3.7, `a = b = 0`). -/
def demandB (t p_a p_b : ℝ) : ℝ := (1 : ℝ) / 2 + (p_a - p_b) / (2 * t)

/-- Probability the police succeed against retailer i: `q ^ (v_i / v_r)` (§3.4). -/
def catchRetail (q v_r v_i : ℝ) : ℝ := Real.rpow q (v_i / v_r)

/-- Probability the police succeed against wholesaler i: `q ^ (1 / v_ri)` (§3.7.1). -/
def catchWholesale (q v_ri : ℝ) : ℝ := Real.rpow q (1 / v_ri)

/-- Retailer A expected profit (eq. 3.13 / 3.15). -/
def retailProfitA (q s t v_r w_a p_a p_b v_a : ℝ) : ℝ :=
  (1 - catchRetail q v_r v_a) * (p_a - w_a) * demandA t p_a p_b
    - s * catchRetail q v_r v_a - v_a

/-- Retailer B expected profit (eq. 3.14 / 3.16). -/
def retailProfitB (q s t v_r w_b p_a p_b v_b : ℝ) : ℝ :=
  (1 - catchRetail q v_r v_b) * (p_b - w_b) * demandB t p_a p_b
    - s * catchRetail q v_r v_b - v_b

/-- Demand faced by wholesaler A at the retail price equilibrium (eq. 3.23 / 3.44). -/
def wholesaleDemandA (t w_a w_b : ℝ) : ℝ := (1 : ℝ) / 2 + (w_b - w_a) / (6 * t)

/-- Demand faced by wholesaler B at the retail price equilibrium (eq. 3.24 / 3.45). -/
def wholesaleDemandB (t w_a w_b : ℝ) : ℝ := (1 : ℝ) / 2 + (w_a - w_b) / (6 * t)

/-- Wholesaler A expected profit (eq. 3.42 / 3.44). -/
def wholesaleProfitA (q s t c v_ra w_a w_b : ℝ) : ℝ :=
  (1 - catchWholesale q v_ra) * (w_a - c) * wholesaleDemandA t w_a w_b
    - s * wholesaleDemandA t w_a w_b * catchWholesale q v_ra

/-- Wholesaler B expected profit (eq. 3.43 / 3.45, with the cost-term index `v_rb`
as in the first-order condition (3.47)). -/
def wholesaleProfitB (q s t c v_rb w_a w_b : ℝ) : ℝ :=
  (1 - catchWholesale q v_rb) * (w_b - c) * wholesaleDemandB t w_a w_b
    - s * wholesaleDemandB t w_a w_b * catchWholesale q v_rb

/-- Retailer A's objective as a function of its own violence, at fixed gross profit
`g = (p_a - w_a) D_a` (eq. 3.26). -/
def retailViolenceObjective (q s v_r g v : ℝ) : ℝ :=
  (1 - catchRetail q v_r v) * g - s * catchRetail q v_r v - v




end DrugMarket
end


