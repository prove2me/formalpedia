-- Prove2me | Definitions.Def_RevShareCoord_Wholesale_Model
-- name    : RevShareCoord_Wholesale_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:41:20.579145+00:00
-- url     : https://prove2.me/theorems/90a8b7a6-3053-46bd-be72-94594626361f
-- title:
--   Sec. 1 and Sec. 4.1.1 — the single-retailer model, profits under an induced wholesale price, efficiency, profit share and the α-family
-- statement:
--   This file fixes the single-retailer model of Cachon and Lariviere (Sec. 1) as it is used in their analysis of the wholesale-price contract (Sec. 4.1.1), together with the profit functions, the efficiency and the profit share of that contract, and the parametric family of revenue functions used in their example.
--
--   **The model.** A supplier sells to one retailer. The retailer's expected revenue from $q$ units is $R(q)$, and the supplier's unit production cost is $c$. The standing assumptions are:
--
--   1. $c > 0$;
--   2. $R(0) = 0$ (revenue from zero units is zero);
--   3. $R$ is strictly concave on $[0, \infty)$;
--   4. $R$ is differentiable on $[0,\infty)$ with derivative $R'$ (one-sided at $0$);
--   5. $R'$ is differentiable on $(0,\infty)$ with derivative $R''$;
--   6. the product is viable, $R'(0) > c$;
--   7. a finite quantity is optimal, $R'(\infty) < c$: there is $Q \ge 0$ with $R'(Q) < c$;
--   8. the supplier's profit is unimodal: $q \mapsto R'(q) + qR''(q)$ is decreasing on $(0,\infty)$.
--
--   **Profits.** Under a wholesale-price contract with price $w$, the retailer who orders $q$ earns $R(q) - wq$. The wholesale price under which the retailer orders $q$ is $w(q) = R'(q)$. Writing everything as a function of the induced quantity $q$:
--
--   $$
--   \Pi(q) = R(q) - qc, \qquad \pi_s(q) = q\,(w(q) - c) = q\,(R'(q) - c), \qquad \pi_r(q) = R(q) - w(q)\,q = R(q) - qR'(q).
--   $$
--
--   Here $\Pi$ is the total supply chain profit, $\pi_s$ the supplier's profit and $\pi_r$ the retailer's profit. For quantities $q^*$ (the supplier's optimal quantity to induce) and $q_I$ (the integrated channel's optimal quantity), the **efficiency** of the wholesale-price contract and the supplier's **profit share** are
--
--   $$
--   \frac{\pi_s(q^*) + \pi_r(q^*)}{\Pi(q_I)} \qquad\text{and}\qquad \frac{\pi_s(q^*)}{\Pi(q^*)} .
--   $$
--
--   **The α-family.** For $\alpha > 0$ the revenue function $R(q) = qP(q) = q - q^{\alpha+1}/(\alpha+1)$ comes from the deterministic inverse demand curve $P(q) = 1 - q^\alpha/(\alpha+1)$; its marginal revenue is $R'(q) = 1 - q^\alpha$. The *α-family efficiency* with unit cost $c$ is the efficiency ratio above, computed from this $R$ and its derivative at $q^* = ((1-c)/(1+\alpha))^{1/\alpha}$ and $q_I = (1-c)^{1/\alpha}$.
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** The profit functions take the revenue function and the marginal-revenue function as separate arguments so that they serve both the general `Model` (where `R'` is a field, linked to `R` by a one-sided derivative hypothesis) and the α-family (where `R'` is `deriv (alphaRevenue α)`, so it cannot drift from $R$). Assumption 2, $R(0)=0$, is not written in the paper; it is implicit in the area reading of the retailer's profit in Figure 2 and in the α-family, and without it the profit-share comparison with $2/3$ fails. Assumptions 5 and 8 are those of Sec. 4.1.1 (the second derivative appears in Eq. (10); unimodality is assumed "for tractability"). "Decreasing" is read weakly (`AntitoneOn`). Efficiency and profit share are real divisions, which Lean sets to $0$ when the denominator is $0$; under the model both denominators are positive at the optimal quantities. In the α-family, $q^{\alpha+1}$ is the real power `rpow`; only its values on $[0,1]$ matter.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 5 (PDF 6), Section 1; p. 6 (PDF 7), Section 2.1; pp. 16-18 (PDF 17-19), Section 4.1.1, Eqs. (9)-(10), efficiency and profit-share displays, and the example R'(q) = 1 - q^α

import Mathlib

namespace RevShareCoord.Wholesale

/-! ### Profits under a wholesale-price contract that induces the order `q` (Sec. 4.1.1, p. 16)

The functions below take a revenue function `R` and a marginal revenue function `R'`
(its derivative) as data, so that they apply both to the general model `Model` and to the
`α`-family of p. 18, where `R'` is `deriv (alphaRevenue α)`. -/

/-- Total supply chain profit `Π(q) = R(q) − qc` (Sec. 2.1, p. 6). -/
def chainProfit (R : ℝ → ℝ) (c q : ℝ) : ℝ := R q - q * c

/-- The wholesale price `w(q) = R'(q)` under which the retailer orders `q`
(Sec. 4.1.1, p. 16, from Eq. (9)). -/
def inducingPrice (R' : ℝ → ℝ) (q : ℝ) : ℝ := R' q

/-- The supplier's profit when she induces the order `q`:
`π_s(q) = q (w(q) − c) = q (R'(q) − c)` (Sec. 4.1.1, p. 16). -/
def supplierProfit (R' : ℝ → ℝ) (c q : ℝ) : ℝ := q * (inducingPrice R' q - c)

/-- The retailer's profit when the supplier induces the order `q`:
`π_r(q) = R(q) − w(q) q = R(q) − q R'(q)` (Sec. 4.1.1, p. 17). -/
def retailerProfit (R R' : ℝ → ℝ) (q : ℝ) : ℝ := R q - inducingPrice R' q * q

/-- The efficiency of the wholesale-price contract, `(π_s(q*) + π_r(q*)) / Π(q_I)`
(Sec. 4.1.1, p. 17), evaluated at the induced quantity `qs` and the integrated-channel
quantity `qI`. -/
noncomputable def efficiency (R R' : ℝ → ℝ) (c qs qI : ℝ) : ℝ :=
  (supplierProfit R' c qs + retailerProfit R R' qs) / chainProfit R c qI

/-- The supplier's profit share `π_s(q*) / Π(q*)` (Sec. 4.1.1, p. 17), evaluated at the
induced quantity `qs`. -/
noncomputable def profitShare (R R' : ℝ → ℝ) (c qs : ℝ) : ℝ :=
  supplierProfit R' c qs / chainProfit R c qs

/-- The single-retailer model of Sec. 1 (p. 5) as used in Sec. 4.1.1 (p. 16).
`R q` is the retailer's expected revenue from `q` units, `R'` its derivative on `q ≥ 0`
(one-sided at `0`), `R''` the derivative of `R'` on `q > 0`, and `c` the supplier's unit
production cost. -/
structure Model where
  /-- Expected revenue `R(q)` as a function of the order quantity. -/
  R : ℝ → ℝ
  /-- Marginal revenue `R'(q)` for `q ≥ 0`. -/
  R' : ℝ → ℝ
  /-- Second derivative `R''(q)` for `q > 0`. -/
  R'' : ℝ → ℝ
  /-- Supplier's unit production cost `c`. -/
  c : ℝ
  /-- `c > 0` (Sec. 1). -/
  c_pos : 0 < c
  /-- Revenue from zero units is zero (implicit in the area reading of Fig. 2). -/
  R_zero : R 0 = 0
  /-- `R` is strictly concave for `q ≥ 0` (Sec. 1). -/
  strictConcave : StrictConcaveOn ℝ (Set.Ici 0) R
  /-- `R` is differentiable for `q ≥ 0`, with derivative `R'` (one-sided at `0`) (Sec. 1). -/
  hasDeriv : ∀ q : ℝ, 0 ≤ q → HasDerivWithinAt R (R' q) (Set.Ici 0) q
  /-- `R'` is differentiable for `q > 0`, with derivative `R''` (used in Eq. (10)). -/
  hasDeriv2 : ∀ q : ℝ, 0 < q → HasDerivAt R' (R'' q) q
  /-- The product is viable: `R'(0) > c` (Sec. 1). -/
  viable : c < R' 0
  /-- A finite quantity is optimal, `R'(∞) < c`: marginal revenue eventually falls below `c`
  (Sec. 1). -/
  finite_optimal : ∃ Q : ℝ, 0 ≤ Q ∧ R' Q < c
  /-- The supplier's profit is unimodal: `R'(q) + q R''(q)` is decreasing in `q`
  (Sec. 4.1.1, p. 16, "For tractability, we assume that condition holds"). -/
  unimodal : AntitoneOn (fun q => R' q + q * R'' q) (Set.Ioi 0)

/-! ### The `α`-family (Sec. 4.1.1, p. 18) -/

/-- The revenue function of the `α`-family, `R(q) = q P(q) = q − q^{α+1}/(α+1)`, generated by
the deterministic inverse demand curve `P(q) = 1 − q^α/(α+1)`; its marginal revenue is
`R'(q) = 1 − q^α`. The paper uses it for `α > 0` and `q ∈ [0, 1]`. -/
noncomputable def alphaRevenue (α q : ℝ) : ℝ := q - q ^ (α + 1) / (α + 1)

/-- The efficiency of the supplier's optimal wholesale-price contract in the `α`-family with
unit cost `c`: the profit ratio `(π_s(q*) + π_r(q*)) / Π(q_I)` computed from
`R = alphaRevenue α` and `R' = deriv R`, at `q* = ((1−c)/(1+α))^{1/α}` and
`q_I = (1−c)^{1/α}` (p. 18). -/
noncomputable def alphaEfficiency (α c : ℝ) : ℝ :=
  efficiency (alphaRevenue α) (deriv (alphaRevenue α)) c
    (((1 - c) / (1 + α)) ^ (1 / α)) ((1 - c) ^ (1 / α))

end RevShareCoord.Wholesale


