-- Prove2me | Definitions.Def_SupplyChainFactoring_Choice_Model
-- name    : SupplyChainFactoring_Choice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:23:03.012092+00:00
-- url     : https://prove2.me/theorems/a83cadc9-5a7d-4fb7-92fb-27e5b4214608
-- title:
--   Credit functions, coefficients $\Lambda_i$, effective costs $c_i$, profits, equilibrium, feasibility and adoption (§3–§5)
-- statement:
--   **Data.** A unit production cost $c$ and retail price $p$ with $0 < c < p$; a lead time $t_1 > 0$ and payment term $t_2 > 0$; the supplier's and the retailer's liquidity risks $\lambda_s, \lambda_r \ge 0$; a range of credit ratings $0 \le C_{\min} < C_{\max}$; a **default probability** $\rho$ with $\rho(C) \in [0,1]$ and $\rho$ strictly decreasing on $(C_{\min}, C_{\max})$; an **interest-rate premium** $\eta > 0$, (weakly) decreasing on $(C_{\min}, C_{\max})$. For the supplier's rating $C_s$ and the retailer's rating $C_r$ write $\rho_j = \rho(C_j)$, $\eta_j = \eta(C_j)$; $\tau \ge 0$ is the payment extension of reverse factoring.
--
--   **Schemes and coefficients.** The supplier finances through recourse factoring $\mathcal F$, non-recourse factoring $\mathcal N$ or reverse factoring $\mathcal R$, with
--
--   $$\Lambda_{\mathcal F} = (1-\rho_r) + (1-\rho_s) - e^{\eta_s t_2}, \qquad \Lambda_{\mathcal N} = e^{-\eta_r t_2}(1-\rho_r), \qquad \Lambda_{\mathcal R} = e^{-\eta_r (t_2+\tau)},$$
--
--   and effective unit production costs (Eqs. (8), (9), (12))
--
--   $$c_{\mathcal F} = \frac{c\,e^{(\eta_s+\lambda_s)t_1}}{(1-\rho_r)+(1-\rho_s)-e^{\eta_s t_2}},\qquad c_{\mathcal N} = \frac{c\,e^{(\eta_s+\lambda_s)t_1+\eta_r t_2}}{1-\rho_r},\qquad c_{\mathcal R}(\tau) = c\,e^{(\eta_s+\lambda_s)t_1+\eta_r(t_2+\tau)}.$$
--
--   **Profits.** At wholesale price $w$ and production quantity $q$ the supplier's and the retailer's expected profits are
--
--   $$\pi_i(q; w) = (1-\rho_s)\big(\Lambda_i e^{-\lambda_s t_1} w S(q) - c q e^{\eta_s t_1}\big), \qquad \Pi_i(w) = e^{-\lambda_s t_1}(1-\rho_r)\,\beta_i\,(p-w) S(q),$$
--
--   with $\beta_{\mathcal F} = \beta_{\mathcal N} = 1$ and $\beta_{\mathcal R} = 2 - e^{-\lambda_r \tau}$ (the retailer's liquidity benefit of the payment extension).
--
--   **Game.** The retailer (leader) sets $w \ge 0$; the supplier (follower) chooses $q \ge 0$. A **best response** to $w$ is a $q \ge 0$ maximizing $\pi_i(\cdot\,; w)$ over $[0,\infty)$. An **equilibrium** is a pair $(w^*, q^*)$ with $w^* \ge 0$, $q^*$ a best response to $w^*$, and $\Pi_i$ at $(w^*, q^*)$ at least $\Pi_i$ at every $(w, q)$ with $w \ge 0$ and $q$ a best response to $w$.
--
--   **Feasibility and adoption.** Scheme $i$ is **feasible** if some $w \ge 0$ together with a best response $q$ gives the retailer a strictly positive expected profit. Scheme $i$ is **adopted** from a set $A$ of available schemes if $i \in A$ is feasible and has an equilibrium whose supplier profit $\pi^*_i$ satisfies, against the equilibrium supplier profit $\pi^*_j$ of every other feasible $j \in A$: $\pi^*_i \ge \pi^*_j$ when $i$ ranks above $j$, and $\pi^*_i > \pi^*_j$ when $j$ ranks above $i$, for the tie order $\mathcal R \succ \mathcal N \succ \mathcal F$.
--
--   Finally, "$x$ is the unique value of $C$ in $(C_{\min}, C_{\max})$ that satisfies $E$" is the predicate `IsUniqueSolution`: $x \in (C_{\min}, C_{\max})$, $E(x)$ holds, and every $y \in (C_{\min}, C_{\max})$ with $E(y)$ equals $x$.
--
--   **Formalization Note** The paper never defines "feasible" or "adopted". Feasibility is read from p. 6076 ("the physical supply chain may become infeasible because of its financial constraints"): the game can operate with positive profit. It is not defined by the inequality $c_i < p$, which Propositions 2 and 3 prove. Adoption compares equilibrium **profits** (the supplier's preference, p. 6080), not the coefficients $\Lambda_i$; the tie order is the one forced by the paper's boundary cases ($C_s = \mathbb C_1$ goes to $\mathcal N$ in Proposition 4, $C_s = \mathbb C_3$ and $C_r = \mathbb C_2$ go to $\mathcal R$ in Proposition 5). The wholesale price is restricted to $w \ge 0$ (an addition: with $\Lambda_{\mathcal F} < 0$ and a negative $w$ the profit formula (7) would reward production). The profit functions (7), the p. 6079 display, (10) and the p. 6082 display are taken as the model; the finance derivations behind them are not formalized. The retailer's reverse-factoring profit uses the last line of the p. 6082 display (its middle line carries a stray factor $w$, a misprint). $\lambda_s$, $\lambda_r$ are `lamS`, `lamR`; $\Lambda_i$ is `coef`; $c_i$ is `effCost`.
-- source:
--   Kouvelis and Xu, A Supply Chain Theory of Factoring and Reverse Factoring, Management Science 67(10), 2021, pp. 6074–6075, §3.1–3.3; p. 6076 (feasibility); p. 6078, Eqs. (7)–(8); p. 6079, Eq. (9); p. 6080, Eq. (10); p. 6082, §5.1, Eq. (12)

import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- The exogenous data of the model (Kouvelis–Xu 2021, §3–§5): unit production cost `c`, retail
price `p`, lead time `t1`, payment term `t2`, the supplier's liquidity risk `lamS` (`λ_s`), the
retailer's liquidity risk `lamR` (`λ_r`), the range `(Cmin, Cmax)` of credit ratings, the default
probability `ρ` and the interest-rate premium `η` as functions of the credit rating. -/
structure Params where
  c : ℝ
  p : ℝ
  t1 : ℝ
  t2 : ℝ
  lamS : ℝ
  lamR : ℝ
  Cmin : ℝ
  Cmax : ℝ
  ρ : ℝ → ℝ
  η : ℝ → ℝ

/-- Standing assumptions of §3.1–§3.3 (pp. 6074–6076): `0 < c < p`, `t1, t2 > 0`, `λ_s, λ_r ≥ 0`,
`0 ≤ Cmin < Cmax`; on `(Cmin, Cmax)` the default probability `ρ` takes values in `[0, 1]` and is
strictly decreasing, and the premium `η` is positive and (weakly) decreasing. -/
structure Params.Valid (P : Params) : Prop where
  c_pos : 0 < P.c
  c_lt_p : P.c < P.p
  t1_pos : 0 < P.t1
  t2_pos : 0 < P.t2
  lamS_nonneg : 0 ≤ P.lamS
  lamR_nonneg : 0 ≤ P.lamR
  Cmin_nonneg : 0 ≤ P.Cmin
  Cmin_lt_Cmax : P.Cmin < P.Cmax
  ρ_mem : ∀ C ∈ Set.Ioo P.Cmin P.Cmax, P.ρ C ∈ Set.Icc (0 : ℝ) 1
  ρ_strictAnti : StrictAntiOn P.ρ (Set.Ioo P.Cmin P.Cmax)
  η_pos : ∀ C ∈ Set.Ioo P.Cmin P.Cmax, 0 < P.η C
  η_anti : AntitoneOn P.η (Set.Ioo P.Cmin P.Cmax)

/-- The three post-shipment financing schemes: recourse factoring `𝓕`, non-recourse factoring `𝓝`
and reverse factoring `𝓡`. -/
inductive Scheme
  | recourse
  | nonRecourse
  | reverse
  deriving DecidableEq

/-- Tie-breaking rank `𝓡 ≻ 𝓝 ≻ 𝓕`: when two schemes give the supplier the same equilibrium
profit, the higher-ranked one is adopted. -/
def Scheme.rank : Scheme → ℕ
  | .recourse => 0
  | .nonRecourse => 1
  | .reverse => 2

/-- `Λ_𝓕(Cs, Cr) = (1 − ρ_r) + (1 − ρ_s) − e^{η_s t2}` (Eq. (10), p. 6080). -/
noncomputable def coefF (P : Params) (Cs Cr : ℝ) : ℝ :=
  (1 - P.ρ Cr) + (1 - P.ρ Cs) - exp (P.η Cs * P.t2)

/-- `Λ_𝓝(Cr) = e^{−η_r t2}(1 − ρ_r)` (Eq. (10), p. 6080). -/
noncomputable def coefN (P : Params) (Cr : ℝ) : ℝ :=
  exp (-(P.η Cr * P.t2)) * (1 - P.ρ Cr)

/-- `Λ_𝓡 = e^{−η_r(t2 + τ)}` for the payment extension `τ` (p. 6082). -/
noncomputable def coefR (P : Params) (Cr τ : ℝ) : ℝ :=
  exp (-(P.η Cr * (P.t2 + τ)))

/-- The coefficient `Λ_i` of scheme `i` at supplier rating `Cs`, retailer rating `Cr` and payment
extension `τ` (`τ` only matters for reverse factoring). -/
noncomputable def coef (P : Params) : Scheme → ℝ → ℝ → ℝ → ℝ
  | .recourse, Cs, Cr, _ => coefF P Cs Cr
  | .nonRecourse, _, Cr, _ => coefN P Cr
  | .reverse, _, Cr, τ => coefR P Cr τ

/-- Effective unit production cost under recourse factoring,
`c_𝓕 = c e^{(η_s+λ_s)t1} / [(1 − ρ_r) + (1 − ρ_s) − e^{η_s t2}]` (Eq. (8), p. 6078). -/
noncomputable def cF (P : Params) (Cs Cr : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1) / ((1 - P.ρ Cr) + (1 - P.ρ Cs) - exp (P.η Cs * P.t2))

/-- Effective unit production cost under non-recourse factoring,
`c_𝓝 = c e^{(η_s+λ_s)t1 + η_r t2} / (1 − ρ_r)` (Eq. (9), p. 6079). -/
noncomputable def cN (P : Params) (Cs Cr : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1 + P.η Cr * P.t2) / (1 - P.ρ Cr)

/-- Effective unit production cost under reverse factoring with payment extension `τ`,
`c_𝓡(τ) = c e^{(η_s+λ_s)t1 + η_r(t2+τ)}` (Eq. (12), p. 6082). -/
noncomputable def cR (P : Params) (Cs Cr τ : ℝ) : ℝ :=
  P.c * exp ((P.η Cs + P.lamS) * P.t1 + P.η Cr * (P.t2 + τ))

/-- The effective unit production cost `c_i` of scheme `i`. -/
noncomputable def effCost (P : Params) : Scheme → ℝ → ℝ → ℝ → ℝ
  | .recourse, Cs, Cr, _ => cF P Cs Cr
  | .nonRecourse, Cs, Cr, _ => cN P Cs Cr
  | .reverse, Cs, Cr, τ => cR P Cs Cr τ

/-- The supplier's expected profit under scheme `i` at wholesale price `w` and quantity `q`,
`π_i(q; w) = (1 − ρ_s)(Λ_i e^{−λ_s t1} w S(q) − c q e^{η_s t1})` (Eq. (10), p. 6080; p. 6082 for
reverse factoring). -/
noncomputable def supplierProfit (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : ℝ :=
  (1 - P.ρ Cs) *
    (coef P i Cs Cr τ * exp (-(P.lamS * P.t1)) * w * S μ q - P.c * q * exp (P.η Cs * P.t1))

/-- The retailer's liquidity-benefit factor: `1` under factoring, `2 − e^{−λ_r τ}` under reverse
factoring (p. 6082). -/
noncomputable def retailerFactor (P : Params) : Scheme → ℝ → ℝ
  | .recourse, _ => 1
  | .nonRecourse, _ => 1
  | .reverse, τ => 2 - exp (-(P.lamR * τ))

/-- The retailer's expected profit under scheme `i` at wholesale price `w` when the supplier
produces `q`: `Π_𝓕 = Π_𝓝 = e^{−λ_s t1}(1 − ρ_r)(p − w)S(q)` (pp. 6078, 6079) and
`Π_𝓡 = e^{−λ_s t1}(1 − ρ_r)(2 − e^{−λ_r τ})(p − w)S(q)` (p. 6082, last line of the display). -/
noncomputable def retailerProfit (P : Params) (μ : Measure ℝ) (i : Scheme) (Cr τ w q : ℝ) : ℝ :=
  exp (-(P.lamS * P.t1)) * (1 - P.ρ Cr) * retailerFactor P i τ * (P.p - w) * S μ q

/-- `q` is a best response of the supplier (the follower) to the wholesale price `w`: `q ≥ 0`
maximizes `π_i(·; w)` over all quantities `q' ≥ 0`. -/
def IsBestResponse (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → supplierProfit P μ i Cs Cr τ w q' ≤ supplierProfit P μ i Cs Cr τ w q

/-- Scheme `i` is feasible: some nonnegative wholesale price `w`, together with a best response `q`
of the supplier, gives the retailer a strictly positive expected profit (the physical supply chain
can operate under the scheme, p. 6076). -/
def Feasible (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ : ℝ) : Prop :=
  ∃ w q : ℝ, 0 ≤ w ∧ IsBestResponse P μ i Cs Cr τ w q ∧ 0 < retailerProfit P μ i Cr τ w q

/-- `(w, q)` is a Stackelberg equilibrium of the pull game under scheme `i`: `w ≥ 0`, `q` is a
best response to `w`, and no nonnegative wholesale price `w'`, with any best response `q'` to it,
gives the retailer (the leader) a larger expected profit. -/
def IsEquilibrium (P : Params) (μ : Measure ℝ) (i : Scheme) (Cs Cr τ w q : ℝ) : Prop :=
  0 ≤ w ∧ IsBestResponse P μ i Cs Cr τ w q ∧
    ∀ w' q' : ℝ, 0 ≤ w' → IsBestResponse P μ i Cs Cr τ w' q' →
      retailerProfit P μ i Cr τ w' q' ≤ retailerProfit P μ i Cr τ w q

/-- Scheme `i` is adopted by the supplier from the set `A` of available schemes: `i ∈ A` is
feasible and has an equilibrium whose supplier profit is at least (if `i` is ranked higher) or
strictly above (if `i` is ranked lower) the supplier's equilibrium profit under every other
feasible scheme `j ∈ A`. Ties are resolved by `Scheme.rank` (`𝓡 ≻ 𝓝 ≻ 𝓕`). -/
def Adopted (P : Params) (μ : Measure ℝ) (A : Set Scheme) (i : Scheme) (Cs Cr τ : ℝ) : Prop :=
  i ∈ A ∧ Feasible P μ i Cs Cr τ ∧
    ∃ w q : ℝ, IsEquilibrium P μ i Cs Cr τ w q ∧
      ∀ j ∈ A, j ≠ i → Feasible P μ j Cs Cr τ →
        ∀ w' q' : ℝ, IsEquilibrium P μ j Cs Cr τ w' q' →
          (j.rank < i.rank →
              supplierProfit P μ j Cs Cr τ w' q' ≤ supplierProfit P μ i Cs Cr τ w q) ∧
          (i.rank < j.rank →
              supplierProfit P μ j Cs Cr τ w' q' < supplierProfit P μ i Cs Cr τ w q)

/-- `x` is the unique value in `(a, b)` satisfying the property `E`: the paper's phrase
"the unique value of `C` that satisfies …". -/
def IsUniqueSolution (a b : ℝ) (E : ℝ → Prop) (x : ℝ) : Prop :=
  x ∈ Set.Ioo a b ∧ E x ∧ ∀ y ∈ Set.Ioo a b, E y → y = x

end SupplyChainFactoring.Choice


