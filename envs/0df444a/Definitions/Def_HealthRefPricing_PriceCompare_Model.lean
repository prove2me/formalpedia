-- Prove2me | Definitions.Def_HealthRefPricing_PriceCompare_Model
-- name    : HealthRefPricing_PriceCompare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:05.481474+00:00
-- url     : https://prove2.me/theorems/9e3d9e41-0a5c-45ae-9d7a-c38e2b7f8886
-- title:
--   §3, §4.2–§4.3, pp. 7–13 — two-provider MNL price game under variable payment and reference pricing, Assumptions 1–2
-- statement:
--   An insurer's network contains two profit-maximizing providers, $j = 1, 2$, who offer the same procedure to a population of $m$ patients. Provider $j$ has a non-price attribute $a_j$, with $a_1 \le a_2$; all patients have the same price sensitivity $\gamma$, and the alternative treatment has utility $u_0$. If the patient's out-of-pocket cost at provider $j$ is $o_j$, provider $j$'s market share is the multinomial logit share
--
--   $$S_j(P) = \frac{e^{a_j - \gamma o_j}}{e^{u_0} + \sum_{k=1}^{2} e^{a_k - \gamma o_k}}, \qquad j = 1,2,$$
--
--   where $P = (p_1, p_2)$ is the price vector. Both providers have treatment cost $c$, and provider $j$'s profit is $V_j(P) = m(p_j - c)S_j(P)$.
--
--   Two payment systems determine the out-of-pocket costs:
--
--   1. **Variable payment (VP)** with cost share $\lambda \in (0,1]$: $o_j = \lambda p_j$.
--   2. **Reference pricing (RP)** with reference price $p^*$ and co-payment $\tilde c$: $o_j = \tilde c + (p_j - p^*)^+ = \tilde c + \max\{0, p_j - p^*\}$. Provider $j$ is **value-based** if $p_j \le p^*$ and non-value-based otherwise.
--
--   Under each system the providers play a simultaneous price game, and an **equilibrium** is a pure Nash equilibrium: a price vector at which no provider can raise its own profit by changing only its own price. The standing assumptions are $m > 0$, $\gamma > 0$, $c \ge 0$, $a_1 \le a_2$ and $\tilde c < c$.
--
--   For a rival price $y$, a **best response** of provider $j$ is a price maximizing $j$'s profit given $y$. **Assumption 1** (at cost share $\lambda$) says that the limit $\bar S^{VP}_j$, as the rival price tends to $+\infty$, of provider $j$'s market share at its VP best response satisfies $\bar S^{VP}_j \le 50\%$ for $j = 1,2$; **Assumption 2** is the same condition $\bar S^{RP}_j \le 50\%$ under reference pricing.
--
--   These objects are the whole model behind the paper's equilibrium characterizations (Theorems 1 and 2) and its comparison of the two payment systems (Proposition 5).
--
--   **Formalization Note** Providers are indexed by `Fin 2`: index `0` is the paper's provider 1 and index `1` is provider 2. The cost share is named `lam`, the co-payment `ct` and the reference price `ps`. Prices range over all of $\mathbb R$ rather than the paper's $p_j > c$; this does not change the equilibria, since an equilibrium price earns positive profit and any price $p_j \le c$ earns non-positive profit. Equilibrium is the published generic relation `CarbonDoubleCount.Planner.IsPureNash` with every feasible set equal to $\mathbb R$. The paper never states $\gamma > 0$, $m > 0$, or $c \ge 0$ as inequalities; they are implicit in price sensitivity, population size, and treatment cost. The cost bound excludes a negative-cost counterexample to Lemma 2(a). All three are part of `Standing`. "Value-based" is read as $p_j \le p^*$: §4.3 says "below the reference price", but Proposition 2 places value-based providers at $p^*$. Assumptions 1 and 2 are encoded as follows: for each provider a best response to every rival price exists, and along every best-response selection the share converges, as the rival price tends to $+\infty$, to a limit at most $1/2$. The existence clause prevents the assumption from holding vacuously; in this model best responses are unique, so "every selection" agrees with the paper's "the" best response.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), pp. 7–13 (PDF 8–14), §3 eqs. (1), (2), (4), §4.2, §4.3, Assumptions 1–2

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace HealthRefPricing.PriceCompare

/-- The data of the two-provider model of §3 and §4.2–§4.3. Index `0` of `Fin 2` is the paper's
provider 1 and index `1` is provider 2. -/
structure Params where
  /-- population size `m` -/
  m : ℝ
  /-- common price sensitivity `γ` -/
  γ : ℝ
  /-- common treatment cost `c` -/
  c : ℝ
  /-- utility `u₀` of the alternative treatment -/
  u0 : ℝ
  /-- non-price attributes: `a 0 = a₁`, `a 1 = a₂` -/
  a : Fin 2 → ℝ
  /-- co-payment `c̃` under reference pricing -/
  ct : ℝ
  /-- reference price `p*` -/
  ps : ℝ

/-- Standing assumptions: `m > 0`, `γ > 0`, and `c ≥ 0` (implicit in the paper's
population, sensitivity, and treatment-cost interpretation), `a₁ ≤ a₂` (p. 8), and
`c̃ < c` (p. 13). The cost bound excludes a negative-cost counterexample to Lemma 2(a). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.m ∧ 0 < P.γ ∧ 0 ≤ P.c ∧ P.a 0 ≤ P.a 1 ∧ P.ct < P.c

/-- MNL market share (2) of provider `j` when the out-of-pocket costs are `o`:
`S_j = e^{a_j - γ o_j} / (e^{u₀} + Σ_k e^{a_k - γ o_k})`. -/
noncomputable def share (P : Params) (o : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  Real.exp (P.a j - P.γ * o j) / (Real.exp P.u0 + ∑ k, Real.exp (P.a k - P.γ * o k))

/-- Out-of-pocket costs under variable payment with cost share `lam`: `o_k = λ p_k`. -/
def oopVP (lam : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ := fun k => lam * p k

/-- Out-of-pocket costs under reference pricing: `o_k = c̃ + max{0, p_k - p*}`. -/
noncomputable def oopRP (P : Params) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun k => P.ct + max 0 (p k - P.ps)

/-- Provider `j`'s profit (4) under variable payment: `m (p_j - c) S^{VP}_j(P)`. -/
noncomputable def profitVP (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  P.m * (p j - P.c) * share P (oopVP lam p) j

/-- Provider `j`'s profit (4) under reference pricing: `m (p_j - c) S^{RP}_j(P)`. -/
noncomputable def profitRP (P : Params) (p : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  P.m * (p j - P.c) * share P (oopRP P p) j

/-- A pure Nash equilibrium of the simultaneous price game under variable payment
(prices range over all of `ℝ`). -/
def IsEqVP (P : Params) (lam : ℝ) (p : Fin 2 → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun _ => Set.univ) (fun j q => profitVP P lam q j) p

/-- A pure Nash equilibrium of the simultaneous price game under reference pricing
(prices range over all of `ℝ`). -/
def IsEqRP (P : Params) (p : Fin 2 → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun _ => Set.univ) (fun j q => profitRP P q j) p

/-- Provider `j` is value-based at the price profile `p`: it prices at or below `p*`. -/
def IsValueBased (P : Params) (p : Fin 2 → ℝ) (j : Fin 2) : Prop :=
  p j ≤ P.ps

/-- The price profile in which provider `j` charges `x` and the other provider charges `y`. -/
def vs (j : Fin 2) (x y : ℝ) : Fin 2 → ℝ :=
  Function.update (fun _ => y) j x

/-- `x` is a best response of provider `j` under variable payment to the rival price `y`. -/
def IsBestRespVP (P : Params) (lam : ℝ) (j : Fin 2) (y x : ℝ) : Prop :=
  ∀ x', profitVP P lam (vs j x' y) j ≤ profitVP P lam (vs j x y) j

/-- `x` is a best response of provider `j` under reference pricing to the rival price `y`. -/
def IsBestRespRP (P : Params) (j : Fin 2) (y x : ℝ) : Prop :=
  ∀ x', profitRP P (vs j x' y) j ≤ profitRP P (vs j x y) j

/-- Assumption 1 (p. 12) at cost share `lam`: for each provider a best response to every rival
price exists, and along every best-response selection the provider's market share converges, as
the rival price tends to `+∞`, to a limit `S̄^{VP}_j ≤ 1/2`. -/
def Assumption1 (P : Params) (lam : ℝ) : Prop :=
  ∀ j : Fin 2, (∃ br : ℝ → ℝ, ∀ y, IsBestRespVP P lam j y (br y)) ∧
    ∀ br : ℝ → ℝ, (∀ y, IsBestRespVP P lam j y (br y)) →
      ∃ L : ℝ, L ≤ 1 / 2 ∧
        Filter.Tendsto (fun y => share P (oopVP lam (vs j (br y) y)) j) Filter.atTop (nhds L)

/-- Assumption 2 (p. 13): the reference-pricing analogue of Assumption 1, `S̄^{RP}_j ≤ 1/2`. -/
def Assumption2 (P : Params) : Prop :=
  ∀ j : Fin 2, (∃ br : ℝ → ℝ, ∀ y, IsBestRespRP P j y (br y)) ∧
    ∀ br : ℝ → ℝ, (∀ y, IsBestRespRP P j y (br y)) →
      ∃ L : ℝ, L ≤ 1 / 2 ∧
        Filter.Tendsto (fun y => share P (oopRP P (vs j (br y) y)) j) Filter.atTop (nhds L)

end HealthRefPricing.PriceCompare


