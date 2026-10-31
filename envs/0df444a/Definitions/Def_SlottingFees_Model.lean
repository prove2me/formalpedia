-- Prove2me | Definitions.Def_SlottingFees_Model
-- name    : SlottingFees_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:54.284424+00:00
-- url     : https://prove2.me/theorems/b53c0402-82f9-47e5-bcb0-f94ad8b51ec0
-- title:
--   Slotting-fee channel: parameters, vertical-differentiation demand, profits (1)–(3)
-- statement:
--   One retailer sells the products of two manufacturers. Product $l\in\{1,2\}$ has quality $q_l$ and unit production cost $c_l$; the retailer pays an operational cost $K$ for every product it carries. The parameter vector is $\omega=(q_1,q_2,c_1,c_2,K)$; the standing assumptions are $q_1>q_2$ and $q_l>c_l\ge 0$.
--
--   **Demand.** A consumer of type $\theta$, uniform on $[0,1]$, derives utility $u_l(\theta)=\theta q_l-p_l$ from product $l$ at retail price $p_l$. Under an assortment $A\subseteq\{1,2\}$, product $i\in A$ sells to the types with $u_i(\theta)\ge 0$ and $u_i(\theta)\ge u_j(\theta)$ for every $j\in A$:
--   $$
--   z_i(A,p)=\Pr\bigl(\theta\in[0,1]:\ u_i(\theta)\ge 0,\ u_i(\theta)\ge u_j(\theta)\ \forall j\in A\bigr),
--   $$
--   and $z_i=0$ for $i\notin A$ (the market size is one).
--
--   **Profits.** With wholesale prices $w_i$ and a slotting fee $S$ per carried product, manufacturer $i$ earns
--   $$
--   \Pi_i(A)=\begin{cases}(w_i-c_i)z_i(A)-S & i\in A,\\ 0&\text{otherwise,}\end{cases}\qquad(2)
--   $$
--   and the retailer earns
--   $$
--   \Pi_r(A)=\sum_{i\in A}(p_i-w_i)z_i(A)+S|A|-K|A|.\qquad(3)
--   $$
--
--   These are the primitives of the three-stage game on which every result of the mission is stated.
--
--   **Formalization Note** Products 1 and 2 are the indices $0$ and $1$ of `Fin 2`. $\Pr$ is the Lebesgue measure of the set of types in $[0,1]$, as a real number; types indifferent between the two products are counted for both, a null set when $q_1\neq q_2$.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, §3, (1)–(3), pp.7–8; Ω and the assumptions q_l > c_l ≥ 0, p.16

import Mathlib

open MeasureTheory

namespace SlottingFees

/-- The parameters `ω = (q₁, q₂, c₁, c₂, K)` of the slotting-fee model.
Alan, Kurtuluş, Nakkas, *Retail Category Management with Slotting Fees*, Manufacturing & Service
Operations Management (2024), doi:10.1287/msom.2022.0143, §3, pp.7–8, and §4.3, p.16.

* `q l` is the quality of product `l`, `c l` its unit production cost;
* `K` is the retailer's operational cost per product carried.

**Formalization Note** Products are indexed by `Fin 2`: the paper's product 1 (the high-quality
product of manufacturer 1) is `0`, product 2 is `1`. The fields are bare reals; the paper's
standing assumptions are the separate predicates `Params.Standing` and `Omega`. -/
structure Params where
  q : Fin 2 → ℝ
  c : Fin 2 → ℝ
  K : ℝ

/-- The standing assumptions of §3–§4.2 (pp.7, 16): `q₁ > q₂` (p.7, "we assume without loss of
generality that q₁ > q₂") and `q_l > c_l ≥ 0` for both products (p.16). -/
def Params.Standing (ω : Params) : Prop :=
  ω.q 1 < ω.q 0 ∧ ∀ l : Fin 2, 0 ≤ ω.c l ∧ ω.c l < ω.q l

/-- The other product: `other 0 = 1`, `other 1 = 0` (the paper's `j ≠ i`). -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- Demand (unit sales) of product `i` under assortment `A` and retail prices `p`, §3, p.7 and (1).
A consumer of type `θ ~ U[0,1]` has utility `u_l(θ) = θ q_l − p_l` (1) and buys product `i ∈ A`
when `u_i(θ) ≥ 0` and `u_i(θ) ≥ u_j(θ)` for every `j ∈ A`; the market size is one. So
`z_i(A, p) = Pr(θ ∈ [0,1] : u_i(θ) ≥ 0, u_i(θ) ≥ u_j(θ) ∀ j ∈ A)` for `i ∈ A`, and `z_i = 0`
for `i ∉ A`.

**Formalization Note** `Pr` is Lebesgue measure of the set of types in `[0,1]`, as a real number.
Ties `u_i(θ) = u_j(θ)` are counted for both products, as in the paper's `z₁`, `z₂` (p.7); they
form a null set whenever `q₁ ≠ q₂`. The prices of products outside `A` are ignored. -/
noncomputable def demand (ω : Params) (A : Finset (Fin 2)) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if i ∈ A then
    (volume {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ θ * ω.q i - p i ∧
      ∀ j ∈ A, θ * ω.q j - p j ≤ θ * ω.q i - p i}).toReal
  else 0

/-- The retailer's gross profit `Σ_{i ∈ A} (p_i − w_i) z_i(A)`, the first term of (3), p.8. -/
noncomputable def grossProfit (ω : Params) (A : Finset (Fin 2)) (w p : Fin 2 → ℝ) : ℝ :=
  ∑ i ∈ A, (p i - w i) * demand ω A p i

/-- The retailer's profit (3), p.8:
`Π_r(A) = Σ_{i ∈ A} (p_i − w_i) z_i(A) + S|A| − K|A|`. -/
noncomputable def retailerProfit (ω : Params) (A : Finset (Fin 2)) (w p : Fin 2 → ℝ) (S : ℝ) :
    ℝ :=
  grossProfit ω A w p + S * (A.card : ℝ) - ω.K * (A.card : ℝ)

/-- Manufacturer `i`'s gross profit `(w_i − c_i) z_i(A)` (p.8, after (2)). -/
noncomputable def mfrGross (ω : Params) (A : Finset (Fin 2)) (w p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (w i - ω.c i) * demand ω A p i

/-- Manufacturer `i`'s profit (2), p.8: `Π_i(A) = (w_i − c_i) z_i(A) − S` if `i ∈ A`, else `0`. -/
noncomputable def mfrProfit (ω : Params) (A : Finset (Fin 2)) (w p : Fin 2 → ℝ) (S : ℝ)
    (i : Fin 2) : ℝ :=
  if i ∈ A then mfrGross ω A w p i - S else 0

end SlottingFees


