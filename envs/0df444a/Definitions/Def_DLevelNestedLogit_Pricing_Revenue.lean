-- Prove2me | Definitions.Def_DLevelNestedLogit_Pricing_Revenue
-- name    : DLevelNestedLogit_Pricing_Revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:29:57.592899+00:00
-- url     : https://prove2.me/theorems/9df6b504-2118-47fe-80b1-ae12a4a8b7f1
-- title:
--   Preference weights V_j(p), expected revenues R_j(p) and R_root(p), choice probabilities θ_l(p) and the scalars u_j(p) of the d-level nested logit price model
-- statement:
--   Fix a $d$-level product tree with parameters $\eta,\alpha_0,\alpha,\beta$ and a price vector $\mathbf p=(p_1,\dots,p_n)$; the price of the no-purchase option is fixed at $p_0=0$.
--
--   1. **Preference weights.** For a product leaf $l$, $V_l(\mathbf p)=e^{\alpha_l-\beta_lp_l}$; for the no-purchase leaf, $V_0(\mathbf p)=e^{\alpha_0}$; for a nonleaf node $j$,
--   $$
--   V_j(\mathbf p)=\Big(\sum_{k\in\mathrm{Children}(j)}V_k(\mathbf p)\Big)^{\eta_j}.
--   $$
--   2. **Expected revenues.** For a product leaf, $R_l(\mathbf p)=p_l$; for the no-purchase leaf, $R_0(\mathbf p)=0$; for a nonleaf node $j$,
--   $$
--   R_j(\mathbf p)=\frac{\sum_{k\in\mathrm{Children}(j)}V_k(\mathbf p)R_k(\mathbf p)}{\sum_{k\in\mathrm{Children}(j)}V_k(\mathbf p)} .
--   $$
--   The **expected revenue** of the price vector is $R_{\mathrm{root}}(\mathbf p)$.
--   3. **Choice probabilities.** Writing $\mathrm{An}(l,h)$ for the ancestor of product $l$ in level $h$ (so $\mathrm{An}(l,d)=l$, $\mathrm{An}(l,0)=\mathrm{root}$) and $\mathrm{Sibling}(j)=\mathrm{Children}(\mathrm{Parent}(j))$,
--   $$
--   \theta_l(\mathbf p)=\prod_{h=1}^{d}\frac{V_{\mathrm{An}(l,h)}(\mathbf p)}{\sum_{k\in\mathrm{Sibling}(\mathrm{An}(l,h))}V_k(\mathbf p)} ,
--   $$
--   the probability that a customer who walks down the tree, moving from a node to a child with probability proportional to its weight, chooses product $l$.
--   4. **The scalars $u$.** At the nonleaf nodes, top-down: $u_{\mathrm{root}}(\mathbf p)=R_{\mathrm{root}}(\mathbf p)$ and $u_j(\mathbf p)=\eta_ju_{\mathrm{Parent}(j)}(\mathbf p)+(1-\eta_j)R_j(\mathbf p)$.
--
--   These are the objects in which the gradient of the expected revenue (Lemma 7.1) and the stationarity condition (Corollary 7.2) are expressed.
--
--   **Formalization Note** `weight`, `revenue` and `expectedRevenue` are defined for every $\mathbf p\in\mathbb R^n$ by the same formulas (the paper restricts to $\mathbb R^n_+$); powers are `Real.rpow` and division is Lean's (`x / 0 = 0`), which never matters under the standing assumptions because every nonleaf node has a child and all leaf weights are positive. `ancestor T l h` is the node reached from leaf $l$ by $d-h$ parent steps. The scalars $u_j$ are defined only at nonleaf nodes, the only place Lemma 7.1 uses them; `root` uses the special value $R_{\mathrm{root}}$ directly.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 335, §7 (V_j, R_j, R_root, θ_l) and §7.1 (u_j)

import Mathlib
import Definitions.Def_DLevelNestedLogit_Pricing_Model

namespace DLevelNestedLogit.Pricing

variable {n d : ℕ} {T : DLevelTree n d}

/-- The preference weight `V_c(p)` of a node `c` under the price vector `p` (p. 335):
`V_l(p) = e^{α_l − β_l p_l}` at a product leaf `l`, `V_0(p) = e^{α_0}` at the no-purchase leaf
(whose price is fixed at `p_0 = 0`), and `V_j(p) = (∑_{k ∈ Children(j)} V_k(p))^{η_j}` at a
nonleaf node `j` (`Real.rpow`). -/
noncomputable def weight (P : Params T) (p : Fin n → ℝ) : T.Node → ℝ
  | Sum.inl none => Real.exp P.α₀
  | Sum.inl (some l) => Real.exp (P.α l - P.β l * p l)
  | Sum.inr j => (∑ c ∈ (T.children j).attach, weight P p c.1) ^ P.η j
termination_by c => T.rank c
decreasing_by exact T.rank_lt_of_mem_children c.2

/-- The expected revenue `R_c(p)` from a customer at node `c` (p. 335): `R_l(p) = p_l` at a
product leaf, `R_0(p) = p_0 = 0` at the no-purchase leaf, and at a nonleaf node `j`
`R_j(p) = ∑_{k ∈ Children(j)} V_k(p) R_k(p) / ∑_{k ∈ Children(j)} V_k(p)`. -/
noncomputable def revenue (P : Params T) (p : Fin n → ℝ) : T.Node → ℝ
  | Sum.inl none => 0
  | Sum.inl (some l) => p l
  | Sum.inr j =>
      (∑ c ∈ (T.children j).attach, weight P p c.1 * revenue P p c.1) /
        (∑ c ∈ T.children j, weight P p c)
termination_by c => T.rank c
decreasing_by exact T.rank_lt_of_mem_children c.2

/-- The expected revenue `R_root(p)` associated with the price vector `p` (p. 335). -/
noncomputable def expectedRevenue (P : Params T) (p : Fin n → ℝ) : ℝ :=
  revenue P p (Sum.inr T.root)

/-- `An(l, h)`, the ancestor of the product leaf `l` in level `h` (p. 335): obtained from the
leaf by `d - h` steps to the parent, so `An(l, d) = l` and `An(l, 0) = root`. -/
def ancestor (T : DLevelTree n d) (l : Fin n) (h : ℕ) : T.Node :=
  (fun c : T.Node => (Sum.inr (T.parent c) : T.Node))^[d - h] (T.productNode l)

/-- `θ_l(p)`, the probability that a customer chooses product `l` under the price vector `p`
(p. 335): `θ_l(p) = ∏_{h=1}^{d} V_{An(l,h)}(p) / ∑_{k ∈ Sibling(An(l,h))} V_k(p)`, where
`Sibling(j) = Children(Parent(j))`. -/
noncomputable def choiceProb (P : Params T) (p : Fin n → ℝ) (l : Fin n) : ℝ :=
  ∏ h ∈ Finset.Icc 1 d,
    weight P p (ancestor T l h) /
      ∑ k ∈ T.children (T.parent (ancestor T l h)), weight P p k

/-- The scalars `u_j(p)` of §7.1 (p. 335) at the nonleaf nodes, computed top-down:
`u_root(p) = R_root(p)` and `u_j(p) = η_j u_{Parent(j)}(p) + (1 − η_j) R_j(p)`. -/
noncomputable def uScalar (P : Params T) (p : Fin n → ℝ) (j : T.Inner) : ℝ :=
  if h : j = T.root then expectedRevenue P p
  else P.η j * uScalar P p (T.parent (Sum.inr j)) + (1 - P.η j) * revenue P p (Sum.inr j)
termination_by T.level j
decreasing_by have := T.level_parent j h; omega

end DLevelNestedLogit.Pricing


