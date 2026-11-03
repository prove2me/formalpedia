-- Prove2me | Definitions.Def_RandomOrderCRS_Objective
-- name    : RandomOrderCRS_Objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:57.829808+00:00
-- url     : https://prove2.me/theorems/37e0e3ea-8d0b-4f3a-af13-5e9b5bd4ebc1
-- title:
--   The objective $\mathrm{obj}_G(e,y)$ and its form on pairs
-- statement:
--   For an edge $e$ of $G$ and $y\in[0,1]$, the paper's equation (4) defines
--
--   $$\mathrm{obj}_G(e,y):=\prod_{g\in\partial(e)}\ell(x_g,y)+\sum_{f\in\partial(e)}T(x_f+x_{f^c},y)\cdot s(x_f)\,y\prod_{g\in\partial(e)\setminus\{f\}}\ell(x_g,y).$$
--
--   Grouping $f$ with $f^c$ gives a formula in the pairs $(p_w,q_w):=(x_{u,w},x_{v,w})$, for $w\in N(u)\cup N(v)\setminus\{u,v\}$:
--
--   $$\prod_w\ell(p_w,y)\ell(q_w,y)+\sum_wT(p_w+q_w,y)\,y\,\big(s(p_w)\ell(q_w,y)+s(q_w)\ell(p_w,y)\big)\prod_{w'\ne w}\ell(p_{w'},y)\ell(q_{w'},y).$$
--
--   The second expression, defined for any finite family of pairs, is the form used by the vertex-splitting argument. `splitFamily` adds $k$ copies of the value $p_0/k$ to a family; for $(p,q)$ this is the pair family of the graph $G_k$ of p.21, and for $k=1$ the pair family of $G$.
--
--   **Formalization Note** The attenuation function is a parameter; the paper fixes $a=a_1$ throughout §3.1. The second formula is not displayed in the paper. A verification file proves that the two expressions agree.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §3.1, equation (4), p.20; Lemma 4 and the graph G_k, p.21; ec17–ec18

import Mathlib
import Definitions.Def_RandomOrderCRS_SimpleBlocker

open Finset

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The function `obj_G(e, y)` of arXiv:2209.07520v2, §3.1, equation (4), p.20:
`∏_{g∈∂(e)} ℓ(x_g, y) + ∑_{f∈∂(e)} T(x_f + x_{fᶜ}, y) · s(x_f) y ∏_{g∈∂(e)\{f}} ℓ(x_g, y)`.

**Formalization Note.** `a` is a parameter; the paper fixes `a = a₁` throughout §3.1. -/
noncomputable def obj (a : ℝ → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (e : G.edgeSet) (y : ℝ) : ℝ :=
  ∏ g ∈ edgeNbrs G e, ell a (x g) y +
    ∑ f ∈ edgeNbrs G e, T a (x f + x (pair (e : Sym2 V) (f : Sym2 V))) y * survival a (x f) * y *
      ∏ g ∈ (edgeNbrs G e).erase f, ell a (x g) y

/-- The function `obj_G(e, y)` as a function of the pairs `(p_w, q_w) := (x_{u,w}, x_{v,w})`, where
`w` runs over `N(u) ∪ N(v) \ {u, v}`:
`∏_w ℓ(p_w, y) ℓ(q_w, y) + ∑_w T(p_w + q_w, y) y (s(p_w) ℓ(q_w, y) + s(q_w) ℓ(p_w, y))
  ∏_{w′≠w} ℓ(p_{w′}, y) ℓ(q_{w′}, y)`.

**Formalization Note.** Not displayed in the paper. Grouping `f` with `fᶜ` turns (4) into this
formula. On ec17–ec19 the paper uses `obj` of the split graph `G_k`, which is not 1-regular, only
through this formula. -/
noncomputable def objPairs (a : ℝ → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ)
    (y : ℝ) : ℝ :=
  ∏ i, (ell a (p i) y * ell a (q i) y) +
    ∑ i, T a (p i + q i) y * y * (survival a (p i) * ell a (q i) y +
        survival a (q i) * ell a (p i) y) *
      ∏ j ∈ univ.erase i, (ell a (p j) y * ell a (q j) y)

/-- The family obtained from `p` by adding `k` copies of the value `p₀ / k`. For `(p, q)` it is the
pair family of the vertex-splitting graph `G_k` of arXiv:2209.07520v2, p.21: `x′_{wᵢ,r} := x_{w,r}/k`.
At `k = 1` it is the family `p` together with `p₀`, i.e. the pair family of `G`. -/
noncomputable def splitFamily {ι : Type} (p : ι → ℝ) (p₀ : ℝ) (k : ℕ) : ι ⊕ Fin k → ℝ :=
  Sum.elim p fun _ => p₀ / k

end RandomOrderCRS


