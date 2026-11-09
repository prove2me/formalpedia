-- Prove2me | Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets
-- name    : WeightedEdgeColor_IsAvgOfFeasibleSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:20.924557+00:00
-- url     : https://prove2.me/theorems/c0f43a63-7bfb-4139-862c-f6594a1db1bb
-- title:
--   Averages of feasible sets: the local packing polytope $\mathcal K$ and $\mathcal K_v$
-- statement:
--   Consider a finite set of items with weights $w_e$. A subset $S$ is **feasible** if $\sum_{e\in S}w_e\le 1$. A vector $x=(x_e)$ is an **average of feasible sets** if there are nonnegative numbers $p_S$ with
--   $$
--   \sum_S p_S=1,\qquad x_e=\sum_{S\ni e}p_S,
--   $$
--   where only feasible sets $S$ are used. Write $\mathcal K$ for the set of such vectors; equivalently $\mathcal K=\operatorname{conv}\{\mathbf 1_S: \sum_{e\in S}w_e\le1\}$, and $x\in\mathcal K$ if and only if there is a random feasible set containing each item $e$ with probability $x_e$.
--
--   At a vertex $v$ of an edge-weighted graph the items are the edges $E(v)$, and
--   $$
--   \mathcal K_v=\operatorname{conv}\Big\{\mathbf 1_S: S\subseteq E(v),\ \sum_{e\in S}w_e\le1\Big\}.
--   $$
--   A vector $y$ indexed by all edges satisfies $(y_e:e\ni v)\in\mathcal K_v$ when its restriction to $E(v)$ lies in $\mathcal K$.
--
--   This polytope is strictly smaller than the load condition $\sum_e w_ex_e\le1$: two items of weight $0.6$ with $x=0.8$ have load $0.96$ but are not in $\mathcal K$.
--
--   **Formalization Note** The numbers $p_S$ form a function on all subsets, and "only feasible sets are used" means $p_S\neq0$ implies $S$ feasible. The graph version is a helper in the same module, applied to the edges at $v$.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Appendix C, p.33; §C.1, p.33

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

/-- `x ∈ 𝒦`: for a finite set of items `ι` with weights `w`, the vector `x = (x_e)` is an
average of feasible sets, i.e. there are nonnegative numbers `p_S` with `∑_S p_S = 1` and
`x_e = ∑_{S ∋ e} p_S`, where only feasible sets (total weight at most one) are used.
Equivalently `x ∈ conv{1_S : ∑_{e ∈ S} w_e ≤ 1}`.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
Appendix C, p.33, and §C.1, p.33.

**Formalization Note.** `p` is a function on all subsets of `ι`; "only feasible sets are used"
is `p S ≠ 0 → ∑_{e ∈ S} w_e ≤ 1`. This is the polytope, not the load bound `∑ w_e x_e ≤ 1`
(which is strictly weaker, Remark on p.33). -/
def IsAvgOfFeasibleSets {ι : Type} [Fintype ι] [DecidableEq ι] (w x : ι → ℝ) : Prop :=
  ∃ p : Finset ι → ℝ, (∀ S, 0 ≤ p S) ∧ ∑ S, p S = 1 ∧
    (∀ S, p S ≠ 0 → ∑ e ∈ S, w e ≤ 1) ∧
    ∀ e, x e = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => e ∈ S), p S

namespace WGraph

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V]

/-- `(y_e : e ∋ v) ∈ 𝒦_v = conv{1_S : S ⊆ E(v), ∑_{e∈S} w_e ≤ 1}`: the restriction of `y` to
the edges at `v` is an average of feasible subsets of `E(v)`. Only the coordinates `e ∈ E(v)`
of `y` are constrained. -/
def InK (G : WGraph V E) (v : V) (y : E → ℝ) : Prop :=
  IsAvgOfFeasibleSets (fun e : G.inc v => G.w e) (fun e : G.inc v => y e)

end WGraph

end WeightedEdgeColor


