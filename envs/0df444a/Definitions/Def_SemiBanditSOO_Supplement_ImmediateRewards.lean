-- Prove2me | Definitions.Def_SemiBanditSOO_Supplement_ImmediateRewards
-- name    : SemiBanditSOO_Supplement_ImmediateRewards
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:07.425523+00:00
-- url     : https://prove2.me/theorems/ea1f1cc7-ffeb-4dab-93ed-ccde65d9a2a2
-- title:
--   Immediate rewards $\chi_e$ satisfying conditions (a)–(c) of Theorem 3.7
-- statement:
--   Let $s_1,\dots,s_n\ge1$ be integers. Each revelation edge $e=(u,v)$, revealing coordinate $i$, carries a measurable **immediate reward** $\chi_e(x_{\mathrm{obs}(v)})\in[0,1]$. The family $(\chi_e)$ satisfies the conditions of Theorem 3.7 when:
--
--   1. **(a)** For every revelation edge $e=(u,v)$ revealing $i$ and every $x_{\mathrm{obs}(u)}$ with $v\in\mathcal A_u(x_{\mathrm{obs}(u)})$, the function $z\mapsto\chi_e(z,x_{\mathrm{obs}(u)})$ has level-set complexity at most $s_i$, and there is a number $\kappa_e(x_{\mathrm{obs}(u)})$, common to all leaves $\ell$ in the subtree rooted at $v$, such that
--   $$f_\ell(x_{\mathrm{obs}(\ell)})=\kappa_e(x_{\mathrm{obs}(u)})+\chi_e(x_{\mathrm{obs}(v)})+F_{e,\ell}(x_{\mathrm{obs}(\ell)}),\qquad 0\le F_{e,\ell}\le1,$$
--   for all values of the remaining coordinates.
--   2. **(b)** For the same edge and observations, the residual rewards $F_{e,\ell}$ and the sets of feasible actions at the nodes of the subtree rooted at $v$ are nonincreasing in $x_i$, with the other coordinates fixed and sets ordered by inclusion.
--   3. **(c)** For every realization $x$, the immediate rewards sum to at most $1$ along every root-to-leaf path consisting of feasible actions.
--
--   These conditions replace Assumption 3.1 in the regret bound of Theorem 3.7: the continuation value splits into an immediate reward and a residual value whose level-set complexities are controlled separately.
--
--   **Formalization Note.** On the published rooted-DAG model, the subtree rooted at $v$ is the set of nodes reachable from $v$. "For all remaining coordinate values" quantifies over every vector agreeing with $x$ on $\mathrm{obs}(u)$, and $\kappa$ is chosen after $x_{\mathrm{obs}(u)}$ and before the leaf and the remaining values. A path is a list of nodes from the root to a leaf whose consecutive pairs are feasible actions; only its revelation edges contribute to the sum in (c). $\chi$ is a function of the full vector that depends only on $\mathrm{obs}(v)$; its values off revelation edges are unused.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Theorem 3.7 (a)–(c), p.13

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet

open MeasureTheory

namespace SemiBanditSOO.Supplement

/-- **Conditions (a)–(c) of Theorem 3.7 on immediate rewards** (§3.3, p.13). Harada, Kawase,
Sumita, *Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*,
arXiv:2611.02739v1, Theorem 3.7, p.13.

Let `s_1, …, s_n ≥ 1` be integers. Each revelation edge `e = (u, v)` (revealing coordinate `i`)
carries an immediate reward `χ_e(x_obs(v)) ∈ [0, 1]`, measurable; here `χ u v x`.

(a) For every revelation edge `e = (u, v)` revealing `i` and every `x_obs(u)` with
    `v ∈ 𝒜_u(x_obs(u))`: `z ↦ χ_e(z, x_obs(u))` has level-set complexity at most `s_i`, and there
    is a number `κ_e(x_obs(u))`, common to all leaves `ℓ` of the subtree rooted at `v`, such that
    `F_{e,ℓ} := f_ℓ − κ_e − χ_e` satisfies `0 ≤ F_{e,ℓ} ≤ 1` for all remaining coordinate values.
(b) For the same edge and observations, `F_{e,ℓ}` (every leaf `ℓ` of the subtree) and the feasible
    sets `𝒜_w` (every node `w` of the subtree) are nonincreasing in `x_i`, other coordinates fixed,
    sets ordered by inclusion.
(c) For every realization `x`, the immediate rewards sum to at most `1` along every root-to-leaf
    path consisting of feasible actions.

**Formalization Note.**
* The decision structure is the published rooted DAG (footnote 1, p.6); "the subtree rooted at
  `v`" is the set of nodes reachable from `v` along edges (a tree's subtree, for trees).
* "For all remaining coordinate values" is: for every vector `y` agreeing with `x` on `obs(u)`;
  `κ` is chosen after `x` and before `ℓ` and `y`, so it depends only on the edge and `x_obs(u)`.
* `χ` is a function of the full vector that depends only on `obs(v)`; its values on stopping edges
  and on non-edges are never used (stopping edges carry no immediate reward).
* A path is a list of nodes starting at the root and ending at a leaf, each consecutive pair a
  feasible action for `x`; only its revelation edges contribute to the sum in (c). -/
def ImmediateRewardConditions {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)
    (s : Fin n → ℕ) (χ : V → V → Obs dom → ℝ) : Prop :=
  (∀ u, ∀ v ∈ Pb.children u, ∀ i, Pb.edgeCoord u v = some i →
    Measurable (χ u v) ∧ (∀ x, χ u v x ∈ Set.Icc (0 : ℝ) 1) ∧ DependsOn (Pb.obs v) (χ u v) ∧
    ∀ x : Obs dom, v ∈ Pb.feasible u x →
      -- (a), level-set complexity of the immediate reward in the revealed coordinate
      LevelSetCpxLE ((s i : ℕ) : ℕ∞) (fun z : dom i => χ u v (Function.update x i z)) ∧
      ∃ κ : ℝ,
        -- (a), the decomposition `f_ℓ = κ + χ + F` with `0 ≤ F ≤ 1`
        (∀ ℓ, Relation.ReflTransGen (fun a b => b ∈ Pb.children a) v ℓ → Pb.children ℓ = ∅ →
          ∀ y : Obs dom, (∀ j ∈ Pb.obs u, y j = x j) →
            0 ≤ Pb.reward ℓ y - κ - χ u v y ∧ Pb.reward ℓ y - κ - χ u v y ≤ 1) ∧
        -- (b), monotonicity in `x_i` of the residual rewards and of the feasible sets
        (∀ y y' : Obs dom, (∀ j ∈ Pb.obs u, y j = x j) → (∀ j, j ≠ i → y j = y' j) →
          ((y i : ℝ) ≤ (y' i : ℝ)) →
          (∀ ℓ, Relation.ReflTransGen (fun a b => b ∈ Pb.children a) v ℓ → Pb.children ℓ = ∅ →
            Pb.reward ℓ y' - κ - χ u v y' ≤ Pb.reward ℓ y - κ - χ u v y) ∧
          (∀ w, Relation.ReflTransGen (fun a b => b ∈ Pb.children a) v w →
            Pb.feasible w y' ⊆ Pb.feasible w y))) ∧
  -- (c), the immediate rewards along every feasible root-to-leaf path sum to at most 1
  (∀ (x : Obs dom) (p : List V), p.head? = some Pb.root →
    (∀ ℓ, p.getLast? = some ℓ → Pb.children ℓ = ∅) →
    p.IsChain (fun a b => b ∈ Pb.feasible a x) →
    ((p.zip p.tail).map fun e =>
      if (Pb.edgeCoord e.1 e.2).isSome then χ e.1 e.2 x else 0).sum ≤ 1)

end SemiBanditSOO.Supplement


