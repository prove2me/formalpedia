-- Prove2me | Definitions.Def_StochasticProg_MultistageBounds_Instance
-- name    : StochasticProg_MultistageBounds_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:15:43.387289+00:00
-- url     : https://prove2.me/theorems/b8350ae9-6e29-4c13-8af6-2379e897f4da
-- title:
--   Multistage recourse LP deterministic equivalent over a scenario tree
-- statement:
--   An **`Instance`** bundles the node-varying data of the multistage recourse LP deterministic
--   equivalent Birge & Louveaux write as (1.1) (over the exact tree) and (1.2) (over the
--   aggregated tree), p. 418-419: for a scenario tree `T : Tree H` and dimensions `n` (decision),
--   `m` (constraint), it consists of
--   - `c : T.Node → Fin n → ℝ`, the (possibly node-dependent) stage cost;
--   - `W : Fin H → Matrix (Fin m) (Fin n) ℝ`, the recourse matrix, a function of the stage alone
--     ("the recourse within each period `Wᵗ` is known and not random", p. 418);
--   - `Tmat : T.Node → Matrix (Fin m) (Fin n) ℝ`, the technology matrix at each node (the exact
--     `Tᵗ` for (1.1), or its conditional-expectation aggregate `T̄ᵗᵢ` for (1.2));
--   - `h : T.Node → Fin m → ℝ`, the right-hand side at each node (similarly `hᵗ` or `h̄ᵗᵢ`);
--   - `p : T.Node → ℝ`, each node's unconditional probability, positive and summing to `1` within
--     every stage.
--
--   Two derived operations use an `Instance`: `Feasible x` holds for a tree-wide assignment
--   `x : T.Node → Fin n → ℝ` of decisions to nodes when every node `j`'s own decision is
--   nonnegative and satisfies its equality constraint against its parent's decision,
--   $$
--   W^{\mathrm{stage}(j)} x_j \;=\; h_j - T_j\,x_{\mathrm{anc}(j)} \qquad (j \ne \mathrm{root}),
--   \qquad W^{\mathrm{stage(root)}} x_{\mathrm{root}} = h_{\mathrm{root}},
--   $$
--   matching (1.1)/(1.2)'s constraint block; and `obj x` is the probability-weighted objective
--   $\sum_{j} p_j\, c_j^{\mathsf T} x_j$.
--
--   **Formalization Note** The same `Instance`/`Feasible`/`obj` triple is applied twice in
--   Chapter 10, Theorem 1: once with the exact tree and data (instantiating problem (1.1)), and
--   once with the aggregated tree and conditional-expectation data (instantiating problem (1.2)).
--   This mirrors Chunk 06's `Multistage.Instance` for the exact multistage recourse LP, restated
--   here for the same import-restriction reason as the companion `Tree` definition.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 418-419, Chapter 10, Eq. (1.1)-(1.2)

import Mathlib
import Definitions.Def_StochasticProg_MultistageBounds_Tree

namespace StochasticProg.MultistageBounds

open scoped Matrix

variable {H n m : ℕ}

/-- A multistage stochastic linear program's deterministic equivalent over a scenario tree `T`,
in the notation of Birge & Louveaux (1.1)/(1.2), p. 418-419. `c` is the (possibly
node-dependent) stage cost, `W` the recourse matrix (a function of the stage alone: "the
recourse within each period `Wt` is known and not random", p. 418), `Tmat` the technology
matrix and `h` the right-hand side at each node (the book's `Tt`/`ht` for the exact tree of
(1.1), or their conditional-expectation aggregates `T̄ti`/`h̄ti` for the coarse tree of (1.2)),
and `p` the node's unconditional probability. This single structure instantiates *both* (1.1)
(applied to the exact tree) and (1.2) (applied to the aggregated tree) in Chapter 10, Theorem 1
— the same deterministic-equivalent shape Chunk 06's `Multistage.Instance` uses for the exact
multistage recourse LP, restated here (see `Def_StochasticProg_MultistageBounds_Tree.lean`'s
docstring for why it is restated rather than imported). -/
structure Instance (H n m : ℕ) (T : Tree H) where
  c : T.Node → Fin n → ℝ
  W : Fin H → Matrix (Fin m) (Fin n) ℝ
  Tmat : T.Node → Matrix (Fin m) (Fin n) ℝ
  h : T.Node → Fin m → ℝ
  p : T.Node → ℝ
  hp_pos : ∀ k, 0 < p k
  hp_sum : ∀ t : Fin H, ∑ k ∈ Finset.univ.filter (fun k => T.stage k = t), p k = 1

variable {T : Tree H} (inst : Instance H n m T)

/-- The transition term entering node `j`'s equality constraint (1.2): `T^{t-1}_j x^{t-1}_{a(j)}`
for a non-root `j`, and `0` at the root (no incoming transition, p. 419: the root's constraint
is simply `W^1x^1 = h^1`). -/
def transitionTerm (j : T.Node) (xp : Fin n → ℝ) : Fin m → ℝ :=
  if (T.stage j).val = 0 then 0 else Matrix.mulVec (inst.Tmat j) xp

/-- Node `j`'s own feasible region given its parent's decision `xp` (unused at the root):
nonnegativity and the equality constraint of (1.1)/(1.2). -/
def LocalFeasible (j : T.Node) (xp : Fin n → ℝ) (xj : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ xj i) ∧
    Matrix.mulVec (inst.W (T.stage j)) xj = inst.h j - transitionTerm inst j xp

/-- The tree-wide feasible region: an assignment of a decision to every node, feasible for its
own parent's decision at every node. This is the feasible set of the deterministic equivalent
(1.1) (over the exact tree) or (1.2) (over the aggregated tree). -/
def Feasible (x : T.Node → Fin n → ℝ) : Prop :=
  ∀ j : T.Node, LocalFeasible inst j (x (T.anc j)) (x j)

/-- The deterministic-equivalent objective of (1.1)/(1.2): the probability-weighted sum of
every node's own stage cost, `c1x1 + Σt Σi pti ctxti` read as one sum over all nodes (the root
contributes `p_root · c_root · x_root` with `p_root = 1`, matching the book's un-weighted
`c1x1` term). -/
def obj (x : T.Node → Fin n → ℝ) : ℝ :=
  ∑ j : T.Node, inst.p j * dotProduct (inst.c j) (x j)

end StochasticProg.MultistageBounds


