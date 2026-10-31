-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ScenarioTree
-- name    : KallMayerSLP_Multistage_ScenarioTree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:00.829694+00:00
-- url     : https://prove2.me/theorems/0a84f298-e26a-4b24-bc1e-6930a395e833
-- title:
--   Scenario tree with its partitions (the subfiltration $\widehat{\mathcal F}$)
-- statement:
--   A **scenario tree** for the intervals $\Xi^t$ consists of finite sets $\mathcal N_t$ of nodes for the stages $t=1,\dots,T$, with $\mathcal N_1=\{1\}$ the root; a parent $h_n\in\mathcal N_{t-1}$ for each node $n\in\mathcal N_t$, $t\ge2$; and a subinterval $\Xi^t_n$ attached to each node $n$ of a stage $t\ge2$, such that for every node $h$ of a stage $\nu<T$ the cells of its children $C_h$ form a partition of the next interval,
--   $$
--   \Xi^{\nu+1}=\bigcup_{k\in C_h}\Xi^{\nu+1}_k,
--   $$
--   with disjoint cells. Different nodes of one stage may use different partitions.
--
--   This is the data of the construction "Subfiltration and the corresponding scenario tree": the events $\Omega^{(n)}$ and the $\sigma$-algebras $\widehat{\mathcal F}_t=\sigma\{\Omega^{(n)}\mid n\in\mathcal N_t\}$ are determined by it and by $\xi$.
--
--   **Formalization Note** Nodes are indexed by their stage, so the stage of a node is part of its type. The children of $n$ are the nodes with parent $n$, so the sets $C_n$ are disjoint by construction; the book's $|C_n|\ge1$ follows from the covering condition when $\Xi^{\nu+1}$ is nonempty. Cells may be empty or null. The values at stage $0$, at stages beyond $T$, and the root's cell are unused.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, "Subfiltration and the corresponding scenario tree", (3.11), p.261 (PDF 270)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP
import Definitions.Def_KallMayerSLP_Multistage_IsInterval

namespace KallMayerSLP.Multistage

/-- A **scenario tree with its partitions**, which is what "a subfiltration `ℱ̂` constructed as
above" consists of (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, "Subfiltration
and the corresponding scenario tree", (3.11), p.261, PDF 270):

* `Node t` is the finite node set `𝒩_t` of stage `t`, and `𝒩_1` is the single root;
* `parent t` sends a node of stage `t + 1` to its unique parent `h_n`, so that the children
  `C_n` of a node `n` are the nodes `v` with `parent v = n`, and the `C_n` are disjoint;
* `cell t n` is the subinterval `Ξ^t_n` of `Ξ^t` attached to the node `n` of stage `t ≥ 2`;
* for each node `h` of a stage `ν < T`, the cells of its children form a partition of `Ξ^{ν+1}`
  into subintervals, (3.11). The partition may differ from one node to another.

The sets `Ω^(n)` and the σ-algebras `ℱ̂_t = σ{Ω^(n) | n ∈ 𝒩_t}` of the book are determined by this
data and `ξ`; see `omegaNode`.

**Formalization Note.** Nodes are indexed by their stage, so the stage `t_n` of a node is part of
its type. The book's `|C_n| = r_n ≥ 1` is not a separate field: finiteness is `fintypeNode`, and a
node of a stage below `T` has a child whenever `Ξ^{ν+1}` is nonempty, by the covering field. A cell
may be empty or `P`-null. `Node 0`, `Node t` for `t > T`, `parent` outside `1 ≤ t < T` and the root's
`cell` are unused, and any tree of the book extends to them (for instance `Node t` empty for
`t > T` and `Node 0` a point). -/
structure ScenarioTree (D : MSLP) (Ξ : ∀ t, Set (Fin (D.r t) → ℝ)) where
  /-- The nodes `𝒩_t` of stage `t`. -/
  Node : ℕ → Type
  fintypeNode : ∀ t, Fintype (Node t)
  uniqueRoot : Unique (Node 1)
  /-- The parent `h_n` of a node `n` of stage `t + 1`. -/
  parent : ∀ t, Node (t + 1) → Node t
  /-- The subinterval `Ξ^t_n` attached to the node `n` of stage `t`. -/
  cell : ∀ t, Node t → Set (Fin (D.r t) → ℝ)
  isInterval_cell : ∀ t, 2 ≤ t → t ≤ D.T → ∀ n, IsInterval (cell t n)
  disjoint_cell : ∀ t, 1 ≤ t → t < D.T → ∀ u v : Node (t + 1), parent t u = parent t v → u ≠ v →
    Disjoint (cell (t + 1) u) (cell (t + 1) v)
  iUnion_cell : ∀ t, 1 ≤ t → t < D.T → ∀ h : Node t,
    ⋃ (v : Node (t + 1)) (_ : parent t v = h), cell (t + 1) v = Ξ (t + 1)

attribute [instance] ScenarioTree.fintypeNode

end KallMayerSLP.Multistage


