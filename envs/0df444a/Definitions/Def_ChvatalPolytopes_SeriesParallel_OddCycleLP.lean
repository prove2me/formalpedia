-- Prove2me | Definitions.Def_ChvatalPolytopes_SeriesParallel_OddCycleLP
-- name    : ChvatalPolytopes_SeriesParallel_OddCycleLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:23:42.184982+00:00
-- url     : https://prove2.me/theorems/9fa5a52c-6639-4db0-a457-402def4f0ac8
-- title:
--   The odd-cycle system (7.1), $Z(G)$ and its linear programming dual (§7)
-- statement:
--   Let $G=(V,E)$ be a finite graph. We denote by $Z(G)$ the set of all subsets $C\subseteq V$ that **induce an odd circuit** in $G$: the induced subgraph $G[C]$ is a cycle of length $2k+1$ for some $k\ge 1$. Thus $|C|\ge 3$, triangles are included, and the cycle has no chords.
--
--   With $G$ we associate the system of inequalities in $x\in\mathbb R^V$
--   $$
--   \begin{aligned}
--   0\le x_u&\le 1 && (u\in V),\\
--   x_v+x_w&\le 1 && (vw\in E),\\
--   \textstyle\sum_{u\in C}x_u&\le \tfrac12(|C|-1) && (C\in Z(G)).
--   \end{aligned}\tag{7.1}
--   $$
--   The **primal problem** is to maximize $\sum_{u\in V}x_u$ subject to (7.1).
--
--   Treating $x_u\ge 0$ as sign constraints, its **linear programming dual** has variables $y_u\ge0$ ($u\in V$, for the rows $x_u\le1$), $z_e\ge0$ ($e\in E$) and $w_C\ge0$ ($C\in Z(G)$), and reads
--   $$
--   \min\ \sum_{u\in V}y_u+\sum_{e\in E}z_e+\sum_{C\in Z(G)}\tfrac12(|C|-1)\,w_C
--   \quad\text{s.t.}\quad y_u+\sum_{e\ni u}z_e+\sum_{C\ni u}w_C\ \ge\ 1\quad(u\in V).
--   $$
--
--   These are the two linear programs of Theorem 7.1.
--
--   **Formalization Note** `InducesOddCircuit H C` says `H.induce C` is graph-isomorphic to Mathlib's `cycleGraph (2k+1)` with `k ≥ 1`; `oddCircuits G` is $Z(G)$ as a `Finset (Finset V)`. `OddCycleFeasible G x` is (7.1), `primalValue x` is $\sum_u x_u$. Dual variables are `y : V → ℝ`, `z : G.edgeSet → ℝ` (one per edge) and `w` on the subtype of $Z(G)$; `DualFeasible` and `dualValue` are the dual constraints and objective above. The paper does not write the dual out; this is the standard dual with $x\ge 0$ as sign constraints (treating $-x_u\le0$ as rows with their own dual variables gives an equivalent dual).
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 150, §7, definition of Z(G) and system (7.1); p. 151, Theorem 7.1 (the dual)

import Mathlib

namespace ChvatalPolytopes.SeriesParallel

/-- The vertex set `C` **induces an odd circuit** in `H`: the induced subgraph `H[C]` is
isomorphic to the cycle `C_{2k+1}` for some `k ≥ 1` (so `|C| = 2k + 1 ≥ 3`, triangles included,
and `H[C]` has no chords). -/
def InducesOddCircuit {V : Type*} (H : SimpleGraph V) (C : Set V) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H.induce C ≃g SimpleGraph.cycleGraph (2 * k + 1))

/-- `Z(G)` (Chvátal 1975, p. 150): the set of all the subsets of `V` that induce an odd circuit
in `G`, as a finset of finsets of vertices. -/
noncomputable def oddCircuits {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun C : Finset V => InducesOddCircuit G (C : Set V)

/-- `x ∈ ℝ^V` satisfies the system (7.1) (Chvátal 1975, p. 150):
* `0 ≤ x_u ≤ 1` for `u ∈ V`,
* `x_v + x_w ≤ 1` for every edge `vw ∈ E`,
* `∑_{u ∈ C} x_u ≤ ½(|C| − 1)` for every `C ∈ Z(G)`. -/
def OddCycleFeasible {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  (∀ u : V, 0 ≤ x u ∧ x u ≤ 1) ∧
  (∀ v w : V, G.Adj v w → x v + x w ≤ 1) ∧
  (∀ C ∈ oddCircuits G, ∑ u ∈ C, x u ≤ ((C.card : ℝ) - 1) / 2)

/-- The primal objective `∑_{u ∈ V} x_u`. -/
def primalValue {V : Type*} [Fintype V] (x : V → ℝ) : ℝ :=
  ∑ u : V, x u

/-- Feasibility for the linear programming dual of `max ∑ x_u` subject to (7.1), where
`0 ≤ x_u` is treated as a sign constraint (it carries no dual variable). Dual variables:
`y_u` for the row `x_u ≤ 1`, `z_e` for the row of the edge `e`, `w_C` for the row of `C ∈ Z(G)`.
Constraints: `y, z, w ≥ 0` and, for every `u ∈ V`,
`y_u + ∑_{e ∋ u} z_e + ∑_{C ∋ u} w_C ≥ 1`. -/
def DualFeasible {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C ∈ oddCircuits G} → ℝ) : Prop :=
  (∀ u : V, 0 ≤ y u) ∧ (∀ e : G.edgeSet, 0 ≤ z e) ∧
  (∀ C : {C : Finset V // C ∈ oddCircuits G}, 0 ≤ w C) ∧
  ∀ u : V, 1 ≤ y u + (∑ e : G.edgeSet, if u ∈ (e : Sym2 V) then z e else 0) +
    ∑ C : {C : Finset V // C ∈ oddCircuits G}, if u ∈ C.1 then w C else 0

/-- The dual objective `∑_u y_u + ∑_e z_e + ∑_{C ∈ Z(G)} ½(|C| − 1) w_C`. -/
noncomputable def dualValue {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V → ℝ) (z : G.edgeSet → ℝ) (w : {C : Finset V // C ∈ oddCircuits G} → ℝ) : ℝ :=
  (∑ u : V, y u) + (∑ e : G.edgeSet, z e) +
    ∑ C : {C : Finset V // C ∈ oddCircuits G}, ((C.1.card : ℝ) - 1) / 2 * w C

end ChvatalPolytopes.SeriesParallel


