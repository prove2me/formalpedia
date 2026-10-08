-- Prove2me | Definitions.Def_BoundedDegreeST_LowerUpper_Algorithm
-- name    : BoundedDegreeST_LowerUpper_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:52.3498+00:00
-- url     : https://prove2.me/theorems/af0d5abf-14d6-4a36-849a-8729be6b4bc5
-- title:
--   MBDCT Algorithm2 (Figure 5, p. 668) as a step relation and its runs
-- statement:
--   A state of **MBDCT Algorithm2** is $(E,\mathcal A,\mathcal B,U,W,F)$; the vertex set and costs are fixed. One iteration from a state whose $F$ is not a spanning tree (Step 1 has not returned) does:
--
--   1. **Step 2.** Choose a basic optimal solution $x^*$ of LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ and delete every edge with $x^*_e=0$; the support is $E^*$.
--   2. **Step 3.** If some $e=\{u,v\}\in E^*$ has $x^*_e=1$, then $\hat F=\{e\}$ for one such $e$, $e$ moves from $G$ to $F$, and $A_u,B_u,A_v,B_v$ each decrease by one. Otherwise $\hat F=\varnothing$.
--   3. **Step 4.** If no edge was picked in Step 3 and some $v\in U\cup W$ has $\deg_{E^*}(v)\le 2$, then one such $v$ is removed from both $U$ and $W$.
--
--   Both tests are mandatory: when one succeeds the step must act. A **run** returns $\varnothing$ when $F$ is a spanning tree (Step 1) and otherwise returns $\hat F\cup H'$, where $H'$ is returned by the recursive call on the updated state (Step 5). A **chain** of length $k$ is $k$ consecutive iterations.
--
--   This relation quantifies over every choice the algorithm leaves open (which basic optimal solution, which 1-edge, which vertex), so the theorem about it holds for every implementation.
--
--   **Formalization Note** Figure 5's Step 4 is printed without the guard "no edge was picked"; the paper's text under Lemma 5.1 states it: "we only remove a degree constraint on $v\in U\cup W$ if $v$ is of degree 2 and there is no 1-edge", and the analysis there ("since there is no 1-edge, we must have $A_v\le 1$") uses it. The guard is formalized; Figure 5's "of degree at most two" is kept. The LP is solved by an oracle (any basic optimal solution); running time beyond the number of iterations is not modelled.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, Figure 5 (MBDCT Algorithm 2) and the paragraph after Lemma 5.1

import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- A state of MBDCT Algorithm2 (Figure 5, p. 668): the current graph `E`, the
integer lower bounds `A` on `U`, the integer upper bounds `B` on `W`, and the
current forest `F`. The vertex set `V` and the costs are fixed. -/
structure Instance (V : Type*) where
  E : Finset (Sym2 V)
  A : V → ℤ
  B : V → ℤ
  U : Finset V
  W : Finset V
  F : Finset (Sym2 V)

/-- A well-formed instance: `E` simple, `F` a forest, and `E(F) ∩ E(G) = ∅`. -/
def Valid {V : Type*} (I : Instance V) : Prop :=
  BoundedDegreeST.PlusOne.SimpleEdges I.E ∧ BoundedDegreeST.PlusOne.IsForest I.F ∧ Disjoint I.E I.F

/-- One pass through Steps 2–4 of MBDCT Algorithm2, from a state whose forest is
not a spanning tree (Step 1 did not return). `picked` is `F̂`.
* Step 2: `x` is a basic optimal solution; the zero edges are deleted
  (`E* = support`).
* Step 3: if some `e ∈ E*` has `x_e = 1`, then `F̂ = {e}` for one such `e`,
  `e` moves from the graph to `F`, and `A`, `B` drop by one at both ends of `e`;
  otherwise `F̂ = ∅`.
* Step 4: if no edge was picked in Step 3 and some `v ∈ U ∪ W` has
  `deg_{E*}(v) ≤ 2`, then one such `v` is removed from both `U` and `W`;
  otherwise `U`, `W` are unchanged. (The guard "no 1-edge" is the paper's
  prose under Lemma 5.1: "we only remove a degree constraint on `v ∈ U ∪ W` if
  `v` is of degree 2 and there is no 1-edge".)
Both tests are mandatory: when they succeed, the step must act. -/
noncomputable def Step {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (picked : Finset (Sym2 V)) (J : Instance V) : Prop := by
  classical
  exact ¬ BoundedDegreeST.PlusOne.IsSpanningTree I.F ∧ ∃ x : Sym2 V → ℝ,
    Basic I.E I.A I.B I.U I.W I.F x ∧ Optimal c I.E I.A I.B I.U I.W I.F x ∧
    let EStar := support I.E x
    picked ⊆ EStar ∧ picked.card ≤ 1 ∧
    (∀ e ∈ picked, x e = 1) ∧
    ((∃ e ∈ EStar, x e = 1) ↔ picked.Nonempty) ∧
    ∃ dropped : Finset V,
      dropped ⊆ I.U ∪ I.W ∧ dropped.card ≤ 1 ∧
      (∀ v ∈ dropped, degree EStar v ≤ 2) ∧
      ((picked = ∅ ∧ ∃ v ∈ I.U ∪ I.W, degree EStar v ≤ 2) ↔ dropped.Nonempty) ∧
      J.E = EStar \ picked ∧
      J.A = (fun v => I.A v - (degree picked v : ℤ)) ∧
      J.B = (fun v => I.B v - (degree picked v : ℤ)) ∧
      J.U = I.U \ dropped ∧ J.W = I.W \ dropped ∧
      J.F = I.F ∪ picked

/-- A finite sequence of `k` consecutive iterations (Steps 2–4) starting from `I`. -/
inductive Chain {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : Instance V → ℕ → Prop where
  | nil (I : Instance V) : Chain c I 0
  | cons {I J : Instance V} {k : ℕ} {picked : Finset (Sym2 V)}
      (hstep : Step c I picked J) (htail : Chain c J k) : Chain c I (k + 1)

/-- `Returns c I H`: some terminating run of MBDCT Algorithm2 on `I` returns `H`.
Step 1 returns `∅` when `F` is a spanning tree; Step 5 returns `F̂ ∪ H'`, where
`H'` is returned by the recursive call on the updated state. -/
inductive Returns {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : Instance V → Finset (Sym2 V) → Prop where
  | done (I : Instance V) (h : BoundedDegreeST.PlusOne.IsSpanningTree I.F) : Returns c I ∅
  | next {I J : Instance V} {picked H : Finset (Sym2 V)}
      (hstep : Step c I picked J) (htail : Returns c J H) :
      Returns c I (picked ∪ H)

end BoundedDegreeST.LowerUpper


