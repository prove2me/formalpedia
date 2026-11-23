-- Prove2me | Definitions.Def_BoundedDegreeST_PlusOne_Supplement_LeafAlgorithm
-- name    : BoundedDegreeST_PlusOne_Supplement_LeafAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:48:26.178094+00:00
-- url     : https://prove2.me/theorems/46166d9e-e9a2-4cda-b5e6-991d076325f7
-- title:
--   Figure 2 — leaf deletion on surviving vertices and real-cost correctness specification
-- statement:
--   Let $V$ be a finite original vertex set. A state records its surviving vertices $R\subseteq V$, a residual edge set $E$, integer residual bounds $B_v$, constrained vertices $W\subseteq R$, and edges $F$ already selected on the original graph. The residual LP uses the published spanning-tree relaxation on the vertex subtype $R$, with no contracted forest. A vector is zero off $E$; basicness includes every tight row, including zero coordinates.
--
--   One nonterminal iteration chooses any basic optimal LP vector, deletes its zero edges and, when a support leaf exists, includes its unique edge $uv$, deletes the leaf $v$ and decrements $B_u$. It then removes one remaining constraint of support degree at most three when any exists. Both tests are mandatory; the degree test uses the support before leaf deletion and $W$ after deletion. A singleton residual returns $F$ without adding an edge. Every output is an edge set on the original vertices.
--
--   For an initial LP-feasible instance with every vertex constrained, the correctness specification requires a run, a bound on every run prefix, and the following guarantee for every returned $H$:
--
--   $$H\subseteq E,\qquad H\text{ spans }V,\qquad d_H(v)\le B_v+2,\qquad c(H)\le\sum_{e\in E}c_ex_e\quad\text{for every feasible }x.$$
--
--   It also states the cost comparison with every original degree-feasible tree. The prefix bound is $k\le2|V|-1$, computed in the integers. This predicate is a target asserted by Theorem 3.3, not an assumption on a supplied algorithm.
--
--   **Formalization Note** Nonempty subtour sets avoid the impossible empty-set row. Figure 2's last isolated vertex has no edge to add: the explicit singleton stop is the boundary convention supported by the source's leaf discussion. No restriction $|V|\ge2$ is imposed on correctness. Step 2b's test "at most one edge incident at $v$ in $E^*$" is read as support degree exactly one: in a feasible residual with at least two vertices every vertex has support degree at least one (the subtour row on the other vertices forces $x^*(\delta(v))\ge1$), so the two tests agree on every nonterminal state.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, DOI 10.1145/1250790.1250887, p. 664, Figure 2 and Eqs. (10)–(14)

import Definitions.Def_BoundedDegreeST_PlusOne_LP

namespace BoundedDegreeST.PlusOne.Supplement

/-- Figure 2 keeps original vertex labels, including those already deleted. -/
structure LeafState (V : Type*) where
  alive : Finset V
  E : Finset (Sym2 V)
  B : V → ℤ
  W : Finset V
  selected : Finset (Sym2 V)

/-- An edge on the surviving vertex subtype, viewed on the original vertex set. -/
def liftEdge {V : Type*} {R : Finset V} (e : Sym2 {v // v ∈ R}) : Sym2 V :=
  e.map Subtype.val

/-- The existing LP is used on precisely the surviving vertices. -/
noncomputable def residualEdges {V : Type*} [Fintype V] [DecidableEq V]
    (I : LeafState V) : Finset (Sym2 {v // v ∈ I.alive}) := by
  classical
  exact Finset.univ.filter (fun e => liftEdge e ∈ I.E)

noncomputable def residualW {V : Type*} [Fintype V] [DecidableEq V]
    (I : LeafState V) : Finset {v // v ∈ I.alive} := by
  classical
  exact Finset.univ.filter (fun v => v.val ∈ I.W)

/-- Edges and constraints refer only to surviving vertices. Selected edges retain
original labels and are not part of the residual LP. -/
def WellFormed {V : Type*} (I : LeafState V) : Prop :=
  SimpleEdges I.E ∧ I.W ⊆ I.alive ∧ ∀ e ∈ I.E, ∀ v ∈ e, v ∈ I.alive

/-- LP-MBDST (11)--(14), through the published F=empty specialization. -/
def ResidualFeasible {V : Type*} [Fintype V] [DecidableEq V]
    (I : LeafState V) (x : Sym2 V → ℝ) : Prop :=
  Supported I.E x ∧ Feasible (residualEdges I) (fun v => I.B v.val)
    (residualW I) ∅ (fun e => x (liftEdge e))

def ResidualBasic {V : Type*} [Fintype V] [DecidableEq V]
    (I : LeafState V) (x : Sym2 V → ℝ) : Prop :=
  Supported I.E x ∧ Basic (residualEdges I) (fun v => I.B v.val)
    (residualW I) ∅ (fun e => x (liftEdge e))

def ResidualOptimal {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : LeafState V) (x : Sym2 V → ℝ) : Prop :=
  Supported I.E x ∧ Optimal (fun e => c (liftEdge e)) (residualEdges I)
    (fun v => I.B v.val) (residualW I) ∅ (fun e => x (liftEdge e))

/-- Step 2b must take one leaf if any exists. Its unique edge is included,
the leaf deleted, and only its neighbour's residual bound decremented. -/
def LeafUpdate {V : Type*} [DecidableEq V]
    (I : LeafState V) (S : Finset (Sym2 V)) (J : LeafState V) : Prop :=
  if ∃ v ∈ I.alive, degree S v = 1 then
    ∃ v ∈ I.alive, ∃ u ∈ I.alive, u ≠ v ∧
      degree S v = 1 ∧ s(v, u) ∈ S ∧
      J.alive = I.alive.erase v ∧
      J.E = S.filter (fun e => v ∉ e) ∧
      J.B = (fun w => if w = u then I.B w - 1 else I.B w) ∧
      J.W = I.W.erase v ∧ J.selected = insert (s(v, u)) I.selected
  else
    J.alive = I.alive ∧ J.E = S ∧ J.B = I.B ∧ J.W = I.W ∧
      J.selected = I.selected

/-- Step 2c uses the support from Step 2a and W after the leaf deletion.
A successful test must remove one constraint. -/
def DropUpdate {V : Type*} [DecidableEq V]
    (S : Finset (Sym2 V)) (J K : LeafState V) : Prop :=
  K.alive = J.alive ∧ K.E = J.E ∧ K.B = J.B ∧ K.selected = J.selected ∧
  (if ∃ v ∈ J.W, degree S v ≤ 3 then
     ∃ v ∈ J.W, degree S v ≤ 3 ∧ K.W = J.W.erase v
   else K.W = J.W)

/-- A complete nonterminal Figure 2 iteration, with all successful tests mandatory. -/
def LeafStep {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I K : LeafState V) : Prop :=
  1 < I.alive.card ∧
  ∃ x : Sym2 V → ℝ, ResidualBasic I x ∧ ResidualOptimal c I x ∧
    ∃ J : LeafState V, LeafUpdate I (support I.E x) J ∧
      DropUpdate (support I.E x) J K

/-- The last isolated vertex adds no edge. This resolves Figure 2's missing
terminal edge; outputs always use the full original vertex set. -/
inductive LeafReturns {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : LeafState V → Finset (Sym2 V) → Prop
  | done (I : LeafState V) (h : I.alive.card ≤ 1) : LeafReturns c I I.selected
  | step {I J : LeafState V} {H : Finset (Sym2 V)}
      (h : LeafStep c I J) (tail : LeafReturns c J H) : LeafReturns c I H

/-- Every prefix is counted, not merely a terminating run. -/
inductive LeafChain {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : ℕ → LeafState V → LeafState V → Prop
  | nil (I : LeafState V) : LeafChain c 0 I I
  | cons {k : ℕ} {I J K : LeafState V}
      (h : LeafStep c I J) (tail : LeafChain c k J K) : LeafChain c (k + 1) I K

/-- All vertices initially constrained, selected set empty (Figure 2, Step 1). -/
def initial {V : Type*} [Fintype V] (E : Finset (Sym2 V)) (B : V → ℤ) : LeafState V :=
  ⟨Finset.univ, E, B, Finset.univ, ∅⟩

/-- Full real-cost correctness and nonvacuous termination. Integer arithmetic
keeps the iteration bound meaningful at zero vertices; LP feasibility excludes it. -/
def FigureTwoCorrect : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (B : V → ℤ) (c : Sym2 V → ℝ), SimpleEdges E →
    (∃ x, Feasible E B Finset.univ ∅ x) →
    (∃ H, LeafReturns c (initial E B) H) ∧
    (∀ (k : ℕ) (J : LeafState V), LeafChain c k (initial E B) J →
      (k : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 1) ∧
    (∀ H, LeafReturns c (initial E B) H →
      H ⊆ E ∧ IsSpanningTree H ∧
      (∀ v, (degree H v : ℤ) ≤ B v + 2) ∧
      (∀ x, Feasible E B Finset.univ ∅ x → cost c H ≤ ∑ e ∈ E, c e * x e) ∧
      (∀ T, T ⊆ E → IsSpanningTree T → (∀ v, (degree T v : ℤ) ≤ B v) →
        cost c H ≤ cost c T))

end BoundedDegreeST.PlusOne.Supplement


