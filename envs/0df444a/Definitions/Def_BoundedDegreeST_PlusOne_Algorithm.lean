-- Prove2me | Definitions.Def_BoundedDegreeST_PlusOne_Algorithm
-- name    : BoundedDegreeST_PlusOne_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:34.820955+00:00
-- url     : https://prove2.me/theorems/1c79e6c4-deb7-4578-baf1-7d7c3de72ced
-- title:
--   MBDCT Algorithm, Figure 4: recursive rounding runs
-- statement:
--   A state consists of the current edge set $E$, integer bounds $B$, constrained vertices $W$, and partial forest $F$. In a nonterminal iteration, choose any basic optimal solution $x^*$ of the current LP and retain its support $E^*$. If a supported edge has $x^*_e=1$, select one, add it to $F$, remove it from $E^*$ and decrement the bounds at its ends. If a vertex $w\in W$ then has $\deg_{E^*}(w)\le B_w+1$, remove one such vertex from $W$. Each choice is mandatory when its test succeeds. A run returns the selected edges together with the result of recursively processing the updated state; it returns the empty set when $F$ is already a spanning tree.
--
--   This relation defines the exact outputs whose cost and degrees are asserted in the two main theorems.
--
--   **Formalization Note** The vertex test reads $E^*$ before deletion of the selected edge and $B$ after its update, following the printed step order. Costs are fixed across recursion; the LP solve is an oracle choice of any basic optimal solution.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 666, Figure 4

import Definitions.Def_BoundedDegreeST_PlusOne_LP

namespace BoundedDegreeST.PlusOne

/-- Current graph, remaining integer degree bounds, constrained vertices, and
partial forest in Figure 4. Costs are fixed externally. -/
structure Instance (V : Type*) where
  E : Finset (Sym2 V)
  B : V → ℤ
  W : Finset V
  F : Finset (Sym2 V)

/-- The well-formed states of the connecting-tree problem. -/
def Valid {V : Type*} (I : Instance V) : Prop :=
  SimpleEdges I.E ∧ IsForest I.F ∧ Disjoint I.E I.F

/-- One pass through Steps 2–4 of Figure 4. The chosen edge and vertex are
mandatory whenever their respective test succeeds. The vertex test uses the
support before edge deletion and the bounds after the edge update. -/
noncomputable def Step {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (picked : Finset (Sym2 V)) (J : Instance V) : Prop := by
  classical
  exact ¬ IsSpanningTree I.F ∧ ∃ x : Sym2 V → ℝ,
    Basic I.E I.B I.W I.F x ∧ Optimal c I.E I.B I.W I.F x ∧
    let EStar := support I.E x
    picked ⊆ EStar ∧ picked.card ≤ 1 ∧
    (∀ e ∈ picked, x e = 1) ∧
    ((∃ e ∈ EStar, x e = 1) ↔ picked.Nonempty) ∧
    let B' : V → ℤ := fun v => I.B v - (degree picked v : ℤ)
    ∃ dropped : Finset V,
      dropped ⊆ I.W ∧ dropped.card ≤ 1 ∧
      (∀ v ∈ dropped, (degree EStar v : ℤ) ≤ B' v + 1) ∧
      ((∃ v ∈ I.W, (degree EStar v : ℤ) ≤ B' v + 1) ↔ dropped.Nonempty) ∧
      J.E = EStar \ picked ∧ J.B = B' ∧
      J.W = I.W \ dropped ∧ J.F = I.F ∪ picked

/-- A finite sequence of recursive calls, with its exact number of iterations. -/
inductive Chain {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : Instance V → ℕ → Prop where
  | nil (I : Instance V) : Chain c I 0
  | cons {I J : Instance V} {k : ℕ} {picked : Finset (Sym2 V)}
      (hstep : Step c I picked J) (htail : Chain c J k) : Chain c I (k + 1)

/-- Every possible terminating run of Figure 4. -/
inductive Returns {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) : Instance V → Finset (Sym2 V) → Prop where
  | done (I : Instance V) (h : IsSpanningTree I.F) : Returns c I ∅
  | next {I J : Instance V} {picked H : Finset (Sym2 V)}
      (hstep : Step c I picked J) (htail : Returns c J H) :
      Returns c I (picked ∪ H)

/-- Figure 4 at the initial bounded-degree spanning-tree instance. -/
def initial {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) : Instance V :=
  ⟨E, B, Finset.univ, ∅⟩

end BoundedDegreeST.PlusOne


