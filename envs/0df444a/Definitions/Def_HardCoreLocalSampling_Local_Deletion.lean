-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Deletion
-- name    : HardCoreLocalSampling_Local_Deletion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:51.03883+00:00
-- url     : https://prove2.me/theorems/e79da57a-d014-46f0-bd19-c0012817c71c
-- title:
--   Ordered deletion contexts, occupation odds, and the deletion computation tree
-- statement:
--   Let $G$ be a finite simple graph with linearly ordered vertices, $D$ a set of deleted vertices, and $v\notin D$. Deletion is represented by pinning every member of $D$ unoccupied and leaving other vertices unpinned. For $w_D$ the resulting compatible weight, the occupation odds in $H=G-D$ are
--
--   $$
--   R_{H}(v)=\frac{\sum_{I:v\in I}w_D(I)}{\sum_{I:v\notin I}w_D(I)}.
--   $$
--
--   List the neighbors of $v$ in $H$ in increasing label order as $u_1,\ldots,u_d$. The $i$th child subproblem is $(H_i,u_i)$ with $H_i=H-\{v,u_1,\ldots,u_{i-1}\}$. The degree of $u$ in $G-D$ is $|N_G(u)\setminus D|$.
--
--   The depth-$h$ *view* of $(H,v)$ is the preorder list of root degrees of the computation tree unfolded to depth $h$; nodes at depth $h$ report their degree and are not expanded. The view depends on $(G,D)$ only through the residual graph $H$, which is what makes a center computed from it independent of the history of a deletion context.
--
--   **Formalization Note** Finite sums and sorted neighbor sets are mathematical definitions, with no claimed implementation or lazy-access cost. A deleted query has odds zero. At positive fugacity the denominator is positive because the empty set contributes one, including on an empty residual graph.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §5, Lemma 6 and equation (1), printed pp.5–6 (PDF pp.6–7); computation tree, Lemma 9, printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_ConditionalLaw

namespace HardCoreLocalSampling.Local

/-! Ordered vertex deletions and occupation odds in §5, printed pp.5–6 / PDF pp.6–7,
and the shape of the deletion computation tree used in Lemma 9. These are mathematical
definitions; costs of lazy access appear only through the machine model. -/

section
variable {V : Type*} [Fintype V]

/-- Deleting a vertex is equivalent to conditioning it unoccupied. -/
noncomputable def deletionPinning (D : Finset V) : Pinning V := by
  classical
  exact fun v => if v ∈ D then .unoccupied else .unpinned

/-- `R_{G-D}(v)`: occupied versus unoccupied weight on the induced graph `G - D`.
For a deleted query this formula is zero; source queries are not deleted.
At positive fugacity the empty set makes the denominator positive. -/
noncomputable def deletionOdds (G : SimpleGraph V) (lam : ℝ) (D : Finset V) (v : V) : ℝ := by
  classical
  let w := conditionalWeight G lam (deletionPinning D)
  exact (∑ I : Finset V, if v ∈ I then w I else 0) /
    (∑ I : Finset V, if v ∉ I then w I else 0)

/-- Degree of `v` in the induced graph obtained by deleting `D`. -/
noncomputable def residualDegree (G : SimpleGraph V) (D : Finset V) (v : V) : ℕ := by
  classical
  exact (G.neighborFinset v \ D).card

/-- `G` has maximum degree at most `Delta`. -/
def MaxDegreeLE (G : SimpleGraph V) (Delta : ℕ) : Prop :=
  ∀ v, residualDegree G ∅ v ≤ Delta

end

section
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The neighbors of `v` in `G - D`, in increasing label order: `u_1, ..., u_d`. -/
noncomputable def orderedNeighbors (G : SimpleGraph V) (D : Finset V) (v : V) : List V := by
  classical
  exact (G.neighborFinset v \ D).sort (· ≤ ·)

/-- The deleted set of the `i`-th child: `D`, the parent `v`, and all earlier neighbors,
so that `H_i = H - {v, u_1, ..., u_{i-1}}` with `H = G - D`. -/
noncomputable def childDeleted (G : SimpleGraph V) (D : Finset V) (v : V)
    (i : Fin (orderedNeighbors G D v).length) : Finset V := by
  classical
  exact D ∪ insert v ((orderedNeighbors G D v).take i.val).toFinset

/-- The child contexts `(H_i, u_i)` in increasing label order. -/
noncomputable def childContexts (G : SimpleGraph V) (D : Finset V) (v : V) :
    List (Finset V × V) :=
  (List.finRange (orderedNeighbors G D v).length).map fun i =>
    (childDeleted G D v i, (orderedNeighbors G D v)[i.val])

/-- The depth-`h` unfolding of the deletion computation tree of `(G - D, v)`, written in
preorder as the list of the root degrees of the visited subproblems. Nodes at depth `h`
report their degree (so a genuine degree-zero terminal is seen before the cutoff) and are
not expanded. It depends on `(G, D)` only through the residual graph `G - D`. -/
noncomputable def deletionView (G : SimpleGraph V) : ℕ → Finset V → V → List ℕ
  | 0, D, v => [residualDegree G D v]
  | h + 1, D, v => residualDegree G D v ::
      (childContexts G D v).flatMap fun c => deletionView G h c.1 c.2

end

end HardCoreLocalSampling.Local


