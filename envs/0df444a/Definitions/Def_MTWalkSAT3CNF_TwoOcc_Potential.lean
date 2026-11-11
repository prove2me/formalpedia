-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential
-- name    : MTWalkSAT3CNF_TwoOcc_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:11.562862+00:00
-- url     : https://prove2.me/theorems/89a3e6f1-0b77-463c-82bc-0d1c87169652
-- title:
--   The clause multigraph outside $A$, defect and boundary trees, and the potential $\Phi$
-- statement:
--   In the setting of §3.2 ($\Delta(F)\le2$, and every variable occurring twice has one positive and one negative occurrence) the clauses are the vertices of a multigraph: a variable occurring twice is an edge between its two (distinct) clauses, a variable occurring once is a half-edge. Fix an assignment $\sigma$ and put $A=\{C: s(C)\ge 2\}$. Delete $A$; the **components** are the connected components of what remains. An occurrence at a clause outside $A$ is a **boundary occurrence** when it is a half-edge or its variable's other occurrence lies in $A$.
--
--   For a component $K$ write $q=|K|$, $e$ for the number of edges inside $K$, $u$ for the number of unsatisfied clauses of $K$ and $b$ for the number of true boundary occurrences at clauses of $K$. $K$ is a tree when $e=q-1$ and unicyclic when $e=q$. A **defect tree** is a tree with $u=1$, $b=0$, rooted at its unsatisfied clause; a **boundary tree** is a tree with $u=0$, $b=1$, rooted at the clause carrying its true boundary occurrence. For a rooted tree,
--
--   $$W_T(r)=\sum_{v\in V(T)}2^{-d_T(r,v)},$$
--
--   and the global potential of display (1) is
--
--   $$\Phi(\sigma)=\sum_{T \text{ defect tree}}W_T(r_T)+\frac14\sum_{T\text{ boundary tree}}W_T(\rho_T).$$
--
--   Every other component and every clause of $A$ contributes $0$.
--
--   **Formalization Note** The definitions are total. The graph outside $A$ is a simple graph on clause indices (distinct clauses outside $A$ sharing a variable); edges are counted separately, as variables with occurrences in two distinct clauses of $K$, so parallel edges count twice. $\Phi$ is written as a sum over clauses that are roots of their component's tree: a clause $r$ with $s(r)=0$ whose component is a defect tree, and $1/4$ times the sum over clauses $r\notin A$ carrying a true boundary occurrence whose component is a boundary tree. A component of neither type contributes $0$ whatever its shape. Distances are taken in the graph outside $A$, which equals the distance inside the component.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, proof of Theorem 3.4, pp. 13–14 (Lemma 3.5, display (1)). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Formula

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The clause multigraph outside `A`, defect and boundary trees, and the global potential `Φ`

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), §3.2, proof of Theorem 3.4,
pp. 13–14 (Lemma 3.5 and display (1)).

The paper's setting (used by every theorem stated with these objects): `Δ(F) ≤ 2` and every
variable occurring twice has one positive and one negative occurrence. Then the clauses are the
vertices of a multigraph whose edges are the variables occurring twice (joining their two,
necessarily distinct, clauses) and whose half-edges are the variables occurring once. The
definitions below are total: they make sense for every formula and assignment.

Conventions.
* `s(C)` is `numTrue σ C`; `A = {C : s(C) ≥ 2}` (`InA`).
* After deleting `A`, two clauses outside `A` are adjacent when they share a variable
  (`outsideGraph`, a simple graph; parallel edges of the multigraph are counted separately by
  `edgeCount`). The component `K(r)` of a clause `r ∉ A` is the set of clauses outside `A`
  reachable from `r`.
* For a set `K` of clauses: `q = |K|`; `e = edgeCount F K`, the number of variables having
  occurrences in two distinct clauses of `K` (the multigraph edges inside `K`);
  `u = unsatCount`, the number of unsatisfied clauses in `K`; `b = trueBoundaryCount`, the
  number of true boundary occurrences at clauses of `K`. An occurrence at a clause outside `A`
  is a boundary occurrence (`IsBoundary`) when every other occurrence of its variable lies in a
  clause of `A`: a half-edge, or an edge to a deleted clause.
* For a connected component, "tree" is `e + 1 = q` and "unicyclic" is `e = q`
  (`IsTreeComp`, `IsUnicyclicComp`), the multigraph meanings for a connected multigraph.
* `W_T(r) = Σ_{v ∈ V(T)} 2^{-d_T(r,v)}` (`distWeight`; distances in the graph outside `A`
  equal distances inside the component).
* `Φ(σ)` (display (1)) is the sum of `W_T(r_T)` over defect trees (tree, `u = 1`, `b = 0`,
  rooted at the unsatisfied clause) plus `1/4` times the sum of `W_T(ρ_T)` over boundary trees
  (tree, `u = 0`, `b = 1`, rooted at the clause carrying the true boundary occurrence). Every
  other component, and every clause in `A`, contributes `0`. The sums are written over roots:
  a clause contributes when it is the root of its component's tree.
-/

namespace MTWalkSAT3CNF.TwoOcc

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- `C_i ∈ A`: the clause has at least two true literal occurrences under `σ`. -/
def InA (F : Formula V m) (σ : V → Bool) (i : Fin m) : Prop := 2 ≤ numTrue σ (F i)

/-- The graph on clauses after deleting `A`: distinct clauses outside `A` sharing a variable. -/
def outsideGraph (F : Formula V m) (σ : V → Bool) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ ¬ InA F σ i ∧ ¬ InA F σ j ∧ ∃ p q : Fin 3, (F i).var p = (F j).var q
  symm := ⟨fun _ _ ⟨hne, hi, hj, p, q, h⟩ => ⟨hne.symm, hj, hi, q, p, h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The component `K(r)` of the graph outside `A` containing `r` (empty if `r ∈ A`). -/
noncomputable def comp (F : Formula V m) (σ : V → Bool) (r : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun v => ¬ InA F σ r ∧ (outsideGraph F σ).Reachable r v)

/-- `e`: the number of multigraph edges inside `K`, i.e. of variables occurring in two distinct
clauses of `K`. -/
noncomputable def edgeCount (F : Formula V m) (K : Finset (Fin m)) : ℕ :=
  (Finset.univ.filter (fun x : V => ∃ i ∈ K, ∃ j ∈ K, i ≠ j ∧
    (∃ p : Fin 3, (F i).var p = x) ∧ (∃ q : Fin 3, (F j).var q = x))).card

/-- `u`: the number of unsatisfied clauses in `K`. -/
noncomputable def unsatCount (F : Formula V m) (σ : V → Bool) (K : Finset (Fin m)) : ℕ :=
  (K.filter (fun i => numTrue σ (F i) = 0)).card

/-- The occurrence at position `p` of clause `i` is a boundary occurrence: every other
occurrence of its variable lies in a clause of `A` (vacuous for a half-edge). -/
def IsBoundary (F : Formula V m) (σ : V → Bool) (i : Fin m) (p : Fin 3) : Prop :=
  ∀ (j : Fin m) (q : Fin 3), (j, q) ≠ (i, p) → (F j).var q = (F i).var p → InA F σ j

/-- `b`: the number of true boundary occurrences at clauses of `K`. -/
noncomputable def trueBoundaryCount (F : Formula V m) (σ : V → Bool) (K : Finset (Fin m)) : ℕ :=
  ((K ×ˢ (Finset.univ : Finset (Fin 3))).filter
    (fun ip => LitTrue σ (F ip.1) ip.2 ∧ IsBoundary F σ ip.1 ip.2)).card

/-- A connected component with `e = q − 1` (a tree, for a connected multigraph). -/
def IsTreeComp (F : Formula V m) (K : Finset (Fin m)) : Prop := edgeCount F K + 1 = K.card

/-- A connected component with `e = q` (unicyclic, for a connected multigraph). -/
def IsUnicyclicComp (F : Formula V m) (K : Finset (Fin m)) : Prop := edgeCount F K = K.card

/-- A defect tree: a tree with one unsatisfied clause and no true boundary occurrence. -/
def IsDefectTree (F : Formula V m) (σ : V → Bool) (K : Finset (Fin m)) : Prop :=
  IsTreeComp F K ∧ unsatCount F σ K = 1 ∧ trueBoundaryCount F σ K = 0

/-- A boundary tree: a tree with no unsatisfied clause and one true boundary occurrence. -/
def IsBoundaryTree (F : Formula V m) (σ : V → Bool) (K : Finset (Fin m)) : Prop :=
  IsTreeComp F K ∧ unsatCount F σ K = 0 ∧ trueBoundaryCount F σ K = 1

/-- `Σ_{v ∈ s} 2^{-d_G(r,v)}`. For a tree `T` and `s = V(T)` this is `W_T(r)`. -/
noncomputable def distWeight {W : Type*} (G : SimpleGraph W) (s : Finset W) (r : W) : ℝ :=
  ∑ v ∈ s, (1 / 2 : ℝ) ^ G.dist r v

/-- `W_T(r) = Σ_{v ∈ V(T)} 2^{-d_T(r,v)}` for a graph `T` on a finite vertex type. -/
noncomputable def treeWeight {W : Type*} [Fintype W] (T : SimpleGraph W) (r : W) : ℝ :=
  distWeight T Finset.univ r

/-- `W_{K(r)}(r)`: the weight of the component of `r` outside `A`, rooted at `r`. -/
noncomputable def compWeight (F : Formula V m) (σ : V → Bool) (r : Fin m) : ℝ :=
  distWeight (outsideGraph F σ) (comp F σ r) r

/-- The global potential `Φ(σ)` of display (1): the sum of `W_T(r_T)` over defect trees rooted
at their unsatisfied clause, plus `1/4` times the sum of `W_T(ρ_T)` over boundary trees rooted at
the clause carrying their true boundary occurrence; all other components and `A` contribute 0. -/
noncomputable def potential (F : Formula V m) (σ : V → Bool) : ℝ :=
  (∑ r : Fin m,
      if numTrue σ (F r) = 0 ∧ IsDefectTree F σ (comp F σ r) then compWeight F σ r else 0) +
    (1 / 4 : ℝ) * ∑ r : Fin m,
      if ¬ InA F σ r ∧ IsBoundaryTree F σ (comp F σ r) ∧
          (∃ p : Fin 3, LitTrue σ (F r) p ∧ IsBoundary F σ r p)
        then compWeight F σ r else 0

end MTWalkSAT3CNF.TwoOcc


