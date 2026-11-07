-- Prove2me | Definitions.Def_DisjointPathsDAG_Regional
-- name    : DisjointPathsDAG_Regional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:36.218381+00:00
-- url     : https://prove2.me/theorems/e93a56ab-1a0e-4e15-a42c-348e7b35ffd4
-- title:
--   Regional instances, regional polynomials, monotone cuts and feasible bijections
-- statement:
--   The setting of Section 3. $G$ is a directed or undirected graph with vertex set $V$ and edges $0,\dots,M-1$, edge $e$ with endpoints $(x_e,y_e)$. An **arc** is an edge with an orientation, $x_e\to y_e$ or $y_e\to x_e$, and for each label $i\in[k]$, $H_i$ is a set of arcs (for directed $G$ only the forward orientations occur).
--
--   A **regional instance** consists of $R\subseteq V$, a label set $I\subseteq[k]$ and terminals $a_i,b_i\in R$ for $i\in I$. Its **solutions** are the tuples $(P_i)_{i\in I}$ of pairwise vertex-disjoint paths, $P_i$ an $a_i$–$b_i$ path in $H_i[R]$ (arcs of $H_i$ with both ends in $R$; for $a_i=b_i$ the zero-edge path occupies $a_i$). The **regional polynomial** is
--   $$F_R=\sum_{(P_i)_{i\in I}}\prod_{i\in I}\prod_{e\in E(P_i)}x_e,$$
--   $e$ running over the edges underlying the arcs.
--
--   A partition $(L,U)$ of $R$ is a **monotone cut** if for every $i\in I$ no path of $H_i[R]$ contains two arcs over edges between $L$ and $U$ (the **cut edges**). A label is **active** if $a_i,b_i$ lie on different sides; $J$ is the set of active labels and $j=|J|$. For a set $B$ of $j$ cut edges, a bijection $\sigma:J\to B$ is **feasible** if, for every $i\in J$, the edge $\sigma(i)$ oriented from the side of $a_i$ to the side of $b_i$ is an arc $(u_i,v_i)$ of $H_i$. The **low child** under $\sigma$ is the regional instance on $L$ with the pairs $(a_i,u_i)$ or $(v_i,b_i)$ that lie in $L$ for $i\in J$ and the inactive labels with terminals in $L$; the **high child** on $U$ is symmetric. $Q(z)$ is $F_R$ with every noncut variable fixed to $\xi_e$.
--
--   These objects drive the reporting algorithm: a nonzero coefficient of $Q$ splits a solution at the cut.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 3, pp.7–8

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-!
# Regional instances, monotone cuts and feasible bijections (Section 3)

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 3, pp.7–8.

"Throughout this section, R = F is a field with unit-cost operations and uniform sampling, G is a
directed or undirected graph with vertex set V and edge set E, and for each label i ∈ [k], Hi is a
directed graph on V whose arcs are orientations of edges of G; for directed G, the only orientation of
an edge is its own direction, so Hi ⊆ G. Every edge e of G carries one variable xe, shared by all its
orientations and all graphs Hi."

"A regional instance consists of a set R ⊆ V, a label set I ⊆ [k], and terminals ai, bi ∈ R for
i ∈ I. Its solutions are the tuples (Pi)i∈I of pairwise vertex-disjoint paths such that Pi is an ai–bi
path in Hi[R]; a path contains its endpoints, so for ai = bi the zero-edge path occupies ai."

"Monotone cuts. A partition of R into a low side L and a high side U is a monotone cut of a regional
instance if, for every i ∈ I, no path of Hi[R] contains two edges between L and U. The edges of G[R]
between L and U are the cut edges; their variables are the cut variables, written ze, and all other
variables of FR are noncut variables. A label i ∈ I is active if ai and bi lie on different sides. Let
J be the set of active labels and put j := |J|."

"For a set B of j cut edges, a bijection σ: J → B is feasible if, for every i ∈ J, the edge σ(i),
oriented from the side of ai to the side of bi, is an arc (ui, vi) of Hi whose underlying edge is σ(i).
Under a feasible σ, each active label i has the pair (ai, ui) on the side of ai and the pair (vi, bi) on
the side of bi. The low child is the regional instance on L whose pairs are these pairs inside L for
i ∈ J together with the pairs of the inactive labels with terminals in L; the high child on U is defined
symmetrically. Let FσL and FσU be their polynomials."

**Formalization Note** This module bundles the Section 3 objects, which depend on one another.
* The graph `G` has vertex type `V` (finite) and edges `Fin M`; `ends e = (x, y)` lists the two
  endpoints of `e`. An **arc** is a pair `(e, b)`: `b = true` orients `e` from `x` to `y`, `b = false`
  from `y` to `x`. Each `H i` is a set of arcs. This one encoding covers directed `G` (every `H i`
  contains only arcs `(e, true)`) and undirected `G` (both orientations may occur).
* A path in `H i[R]` is a list of arcs of `H i` whose endpoints lie in `R`, consecutive, repeating no
  vertex; the empty list is the zero-edge path at its start. The monomial of a solution multiplies the
  variables `X e` of the underlying edges of its arcs.
* A solution of a regional instance is indexed by the labels in `I` (`P : ρ.I → List (Fin M × Bool)`);
  terminals of labels outside `I` are ignored. The regional polynomial is a sum over the finite set of
  solutions (paths have at most `|V|` arcs).
* The orientation of `σ(i)` "from the side of `aᵢ`" is the arc `(σ i, b)` with `b` true iff the first
  endpoint of `σ i` lies on the side of `aᵢ`; for a cut edge this is the unique such orientation.
-/

variable {V : Type} [Fintype V] [DecidableEq V] {M k : ℕ}

/-- The tail of an arc. -/
def arcTail (ends : Fin M → V × V) (a : Fin M × Bool) : V :=
  if a.2 then (ends a.1).1 else (ends a.1).2

/-- The head of an arc. -/
def arcHead (ends : Fin M → V × V) (a : Fin M × Bool) : V :=
  if a.2 then (ends a.1).2 else (ends a.1).1

/-- A regional instance: a vertex set `R`, a label set `I`, terminals `a i`, `b i` (used for
`i ∈ I`). -/
structure RegInst (V : Type) (k : ℕ) where
  R : Finset V
  I : Finset (Fin k)
  a : Fin k → V
  b : Fin k → V

/-- The terminals of every label in `I` lie in `R`. -/
def RegInst.WF (ρ : RegInst V k) : Prop :=
  ∀ i ∈ ρ.I, ρ.a i ∈ ρ.R ∧ ρ.b i ∈ ρ.R

/-- `p` is an `x`–`y` path in `Hi[R]`. -/
def IsRegPath (ends : Fin M → V × V) (Hi : Set (Fin M × Bool)) (R : Finset V) (x y : V)
    (p : List (Fin M × Bool)) : Prop :=
  IsPathOf (arcTail ends) (arcHead ends)
    (fun c => c ∈ Hi ∧ arcTail ends c ∈ R ∧ arcHead ends c ∈ R) x y p

/-- A solution of the regional instance `ρ`: for every `i ∈ I` an `aᵢ`–`bᵢ` path in `Hᵢ[R]`, pairwise
vertex-disjoint. -/
def RegInst.IsSol (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k)
    (P : ρ.I → List (Fin M × Bool)) : Prop :=
  (∀ i : ρ.I, IsRegPath ends (H i) ρ.R (ρ.a i) (ρ.b i) (P i)) ∧
    ∀ i j : ρ.I, i ≠ j → Disjoint (walkVerts (arcHead ends) (ρ.a i) (P i)).toFinset
      (walkVerts (arcHead ends) (ρ.a j) (P j)).toFinset

/-- The finite set of solutions of `ρ`. -/
noncomputable def RegInst.sols (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool))
    (ρ : RegInst V k) : Finset (ρ.I → List (Fin M × Bool)) := by
  classical
  exact (Fintype.piFinset fun _ : ρ.I => listsUpTo (Fin M × Bool) (Fintype.card V)).filter
    (ρ.IsSol ends H)

/-- The regional polynomial `F_R = ∑_{(Pᵢ)} ∏_{i ∈ I} ∏_{e ∈ E(Pᵢ)} X e` over the ring `F`, the sum
over the solutions of `ρ`, `e` running over the edges underlying the arcs. -/
noncomputable def regionalPoly (F : Type) [CommRing F] (ends : Fin M → V × V)
    (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k) : MvPolynomial (Fin M) F :=
  ∑ P ∈ ρ.sols ends H, ∏ i, ((P i).map fun c => (X c.1 : MvPolynomial (Fin M) F)).prod

/-- The exponent vector of the monomial of a solution: the number of its arcs over each edge. -/
noncomputable def solExp (ρ : RegInst V k) (P : ρ.I → List (Fin M × Bool)) : Fin M →₀ ℕ :=
  ∑ i, ((P i).map fun c => Finsupp.single c.1 1).sum

/-- The monomial `z^B` of an edge set `B`. -/
noncomputable def setExp (B : Finset (Fin M)) : Fin M →₀ ℕ :=
  ∑ e ∈ B, Finsupp.single e 1

/-- `e` is an edge between `L` and `U` (one endpoint in each). -/
def IsCutEdge (ends : Fin M → V × V) (L U : Finset V) (e : Fin M) : Prop :=
  ((ends e).1 ∈ L ∧ (ends e).2 ∈ U) ∨ ((ends e).1 ∈ U ∧ (ends e).2 ∈ L)

/-- The cut edges: the edges between `L` and `U`. -/
noncomputable def cutEdges (ends : Fin M → V × V) (L U : Finset V) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (IsCutEdge ends L U)

/-- `(L, U)` is a monotone cut of `ρ`: a partition of `R` such that, for every `i ∈ I`, no path of
`Hᵢ[R]` contains two (distinct) arcs over edges between `L` and `U`. -/
def IsMonotoneCut (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k)
    (L U : Finset V) : Prop :=
  L ∪ U = ρ.R ∧ Disjoint L U ∧
    ∀ i ∈ ρ.I, ∀ (x y : V) (p : List (Fin M × Bool)), IsRegPath ends (H i) ρ.R x y p →
      ∀ c₁ ∈ p, ∀ c₂ ∈ p, IsCutEdge ends L U c₁.1 → IsCutEdge ends L U c₂.1 → c₁ = c₂

/-- The active labels: the labels of `I` whose terminals lie on different sides. -/
noncomputable def activeSet (ρ : RegInst V k) (L : Finset V) : Finset (Fin k) := by
  classical
  exact ρ.I.filter fun i => ¬ (ρ.a i ∈ L ↔ ρ.b i ∈ L)

/-- The orientation of `σ i` from the side of `aᵢ`: the arc `(σ i, b)` with `b` true iff the first
endpoint of `σ i` lies on the same side as `aᵢ`. -/
noncomputable def orientedArc (ends : Fin M → V × V) (ρ : RegInst V k) (L : Finset V)
    {J : Finset (Fin k)} {B : Finset (Fin M)} (σ : J ≃ B) (i : J) : Fin M × Bool := by
  classical
  exact ((σ i : Fin M), decide ((ends (σ i)).1 ∈ L ↔ ρ.a i ∈ L))

/-- `σ : J ≃ B` is feasible: for every active label `i`, `σ(i)` oriented from the side of `aᵢ` to the
side of `bᵢ` is an arc of `Hᵢ`. -/
def IsFeasibleBij (ends : Fin M → V × V) (H : Fin k → Set (Fin M × Bool)) (ρ : RegInst V k)
    (L : Finset V) {B : Finset (Fin M)} (σ : activeSet ρ L ≃ B) : Prop :=
  ∀ i : activeSet ρ L, orientedArc ends ρ L σ i ∈ H (i : Fin k)

/-- The low child under `σ` (on `L`): labels `J` and the inactive labels with terminals in `L`; for
an active label the pair `(aᵢ, uᵢ)` if `aᵢ ∈ L`, else `(vᵢ, bᵢ)`, where `(uᵢ, vᵢ)` is the arc of
`σ(i)`. -/
noncomputable def lowChild (ends : Fin M → V × V) (ρ : RegInst V k) (L : Finset V)
    {B : Finset (Fin M)} (σ : activeSet ρ L ≃ B) : RegInst V k := by
  classical
  exact
    { R := L
      I := activeSet ρ L ∪ (ρ.I \ activeSet ρ L).filter fun i => ρ.a i ∈ L
      a := fun i => if h : i ∈ activeSet ρ L then
          (if ρ.a i ∈ L then ρ.a i else arcHead ends (orientedArc ends ρ L σ ⟨i, h⟩)) else ρ.a i
      b := fun i => if h : i ∈ activeSet ρ L then
          (if ρ.a i ∈ L then arcTail ends (orientedArc ends ρ L σ ⟨i, h⟩) else ρ.b i) else ρ.b i }

/-- The high child under `σ` (on `U`), symmetric to `lowChild`. -/
noncomputable def highChild (ends : Fin M → V × V) (ρ : RegInst V k) (L U : Finset V)
    {B : Finset (Fin M)} (σ : activeSet ρ L ≃ B) : RegInst V k := by
  classical
  exact
    { R := U
      I := activeSet ρ L ∪ (ρ.I \ activeSet ρ L).filter fun i => ρ.a i ∈ U
      a := fun i => if h : i ∈ activeSet ρ L then
          (if ρ.a i ∈ U then ρ.a i else arcHead ends (orientedArc ends ρ L σ ⟨i, h⟩)) else ρ.a i
      b := fun i => if h : i ∈ activeSet ρ L then
          (if ρ.a i ∈ U then arcTail ends (orientedArc ends ρ L σ ⟨i, h⟩) else ρ.b i) else ρ.b i }

/-- `Q(z)`: the regional polynomial with the cut variables left free and every noncut variable `e`
fixed to `ξ e`. -/
noncomputable def cutRestrict {F : Type} [CommRing F] (ends : Fin M → V × V) (L U : Finset V)
    (ξ : Fin M → F) (p : MvPolynomial (Fin M) F) : MvPolynomial (Fin M) F := by
  classical
  exact aeval (fun e => if e ∈ cutEdges ends L U then X e else C (ξ e)) p

end DisjointPathsDAG


