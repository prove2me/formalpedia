-- Prove2me | Definitions.Def_BimatrixStableSet_LabeledPolytope
-- name    : BimatrixStableSet_LabeledPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:09.044997+00:00
-- url     : https://prove2.me/theorems/df5069f4-304c-495c-a797-c3e35a23c48a
-- title:
--   Labeled polytopes (Definition 2), completely labeled points, the index (Definition 3) and the index of an equilibrium
-- statement:
--   This module fixes the objects of §4 of the paper.
--
--   1. **Labeled polytope** (Definition 2, p.9). A simple $d$-polytope
--
--   $$
--   Z=\{z\in\mathbb R^d\mid -z\le0,\ Cz\le\mathbf 1\}\qquad(5)
--   $$
--
--   without redundant inequalities. The inequality $-z_i\le0$ has label $i$, and the $j$-th inequality of $Cz\le\mathbf 1$ has a given label $\ell(j)\in[d]$.
--   2. **Completely labeled points** (p.9). A point of $Z$ is completely labeled if it has all labels in $[d]$, and $h$-almost completely labeled if it has all labels in $[d]\setminus\{h\}$.
--   3. **Index** (Definition 3, p.10). If $a_i$ is the normal vector of the binding inequality with label $i$, then
--
--   $$
--   \mathrm{index}(z)=(-1)^{d+1}\,\mathrm{sign}\,|a_1\cdots a_d|.\qquad(7)
--   $$
--
--   4. **Almost completely labeled paths** (proof of Theorem 1, p.9). The subgraph of the graph of $Z$ whose edges are those all of whose points are $h$-almost completely labeled, and pairs of degree-one vertices joined by a walk in it.
--   5. **Index of an equilibrium** (pp.9–11). The index (7) of $z=(x,y)$ for the matrix $C$ of display (6), with rows $(0\ A)$ and $(B^\top\ 0)$ and labels $\ell(j)=j$.
--
--   The index is what makes equilibria come in pairs and drives the stable-set bound.
--
--   **Formalization Note** The index is defined at every point. A row of the matrix $|a_1\cdots a_d|$ is $0$ when no binding inequality has that label, so the index is then $0$. At the points where the paper uses it, each label is carried by exactly one binding inequality. The index reads only binding rows, so the index of an equilibrium is defined also when $P$ or $Q$ has never-binding redundant rows, which Lemma 3(c) allows and Definition 2 does not. A proved verification lemma gives $\mathrm{index}(0)=-1$ for every $d$.
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Definition 2, p.9; displays (5), (6), p.9; Definition 3 and display (7), p.10; p.11

import Mathlib
import Definitions.Def_BimatrixStableSet_Polyhedra

open Matrix

namespace BimatrixStableSet

variable {d k : ℕ}

/-- The system `-z ≤ 0, Cz ≤ 1` of display (5), p.9 (Ickstadt, Theobald, von Stengel,
arXiv:2411.12385v3). The rows `Sum.inl i` are the inequalities `-zᵢ ≤ 0` and the rows `Sum.inr j` are
the inequalities `(Cz)ⱼ ≤ 1`. -/
def labeledSystem (C : Matrix (Fin k) (Fin d) ℝ) : System (Fin d ⊕ Fin k) d :=
  ⟨Matrix.fromRows (-1) C, Sum.elim 0 1⟩

/-- The label of a row of (5), Definition 2: `-zᵢ ≤ 0` has label `i`, and `(Cz)ⱼ ≤ 1` has label
`ℓ(j)`. -/
def rowLabel (ℓ : Fin k → Fin d) : Fin d ⊕ Fin k → Fin d := Sum.elim id ℓ

/-- Definition 2, p.9: the set (5) is a simple `d`-polytope and none of its inequalities is
redundant. The labeling `ℓ` is free data.

**Formalization Note.** Definition 2 says "`C` without redundant inequalities" and the proof of
Theorem 1 says "no inequality is redundant". The two readings agree, because the inequalities
`-zᵢ ≤ 0` are never redundant in a simple `d`-polytope with `0` as a vertex. -/
def IsLabeledPolytope (C : Matrix (Fin k) (Fin d) ℝ) : Prop :=
  (labeledSystem C).IsSimplePolytopeOfDim (labeledSystem C).carrier d ∧
    ∀ r, ¬ (labeledSystem C).IsRedundant r

/-- The point `z` has label `h`: some binding inequality has label `h`. -/
def HasLabel (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (z : Fin d → ℝ) (h : Fin d) :
    Prop :=
  ∃ r, rowLabel ℓ r = h ∧ (labeledSystem C).IsBinding z r

/-- A point of `Z` that has all labels in `[d]`, Definition 2, p.9. -/
def IsCompletelyLabeled (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (z : Fin d → ℝ) : Prop :=
  z ∈ (labeledSystem C).carrier ∧ ∀ h, HasLabel C ℓ z h

/-- A point of `Z` that has all labels in `[d] \ {h}`, Definition 2, p.9. -/
def IsAlmostCompletelyLabeled (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (h : Fin d)
    (z : Fin d → ℝ) : Prop :=
  z ∈ (labeledSystem C).carrier ∧ ∀ g, g ≠ h → HasLabel C ℓ z g

open Classical in
/-- The matrix `|a₁ ⋯ a_d|` of Definition 3, p.10: row `i` is the normal vector of the binding
inequality with label `i`.

**Formalization Note.** Defined at every point of `ℝᵈ`. If no binding inequality has label `i`, then
row `i` is `0`, so the determinant vanishes. If several have label `i`, one is chosen. At a
completely labeled vertex of a labeled polytope and at an equilibrium of a non-degenerate game, each
label is carried by exactly one binding inequality (Lemma 3(d)), so there is no choice. No
irredundancy is assumed here: a never-binding row is never looked at. -/
noncomputable def normalMatrix (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (z : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i =>
    if h : ∃ r, rowLabel ℓ r = i ∧ (labeledSystem C).IsBinding z r then
      (labeledSystem C).C h.choose
    else 0

/-- The index of display (7), p.10: `index(z) = (-1)^(d+1) sign |a₁ ⋯ a_d|`. -/
noncomputable def index (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (z : Fin d → ℝ) : ℤ :=
  (-1) ^ (d + 1) * (SignType.sign (normalMatrix C ℓ z).det : ℤ)

/-- The subgraph of the graph of `Z` formed by the `h`-almost completely labeled points (proof of
Theorem 1, p.9): two vertices of `Z` are joined when they are the endpoints of an edge all of whose
points are `h`-almost completely labeled. -/
def almostGraph (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (h : Fin d) :
    SimpleGraph ((labeledSystem C).vertices (labeledSystem C).carrier) where
  Adj u v := (u : Fin d → ℝ) ≠ v ∧ ∃ E, (labeledSystem C).IsEdgeOf E (labeledSystem C).carrier ∧
    (u : Fin d → ℝ) ∈ E ∧ (v : Fin d → ℝ) ∈ E ∧ ∀ z ∈ E, IsAlmostCompletelyLabeled C ℓ h z
  symm := ⟨fun _ _ a => ⟨a.1.symm, a.2.imp fun _ e => ⟨e.1, e.2.2.1, e.2.1, e.2.2.2⟩⟩⟩
  loopless := ⟨fun _ a => a.1 rfl⟩

/-- `z` and `w` are the two endpoints of an `h`-almost completely labeled path: two different vertices
of degree one that are joined by a walk in `almostGraph`. By the proof of Theorem 1 the graph
`almostGraph` has maximal degree two, so its components with a degree-one vertex are the paths. -/
def IsAlmostPathEnds (C : Matrix (Fin k) (Fin d) ℝ) (ℓ : Fin k → Fin d) (h : Fin d)
    (z w : (labeledSystem C).vertices (labeledSystem C).carrier) : Prop :=
  z ≠ w ∧ (almostGraph C ℓ h).Reachable z w ∧
    ((almostGraph C ℓ h).neighborSet z).encard = 1 ∧ ((almostGraph C ℓ h).neighborSet w).encard = 1

/-- The matrix `C` of display (6), p.9, in the coordinates `z = (x, y)` of `ℝ^(m+n)`: the first `m`
rows are `(0 A)` and the last `n` rows are `(B⊤ 0)`. Its rows have the labels `ℓ(j) = j`. -/
def equilibriumMatrix {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 A Bᵀ 0)

/-- The index of an equilibrium `(x, y)`: display (7) for `z = (x, y)` in `Z = P × Q` with `C` and
`ℓ` as in display (6), §4–§5, pp.9–11. -/
noncomputable def equilibriumIndex {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ)
    (y : Fin n → ℝ) : ℤ :=
  index (equilibriumMatrix A B) id (Fin.append x y)

end BimatrixStableSet


