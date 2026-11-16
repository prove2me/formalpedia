-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_Supplement_JunctionTree
-- name    : MinDilationTree_Sublinear_Supplement_JunctionTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:54:32.262239+00:00
-- url     : https://prove2.me/theorems/0a83e160-ae40-40fb-acf3-d58a604f0329
-- title:
--   Partitions, junction trees, spines, nerves and buffers
-- statement:
--   Fix $S$, a Delaunay triangulation $D$, $\Lambda$ and $r$, and a polygon $P$.
--
--   1. A finite family of weakly simple polygons $N_1,\ldots,N_k$ is a **partition** of $P$ (footnote 4) if their union is $P$ and, for every $\varepsilon>0$, their vertices can be moved by less than $\varepsilon$, staying in $P$, so that they become pairwise disjoint weakly simple polygons. Its **intersection graph** joins two pieces that intersect.
--   2. An **$(\alpha,\beta,\gamma)$-junction tree** of $P$ (Definition 11) is a pair of finite lists $\mathcal J$ (junctions) and $\mathcal F$ (faces) of weakly simple polygons such that: $\mathcal J\cup\mathcal F$ is a partition of $P$ whose intersection graph is a tree; distinct junctions are disjoint and distinct faces are disjoint; every junction has geodesic diameter at most $\alpha$; any two points of distinct junctions are at geodesic distance $d_P\ge\beta$; every face has geodesic diameter at most $\gamma$.
--   3. Following Definition 13, a **junction tree of $P\in\mathcal P_r$** of an $n$-point set is any $(18\Lambda r,\ \tfrac23\Lambda^2 r,\ (54\Lambda^2\log_2 n)\,r)$-junction tree of $P$.
--   4. **Spines and nerves** (Definition 14): a $P$-spine is a connected component of $\bigcup\mathcal P_{r/\Lambda}$ contained in $P$; for a face $F$, the $F$-spines $\operatorname{spines}(F)$ are the connected components of $\bigcup\mathcal P_{r/\Lambda}\cap F$, and the $F$-nerves those of $\bigcup\mathcal P_{r/\Lambda^2}\cap F$ ($P$-nerves: $\cap P$).
--   5. $\operatorname{junc}(F)$ is the set of junctions intersecting $F$, and the **$z$-buffer** $B_z(F)$ is the set of points of $F$ within geodesic distance $d_P$ at most $z$ of some junction of $\operatorname{junc}(F)$ (Definition 15).
--
--   These are the structures on which the comb obstruction (Theorem 18), good cuts (Lemma 23) and consistent sequences (Theorem 29) are built.
--
--   **Formalization Note** "No two junctions share a boundary" is encoded as disjointness: pieces of a partition meet only along boundaries. Geodesic diameters are measured inside the piece itself, the junction separation and the buffer by $d_P$. The logarithm has base 2. A junction tree is raw data (two lists of walks); its properties are the predicate, not fields.
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 8 (PDF p. 9), Definition 8 and footnote 4; p. 9 (PDF p. 10), Definition 11; p. 10 (PDF p. 11), Definitions 13 and 14; p. 11 (PDF p. 12), line 377 and Definition 15

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Support

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- The union of the closed polygons of a finite family of pieces. -/
def piecesUnion (L : List BoundaryWalk) : Set Plane :=
  {x | ∃ w ∈ L, x ∈ w.region}

/-- Footnote 4, p.8 (PDF 9): the pieces (weakly simple polygons) form a partition of `P`: their
union is `P`, and for every `ε > 0` their vertices can be moved by less than `ε`, staying in `P`,
so that they become pairwise disjoint weakly simple polygons. -/
def IsPartition (P : Set Plane) (L : List BoundaryWalk) : Prop :=
  piecesUnion L = P ∧ (∀ w ∈ L, w.IsWeaklySimple) ∧
    ∀ ε : ℝ, 0 < ε → ∃ Q : Fin L.length → BoundaryWalk,
      (∀ i : Fin L.length, (Q i).IsWeaklySimple ∧ (Q i).m = (L.get i).m ∧
        (∀ j : Fin (Q i).m, (Q i).vertex j ∈ P) ∧
        ∀ j : ℕ, j < (Q i).m → dist ((Q i).at j) ((L.get i).at j) < ε) ∧
      ∀ i j : Fin L.length, i ≠ j → Disjoint (Q i).region (Q j).region

/-- The intersection graph of a finite family of pieces. -/
def intersectionGraph (L : List BoundaryWalk) : SimpleGraph (Fin L.length) where
  Adj i j := i ≠ j ∧ ((L.get i).region ∩ (L.get j).region).Nonempty
  symm := ⟨fun i j h => ⟨Ne.symm h.1, by simpa [Set.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A finite pair `(J, F)` of lists of polygons: junctions and faces. Its defining properties are
the predicate `IsJunctionTree`, not fields. -/
structure JunctionTreeData where
  junctions : List BoundaryWalk
  faces : List BoundaryWalk

/-- Definition 11, p.9 (PDF 10): an `(α, β, γ)`-junction tree of `P`.
* the polygons of `J ∪ F` are a partition of `P` whose intersection graph is a tree;
* no two junctions share a boundary, and no two faces do (distinct junctions are disjoint, and
  distinct faces are disjoint);
* every junction has geodesic diameter at most `α`;
* the geodesic distance in `P` between two distinct junctions is at least `β`;
* every face has geodesic diameter at most `γ`. -/
def IsJunctionTree (P : Set Plane) (α β γ : ℝ) (Q : JunctionTreeData) : Prop :=
  IsPartition P (Q.junctions ++ Q.faces) ∧
    (intersectionGraph (Q.junctions ++ Q.faces)).IsTree ∧
    (∀ i j : Fin Q.junctions.length, i ≠ j →
      Disjoint (Q.junctions.get i).region (Q.junctions.get j).region) ∧
    (∀ i j : Fin Q.faces.length, i ≠ j →
      Disjoint (Q.faces.get i).region (Q.faces.get j).region) ∧
    (∀ w ∈ Q.junctions, GeodesicDiamLE w.region α) ∧
    (∀ i j : Fin Q.junctions.length, i ≠ j →
      ∀ x ∈ (Q.junctions.get i).region, ∀ y ∈ (Q.junctions.get j).region,
        ENNReal.ofReal β ≤ geodesic P x y) ∧
    (∀ w ∈ Q.faces, GeodesicDiamLE w.region γ)

/-- Definition 13, p.10 (PDF 11), reading R2: a junction tree of a polygon `P ∈ P_r` of an
`n`-point set is any `(18Λr, (2/3)Λ²r, (54Λ² log n)r)`-junction tree of `P`, `log = log₂`. -/
def IsTheJunctionTree (n : ℕ) (Λ r : ℝ) (P : Set Plane) (Q : JunctionTreeData) : Prop :=
  IsJunctionTree P (18 * Λ * r) (2 / 3 * Λ ^ 2 * r) (54 * Λ ^ 2 * log₂ n * r) Q

/-- The connected components of a set. -/
def components (X : Set Plane) : Set (Set Plane) :=
  {K | ∃ x ∈ X, K = connectedComponentIn X x}

/-- Definition 14, p.10 (PDF 11): the `P`-spines, connected components of `P_{Λ⁻¹ r}` that lie
in `P`. -/
def pSpines {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (P : Set Plane) :
    Set (Set Plane) :=
  {W ∈ components (supportUnion p D (r / Λ)) | W ⊆ P}

/-- Definition 14: the `P`-nerves, connected components of `P_{Λ⁻² r} ∩ P`. -/
def pNerves {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (P : Set Plane) :
    Set (Set Plane) :=
  components (supportUnion p D (r / Λ ^ 2) ∩ P)

/-- Definition 14 and p.11 (PDF 12), line 378: `spines(F)`, the `F`-spines, connected components of
`P_{Λ⁻¹ r} ∩ F`. -/
def fSpines {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (F : Set Plane) :
    Set (Set Plane) :=
  components (supportUnion p D (r / Λ) ∩ F)

/-- Definition 14: the `F`-nerves, connected components of `P_{Λ⁻² r} ∩ F`. -/
def fNerves {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (F : Set Plane) :
    Set (Set Plane) :=
  components (supportUnion p D (r / Λ ^ 2) ∩ F)

/-- p.11 (PDF 12), line 377: `junc(F)`, the junctions intersecting `F`. -/
def junc (Q : JunctionTreeData) (F : Set Plane) : Set (Set Plane) :=
  {J | ∃ w ∈ Q.junctions, J = w.region ∧ (J ∩ F).Nonempty}

/-- Geodesic distance in `P` from a point to a set (`+∞` for the empty set). -/
noncomputable def distanceTo (P : Set Plane) (x : Plane) (J : Set Plane) : ℝ≥0∞ :=
  ⨅ y ∈ J, geodesic P x y

/-- Definition 15, p.11 (PDF 12): the `z`-buffer `B_z(F)`, the points of `F` within geodesic
distance (in `P`) at most `z` of some junction of `junc(F)`. -/
noncomputable def buffer (P : Set Plane) (Q : JunctionTreeData) (F : Set Plane) (z : ℝ) :
    Set Plane :=
  {x ∈ F | ∃ J ∈ junc Q F, distanceTo P x J ≤ ENNReal.ofReal z}

end MinDilationTree.Sublinear.Supplement


