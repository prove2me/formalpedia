-- Prove2me | Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation
-- name    : ChvatalArtGallery_FanPartition_Triangulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:42:35.069888+00:00
-- url     : https://prove2.me/theorems/dee0619e-a90a-4cb1-a566-ce196fbc5cae
-- title:
--   n-triangulations (p. 39): maximal non-crossing diagonal sets of the n-gon, their triangles, fans and fan partitions
-- statement:
--   Chvátal (p. 39) defines an **$n$-triangulation** to be a planar graph $G$ with $n$ vertices such that one of its faces is bounded by an $n$-gon and each of the remaining faces is bounded by a triangle. An edge of $G$ is **inner** if it does not bound the $n$-gon, and a $k$-triangulation is a **fan** if one of its vertices meets all of its $k-3$ inner edges. This file gives the combinatorial form of these notions used throughout the mission.
--
--   **Polygon.** The vertices are $0,1,\dots,n-1$ in their cyclic order around the $n$-gon (the paper's vertices $1,\dots,n$, shifted by one), and indices are taken mod $n$. The **forward distance** from $a$ to $b$ is
--   $$\operatorname{cdist}(a,b) = (b - a) \bmod n \in \{0,\dots,n-1\},$$
--   and $j+i$ denotes the vertex $(j+i) \bmod n$. The **sides** of the $n$-gon are the pairs $\{a,a+1\}$; a **diagonal** is a pair $\{a,b\}$ of distinct vertices that is not a side. Two diagonals $\{a,b\}$ and $\{c,d\}$ **cross** when their four endpoints are distinct and exactly one of $c,d$ lies strictly inside the boundary arc from $a$ to $b$; diagonals with a common endpoint never cross.
--
--   **Triangulation.** A set $D$ of pairs is the set of inner edges of an $n$-triangulation, written $\mathrm{IsTriangulation}(n,D)$, when $n \ge 3$ and
--
--   1. every member of $D$ is a diagonal,
--   2. no two members of $D$ cross, and
--   3. $D$ is maximal: every diagonal that crosses no member of $D$ belongs to $D$.
--
--   The graph $G$ has the sides of the $n$-gon and the members of $D$ as its edges. Its **triangles** are the 3-element vertex sets $\{a,b,c\}$ all three of whose pairs are edges of $G$.
--
--   **Fans.** Two distinct triangles are **adjacent** if they share two vertices (hence an edge). A set $F$ of triangles of $G$ is **dual-connected** if every nonempty subset of $F$ that is closed under adjacency within $F$ is all of $F$. An **inner edge of $F$** is an edge shared by two distinct triangles of $F$. A **fan** of $G$ is a nonempty dual-connected set $F$ of triangles of $G$ together with a vertex $c$ (its centre) lying on every inner edge of $F$:
--   $$\forall\, T \ne T' \in F,\ |T\cap T'| = 2 \implies c \in T \cap T'.$$
--   A **partition of $G$ into fans** is a finite family $P$ of fans that are pairwise disjoint as sets of triangles and whose union is the set of all triangles of $G$; distinct fans may share vertices and edges. The number of fans is $|P|$.
--
--   **Relabelling.** For a vertex $j$ and a length $m$, $\mathrm{arc}(j,m)$ is the map $i \mapsto j+i$ from $\{0,\dots,m-1\}$ to the $n$-gon. For a map $\iota$ from the $m$-gon to the $n$-gon, $\mathrm{pullback}(\iota, D)$ is the set of diagonals of the $m$-gon whose image under $\iota$ lies in $D$. These describe the two pieces into which an inner edge cuts $G$.
--
--   These definitions are shared by every statement of the mission: the goal theorem, the base case, the bound $k\le 6$, the cut, the four cases and the tightness of the bound.
--
--   **Formalization Note.** Mathlib has no planar embeddings, so the planar graph of the paper is encoded by the standard equivalent combinatorial description of a triangulated polygon: the labelled $n$-cycle together with a maximal set of pairwise non-crossing diagonals. Maximality is what makes "each of the remaining faces is bounded by a triangle" hold; without it the empty set would triangulate every polygon. Since every vertex lies on the outer face, every 3-cycle of $G$ bounds an inner face, so the triangles defined here are exactly the bounded faces ($n-2$ of them). A dual-connected set $F$ of $k-2$ triangles is a sub-polygon of $G$, i.e. a $k$-triangulation in the paper's sense, whose inner edges are exactly the edges shared by two triangles of $F$; dual-connectedness is binding, since without it a fan partition would only give Fisk's weaker guard set. Vertices are `Fin n`, 0-based; pairs are `Sym2 (Fin n)`; vertex sets and sets of triangles are `Finset`s. The decidability instances only make small instances checkable by evaluation.
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 39, definitions of n-triangulation, inner edge and fan before the Theorem; p. 40, proof of the Theorem (cyclic labelling of the vertices, the cut of G along (j, j + k))

import Mathlib

namespace ChvatalArtGallery.FanPartition

/-!
Combinatorial n-triangulations (Chvátal 1975, p. 39).

The vertices of the n-gon are `Fin n`, 0-based, in their cyclic (boundary) order: the bounding
n-gon is `0 → 1 → ⋯ → n - 1 → 0`. A planar graph with one face bounded by this n-gon and every
other face a triangle is encoded by its set `D` of inner edges: a maximal set of pairwise
non-crossing diagonals of the n-gon.
-/

/-- Forward cyclic distance from `a` to `b` on the n-cycle: the number of boundary steps
`a → a + 1 → ⋯ → b`, a number in `{0, …, n - 1}`. -/
def cdist {n : ℕ} (a b : Fin n) : ℕ := (b.val + n - a.val) % n

/-- The vertex `j + i` (indices mod n). -/
def shift {n : ℕ} (j : Fin n) (i : ℕ) : Fin n :=
  ⟨(j.val + i) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩

/-- `e` is a side of the n-gon: `e = s(a, a + 1)` for some vertex `a`. -/
def IsBoundaryEdge {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  ∃ a b : Fin n, e = s(a, b) ∧ cdist a b = 1

/-- `e` is a diagonal of the n-gon: it joins two distinct vertices and is not a side. -/
def IsDiagonal {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  ∀ a b : Fin n, e = s(a, b) → a ≠ b ∧ cdist a b ≠ 1 ∧ cdist b a ≠ 1

/-- Two chords `e = s(a, b)` and `f = s(c, d)` cross: their four endpoints are distinct and
exactly one of `c, d` lies strictly inside the boundary arc from `a` to `b`. Chords sharing an
endpoint never cross. -/
def Crosses {n : ℕ} (e f : Sym2 (Fin n)) : Prop :=
  ∃ a b c d : Fin n, e = s(a, b) ∧ f = s(c, d) ∧
    0 < cdist a c ∧ cdist a c < cdist a b ∧ cdist a b < cdist a d

/-- `D` is the set of inner edges of an n-triangulation: an n-gon has at least three vertices,
every member is a diagonal, no two members cross, and `D` is maximal (every diagonal crossing
no member of `D` belongs to `D`). -/
def IsTriangulation (n : ℕ) (D : Finset (Sym2 (Fin n))) : Prop :=
  3 ≤ n ∧ (∀ e ∈ D, IsDiagonal e) ∧
  (∀ e ∈ D, ∀ f ∈ D, ¬ Crosses e f) ∧
  (∀ e : Sym2 (Fin n), IsDiagonal e → (∀ f ∈ D, ¬ Crosses e f) → e ∈ D)

/-- The edges of the graph `G` with inner-edge set `D`: the sides of the n-gon and `D`. -/
def IsEdge {n : ℕ} (D : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Prop :=
  IsBoundaryEdge e ∨ e ∈ D

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (IsBoundaryEdge e) := by
  unfold IsBoundaryEdge; infer_instance

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (IsDiagonal e) := by
  unfold IsDiagonal; infer_instance

instance {n : ℕ} (e f : Sym2 (Fin n)) : Decidable (Crosses e f) := by
  unfold Crosses; infer_instance

instance {n : ℕ} (D : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Decidable (IsEdge D e) := by
  unfold IsEdge; infer_instance

instance {n : ℕ} (D : Finset (Sym2 (Fin n))) : Decidable (IsTriangulation n D) := by
  unfold IsTriangulation; infer_instance

/-- The triangles of `G`: the 3-element vertex sets all three of whose pairs are edges of `G`.
In a triangulated polygon these are exactly the bounded (triangular) faces. -/
def triangles (n : ℕ) (D : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun T => ∀ a ∈ T, ∀ b ∈ T, a ≠ b → IsEdge D s(a, b))

/-- Two distinct triangles are adjacent when they share two vertices (hence an edge). -/
def Adjacent {n : ℕ} (T T' : Finset (Fin n)) : Prop :=
  T ≠ T' ∧ (T ∩ T').card = 2

instance {n : ℕ} (T T' : Finset (Fin n)) : Decidable (Adjacent T T') := by
  unfold Adjacent; infer_instance

/-- A set `F` of triangles is dual-connected: every nonempty subset of `F` that is closed under
adjacency inside `F` is all of `F` (equivalently, any two members of `F` are joined by a chain
in `F` whose consecutive members share an edge). -/
def DualConnected {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ S ⊆ F, S.Nonempty → (∀ X ∈ S, ∀ Y ∈ F, Adjacent X Y → Y ∈ S) → S = F

-- The decision procedures below run through the finsets themselves (`Finset.decidableDforallFinset`),
-- not through the ambient finite types of sets of triangles.
instance {n : ℕ} (F : Finset (Finset (Fin n))) : Decidable (DualConnected F) :=
  @decidable_of_iff _ _
    (by simp only [DualConnected, Finset.mem_powerset])
    (@Finset.decidableDforallFinset _ F.powerset
      (fun S _ => S.Nonempty → (∀ X ∈ S, ∀ Y ∈ F, Adjacent X Y → Y ∈ S) → S = F)
      (fun S _ => @instDecidableForall _ _ inferInstance
        (@instDecidableForall _ _
          (@Finset.decidableDforallFinset _ S (fun X _ => ∀ Y ∈ F, Adjacent X Y → Y ∈ S)
            (fun X _ => @Finset.decidableDforallFinset _ F (fun Y _ => Adjacent X Y → Y ∈ S)
              (fun _ _ => inferInstance)))
          inferInstance)))

/-- `F` is a fan of the n-triangulation with inner edges `D`: a nonempty, dual-connected set of
triangles of `G` (so its union is a k-triangulation with `k = |F| + 2`) having a vertex `c` that
meets all of its inner edges, an inner edge of `F` being an edge shared by two distinct
triangles of `F`. -/
def IsFan (n : ℕ) (D : Finset (Sym2 (Fin n))) (F : Finset (Finset (Fin n))) : Prop :=
  F ⊆ triangles n D ∧ F.Nonempty ∧ DualConnected F ∧
  ∃ c : Fin n, ∀ T ∈ F, ∀ T' ∈ F, Adjacent T T' → c ∈ T ∩ T'

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) (F : Finset (Finset (Fin n))) :
    Decidable (IsFan n D F) := by
  unfold IsFan
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance
      (@Fintype.decidableExistsFintype _ _ (fun c =>
        @Finset.decidableDforallFinset _ F (fun T _ => ∀ T' ∈ F, Adjacent T T' → c ∈ T ∩ T')
          (fun T _ => @Finset.decidableDforallFinset _ F (fun T' _ => Adjacent T T' → c ∈ T ∩ T')
            (fun _ _ => inferInstance))) _)))

/-- `P` partitions the n-triangulation with inner edges `D` into fans: every member of `P` is a
fan, distinct members share no triangle, and together they contain every triangle of `G`.
Fans may share vertices and edges. -/
def IsFanPartition (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (P : Finset (Finset (Finset (Fin n)))) : Prop :=
  (∀ F ∈ P, IsFan n D F) ∧
  (∀ F ∈ P, ∀ F' ∈ P, F ≠ F' → Disjoint F F') ∧
  P.biUnion id = triangles n D

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) (P : Finset (Finset (Finset (Fin n)))) :
    Decidable (IsFanPartition n D P) := by
  unfold IsFanPartition
  exact @instDecidableAnd _ _
    (@Finset.decidableDforallFinset _ P (fun F _ => IsFan n D F) (fun _ _ => inferInstance))
    (@instDecidableAnd _ _
      (@Finset.decidableDforallFinset _ P (fun F _ => ∀ F' ∈ P, F ≠ F' → Disjoint F F')
        (fun F _ => @Finset.decidableDforallFinset _ P (fun F' _ => F ≠ F' → Disjoint F F')
          (fun _ _ => inferInstance)))
      inferInstance)

/-- The vertices `j, j + 1, …, j + m - 1` (mod n) of the n-gon, relabelled `0, …, m - 1`. -/
def arc {n : ℕ} (j : Fin n) (m : ℕ) : Fin m → Fin n := fun i => shift j i.val

/-- Pull a set of inner edges of the n-gon back along a relabelling `ι : Fin m → Fin n`: the
diagonals of the m-gon whose image under `ι` lies in `D`. -/
def pullback {m n : ℕ} (ι : Fin m → Fin n) (D : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin m)) :=
  Finset.univ.filter (fun e => IsDiagonal e ∧ Sym2.map ι e ∈ D)

end ChvatalArtGallery.FanPartition


