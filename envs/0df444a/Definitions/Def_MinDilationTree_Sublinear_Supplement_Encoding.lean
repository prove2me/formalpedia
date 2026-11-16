-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_Supplement_Encoding
-- name    : MinDilationTree_Sublinear_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:56:15.808757+00:00
-- url     : https://prove2.me/theorems/1a521149-50c6-4aa3-b167-c9880ec31865
-- title:
--   Real-RAM input and output encodings, compressed scale sequences and consistent sequences
-- statement:
--   This file fixes how the supplement's algorithmic statements talk to the published real RAM, and the two notions of §5.2.
--
--   1. **Inputs.** After the published point-set encoding $[n,x_0,y_0,\ldots]$ come the reals $\Lambda$ (and $r$), the Delaunay triangulation as an edge list $[k,i_1,j_1,\ldots]$ listing each edge once with $i<j$, the label of an input point of the polygon $P$, a junction tree (junctions, then faces, each polygon as its number of walk occurrences followed by their coordinates), a face index, and representative points of the spines of $\mathfrak S$.
--   2. **Outputs.** The output cells hold a self-delimiting list; for statements with a certificate, a nonzero first cell certifies the lower bound and otherwise the first cell is $0$ followed by the object.
--   3. A **compressed scale sequence** for $S$ and $\Lambda$ is $(r_0,\ldots,r_N)$, $N\ge0$, with: for $1\le i\le N$ either $r_i/r_{i-1}=\Lambda$ or $r_i/r_{i-1}\ge\Lambda^{10}$; for every pair $p\ne q$ of $S$ some $i\ge1$ has $r_{i-1}\le\|p-q\|<r_i=\Lambda r_{i-1}$; and $r_0<\|p-q\|$ for every pair $p\ne q$.
--   4. A **consistent sequence of junction trees** (Definition 28) is a compressed scale sequence $R$ together with, for each $r\in R$, a list of junction trees, each tagged with an input point of its polygon, that contains a junction tree (Definition 13) of every $P\in\mathcal P_r$, such that every listed junction tree is one of the polygon of $\mathcal P_r$ containing its tagged point, and for every face $F$ of it there is a good cut of $G_{F,\operatorname{spines}(F)}$.
--
--   Lemma 27 computes compressed scale sequences, and Theorem 29 computes consistent sequences or certifies $\mathrm{Opt}\ge\Lambda/100$.
--
--   **Formalization Note** Labels and counts are written as reals; every encoding is length-prefixed, so it decodes uniquely. Ratios are real quotients; $r_{i-1}=0$ gives ratio $0$, which satisfies neither alternative for $\Lambda\ge6$.
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 19 (PDF p. 20), §5.2 (compressed scale sequence, lines 627–633) and Definition 28; reading R0 of the mission plan

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_RAMEncoding
import Definitions.Def_MinDilationTree_Sublinear_Supplement_SpineCut

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- `L` lists the edges of `D` once each, as label pairs `(i, j)` with `i < j`, in any order. -/
def ListsGraph {n : ℕ} (D : SimpleGraph (Fin n)) (L : List (Fin n × Fin n)) : Prop :=
  L.Nodup ∧ (∀ e ∈ L, e.1 < e.2) ∧ ∀ i j : Fin n, D.Adj i j ↔ ((i, j) ∈ L ∨ (j, i) ∈ L)

/-- Input encoding of an edge list over point labels: its length, then the label pairs. -/
noncomputable def encodeEdgeList {n : ℕ} (L : List (Fin n × Fin n)) : List ℝ :=
  [(L.length : ℝ)] ++ L.flatMap fun e => [((e.1 : ℕ) : ℝ), ((e.2 : ℕ) : ℝ)]

/-- Encoding of a list of planar points: its length, then the coordinates. -/
noncomputable def encodePoints (X : List Plane) : List ℝ :=
  [(X.length : ℝ)] ++ X.flatMap fun x => [x 0, x 1]

/-- Self-delimiting encoding of a boundary walk: the number of occurrences, then their coordinates
in walk order (repeated visits are repeated). -/
noncomputable def encodeWalk (w : BoundaryWalk) : List ℝ :=
  [(w.m : ℝ)] ++ (List.finRange w.m).flatMap fun i => [w.vertex i 0, w.vertex i 1]

/-- Encoding of a list of polygons. -/
noncomputable def encodePieces (L : List BoundaryWalk) : List ℝ :=
  [(L.length : ℝ)] ++ L.flatMap encodeWalk

/-- Encoding of a junction tree: the junctions, then the faces. -/
noncomputable def encodeJunctionTree (Q : JunctionTreeData) : List ℝ :=
  encodePieces Q.junctions ++ encodePieces Q.faces

/-- Encoding of a straight-line graph: the vertex count and coordinates, then the edge list. -/
noncomputable def encodeCut (C : CutData) : List ℝ :=
  [(C.size : ℝ)] ++ (List.finRange C.size).flatMap (fun i => [C.point i 0, C.point i 1]) ++
    [(C.edges.length : ℝ)] ++ C.edges.flatMap fun e => [((e.1 : ℕ) : ℝ), ((e.2 : ℕ) : ℝ)]

/-- Encoding of a finite real sequence: its length, then its entries. -/
noncomputable def encodeReals (R : List ℝ) : List ℝ :=
  [(R.length : ℝ)] ++ R

/-- The output cells of the run after `t` steps (from cell `input.length` on) hold `out`. -/
def OutputIs (A : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape) (t : ℕ)
    (out : List ℝ) : Prop :=
  ∀ j : Fin out.length, MatMulTimeLP.outputAt A input ω t out.length j = out.get j

/-- The first output cell after `t` steps; a nonzero value certifies the lower bound. -/
noncomputable def outputFlag (A : MatMulTimeLP.Program) (input : List ℝ)
    (ω : MatMulTimeLP.Tape) (t : ℕ) : ℝ :=
  (MatMulTimeLP.stateAt A input ω t).R input.length

/-- §5.2, p.19 (PDF 20), lines 627–633: `R = (r₀, …, r_N)` is a compressed scale sequence for
`S` and `Λ`:
* for `1 ≤ i ≤ N`, either `rᵢ / rᵢ₋₁ = Λ` or `rᵢ / rᵢ₋₁ ≥ Λ¹⁰`;
* for all `p ≠ q` in `S` there is `i ≥ 1` with `rᵢ₋₁ ≤ ‖p − q‖ < rᵢ = Λ rᵢ₋₁`;
* for all `p ≠ q` in `S`, `r₀ < ‖p − q‖`. -/
def IsCompressedScaleSequence {n : ℕ} (p : Fin n → Plane) (Λ : ℝ) (R : List ℝ) : Prop :=
  R ≠ [] ∧
  (∀ i : ℕ, 1 ≤ i → i < R.length →
    R.getD i 0 / R.getD (i - 1) 0 = Λ ∨ Λ ^ 10 ≤ R.getD i 0 / R.getD (i - 1) 0) ∧
  (∀ a b : Fin n, a ≠ b → ∃ i : ℕ, 1 ≤ i ∧ i < R.length ∧
    R.getD (i - 1) 0 ≤ ‖p a - p b‖ ∧ ‖p a - p b‖ < R.getD i 0 ∧
    R.getD i 0 = Λ * R.getD (i - 1) 0) ∧
  ∀ a b : Fin n, a ≠ b → R.getD 0 0 < ‖p a - p b‖

/-- One junction tree of a scale, tagged with the label of an input point of its polygon. -/
structure ScaleEntry where
  label : ℕ
  tree : JunctionTreeData

/-- Encoding of a sequence of scales, each with its list of tagged junction trees. -/
noncomputable def encodeScales (scales : List (ℝ × List ScaleEntry)) : List ℝ :=
  [(scales.length : ℝ)] ++ scales.flatMap fun s =>
    [s.1, (s.2.length : ℝ)] ++ s.2.flatMap fun e => [(e.label : ℝ)] ++ encodeJunctionTree e.tree

/-- Definition 28, p.19 (PDF 20): the scales form a compressed scale sequence `R`; for every
`r ∈ R` the entries contain, for every polygon `P ∈ P_r`, a junction tree of `P` (Definition 13);
every entry is a junction tree of the polygon of `P_r` containing its tagged point; and the
sequence is consistent: for every listed junction tree and every face `F` of it there is a good
cut of `G_{F, spines(F)}`. -/
def IsConsistentSequence {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ : ℝ)
    (scales : List (ℝ × List ScaleEntry)) : Prop :=
  IsCompressedScaleSequence p Λ (scales.map Prod.fst) ∧
  ∀ s ∈ scales,
    (∀ P ∈ support p D s.1, ∃ e ∈ s.2, ∃ i : Fin n, (i : ℕ) = e.label ∧ p i ∈ P) ∧
    ∀ e ∈ s.2, ∃ i : Fin n, (i : ℕ) = e.label ∧ ∃ P ∈ support p D s.1, p i ∈ P ∧
      IsTheJunctionTree n Λ s.1 P e.tree ∧
      ∀ F ∈ e.tree.faces, ∃ C : CutData,
        GoodCut p D Λ s.1 P e.tree F (fSpines p D Λ s.1 F.region) C

/-- Input of Lemma 12: the point set, `Λ`, `r`, the Delaunay triangulation as an edge list, and the
label of an input point of the polygon `P ∈ P_r`. -/
noncomputable def lemma12Input {n : ℕ} (p : Fin n → Plane) (Λ r : ℝ)
    (L : List (Fin n × Fin n)) (i : Fin n) : List ℝ :=
  enc p ++ [Λ, r] ++ encodeEdgeList L ++ [((i : ℕ) : ℝ)]

/-- The set `𝔖` of `F`-spines named by representative points. -/
def spinesOf {n : ℕ} (p : Fin n → Plane) (D : SimpleGraph (Fin n)) (Λ r : ℝ) (F : Set Plane)
    (reps : List Plane) : Set (Set Plane) :=
  {W ∈ fSpines p D Λ r F | ∃ x ∈ reps, x ∈ W}

/-- Input of Lemma 23: the point set, `Λ`, `r`, the Delaunay triangulation as an edge list, the
label of an input point of `P`, the junction tree, the index of the face `F`, and one
representative point of each `F`-spine of `𝔖`. -/
noncomputable def lemma23Input {n : ℕ} (p : Fin n → Plane) (Λ r : ℝ)
    (L : List (Fin n × Fin n)) (i : Fin n) (Q : JunctionTreeData) (f : ℕ)
    (reps : List Plane) : List ℝ :=
  enc p ++ [Λ, r] ++ encodeEdgeList L ++ [((i : ℕ) : ℝ)] ++ encodeJunctionTree Q ++
    [(f : ℝ)] ++ encodePoints reps

/-- Input of Theorem 29: the point set, `Λ`, and the Delaunay triangulation as an edge list. -/
noncomputable def theorem29Input {n : ℕ} (p : Fin n → Plane) (Λ : ℝ)
    (L : List (Fin n × Fin n)) : List ℝ :=
  enc p ++ [Λ] ++ encodeEdgeList L

end MinDilationTree.Sublinear.Supplement


