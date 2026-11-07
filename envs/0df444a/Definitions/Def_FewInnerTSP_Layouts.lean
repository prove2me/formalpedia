-- Prove2me | Definitions.Def_FewInnerTSP_Layouts
-- name    : FewInnerTSP_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:36.616348+00:00
-- url     : https://prove2.me/theorems/9229e845-237f-4ea2-b9f5-07f7f1af9953
-- title:
--   Machine input and output layouts for the algorithmic milestones
-- statement:
--   Cell layouts for the machine statements, all lists of reals:
--
--   1. **Output** "starts with" a list $L$: output cell $j$ (after the input) holds the $j$-th entry of $L$.
--   2. **Gap selection** (Lemma 3.1): $h$, $k$, the hull points in counterclockwise order, then the interior points, two coordinates each.
--   3. **Edge codes**: $(0,i,j)$ is the free edge between the vertices at list positions $i,j$; $(1,j,0)$ is skeleton edge $j$; three cells per code. A **family** is its number of members, then for each member its length and its codes.
--   4. **Separator input** (Theorem 4.1): $N_0$, $|V|$, $m$, $a$; per vertex its coordinates and flags for $A$ and $Q$; then the list positions of the skeleton vertices.
--   5. **Charge input** (Lemma 4.5): $N_0$, $a$, $h$, $m$, then the normalized points of $A$, of $H$ and the skeleton vertices in cyclic order.
--   6. **Representative input** (Lemma 5.2): $b$, the number of rows, then per row a weight and the partner of each terminal.
--   7. **State input** (Lemma 5.3): $N_0,|V|,m,a,b,|E|$; per vertex coordinates and flags for $A$ and $B$; skeleton positions; per allowed edge its code, weight and mandatory flag.
--   8. **Kernel input** (Lemma 5.6): $k$, $m$, the coordinates of the interior points then of the skeleton vertices in cyclic order, then per skeleton edge its mandatory flag and stored weight.
--
--   **Formalization Note** Every layout is within a constant factor of any reasonable encoding, so the bounds are unaffected.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemmas 3.1, 4.5, 5.2, 5.3, 5.6 and Theorem 4.1 (pp.4–12, PDF pp.6–14)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_State

namespace FewInnerTSP

/-- The program's output after `t` steps starts with the list `out`: cell `j` after the input holds
`out[j]`. -/
def OutputIs (A : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape) (t : ℕ)
    (out : List ℝ) : Prop :=
  ∀ j : Fin out.length, MatMulTimeLP.outputAt A input ω t out.length j = out.get j

/-- **Input for gap selection (Lemma 3.1).** The reals `h`, `k`, then the hull points in counterclockwise
order, then the interior points. -/
noncomputable def gapLayout {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) (I : List (Fin n)) :
    List ℝ :=
  (h : ℝ) :: (I.length : ℝ) :: (coordsOf P (List.ofFn hull) ++ coordsOf P I)

/-- `L` lists the finite set `X` without repetition. -/
def IsListing {α : Type*} [DecidableEq α] (L : List α) (X : Finset α) : Prop :=
  L.Nodup ∧ L.toFinset = X

/-- A code for an edge: `(0, i, j)` is the free edge between the vertices at list positions `i` and `j`;
`(1, j, 0)` is the skeleton edge `j`. -/
abbrev EdgeCode := ℕ × ℕ × ℕ

/-- Decode an edge code relative to the list `vs` of vertices. -/
def decodeEdge {n : ℕ} (m : ℕ) (vs : List (Fin n)) (c : EdgeCode) : Option (Edge n m) :=
  match c with
  | (0, i, j) =>
    match vs[i]?, vs[j]? with
    | some a, some b => some (Edge.free s(a, b))
    | _, _ => none
  | (1, j, _) => if h : j < m then some (Edge.skel ⟨j, h⟩) else none
  | _ => none

/-- A list of codes decodes without failure to the edge set it lists. -/
def DecodesTo {n m : ℕ} (vs : List (Fin n)) (L : List EdgeCode) (C : Finset (Edge n m)) : Prop :=
  (∀ c ∈ L, (decodeEdge m vs c).isSome) ∧ (L.filterMap (decodeEdge m vs)).toFinset = C

/-- Three cells per edge code. -/
def encodeEdges (L : List EdgeCode) : List ℝ :=
  L.flatMap fun c => [(c.1 : ℝ), (c.2.1 : ℝ), (c.2.2 : ℝ)]

/-- A family of edge lists in cells: the number of lists, then for each list its length and its codes. -/
noncomputable def encodeFamily (L : List (List EdgeCode)) : List ℝ :=
  (L.length : ℝ) :: L.flatMap fun c => (c.length : ℝ) :: encodeEdges c

/-- The list position of each skeleton vertex in the list `vs`, `|vs|` if absent. -/
noncomputable def skelPositions {n m : ℕ} (Γ : Skeleton n m) (vs : List (Fin n)) : List ℝ :=
  List.ofFn fun j => ((vs.idxOf (Γ.vert j) : ℕ) : ℝ)

/-- **Input for Theorem 4.1.** The reals `N₀`, `|V|`, `m`, `a`; four cells per vertex of `vs`: its
coordinates and the flags of `A` and `Q`; then the list positions of the skeleton vertices. -/
noncomputable def sepLayout {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (N0 : ℕ)
    (vs : List (Fin n)) (A Q : Finset (Fin n)) : List ℝ :=
  (N0 : ℝ) :: (vs.length : ℝ) :: (m : ℝ) :: (A.card : ℝ) ::
    ((vs.flatMap fun v => [P v 0, P v 1, if v ∈ A then 1 else 0, if v ∈ Q then 1 else 0]) ++
      skelPositions Γ vs)

/-- **Input for Lemma 4.5**, in normalized coordinates. The reals `N₀`, `a`, `h`, `m`, then the points of
`A`, of `H` and the skeleton vertices in cyclic order, two cells each. -/
noncomputable def chargeLayout {m : ℕ} (N0 : ℕ) (la lh : List Pt) (w : Fin m → Pt) : List ℝ :=
  (N0 : ℝ) :: (la.length : ℝ) :: (lh.length : ℝ) :: (m : ℝ) ::
    ((la ++ lh ++ List.ofFn w).flatMap fun x => [x 0, x 1])

/-- **Input for Lemma 5.2.** The reals `b`, `|𝒜|`, then for each row its weight and the partner of each of
the `b` terminals. -/
noncomputable def repLayout {b : ℕ} (rows : List (ℝ × (Fin b → Fin b))) : List ℝ :=
  (b : ℝ) :: (rows.length : ℝ) ::
    rows.flatMap fun r => r.1 :: List.ofFn fun i => (((r.2 i : ℕ)) : ℝ)

/-- The pairs `{x, M x}` of a partner function. -/
def partnerPairs {b : ℕ} (M : Fin b → Fin b) : Finset (Sym2 (Fin b)) :=
  Finset.univ.image fun x => s(x, M x)

/-- A partner function of a perfect matching on `Fin b`: a fixed-point-free involution. -/
def IsPartner {b : ℕ} (M : Fin b → Fin b) : Prop :=
  ∀ x, M x ≠ x ∧ M (M x) = x

/-- **Input for Lemma 5.3.** The reals `N₀`, `|V|`, `m`, `a`, `b`, `|E|`; four cells per vertex of `vs`:
coordinates and the flags of `A` and `B`; the list positions of the skeleton vertices; then five cells per
allowed edge: its code, its weight and the flag of `F`. -/
noncomputable def stateLayout {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (N0 : ℕ)
    (vs : List (Fin n)) (es : List EdgeCode) (S : State n m) : List ℝ := by
  classical
  exact (N0 : ℝ) :: (vs.length : ℝ) :: (m : ℝ) :: (S.A.card : ℝ) :: (S.B.card : ℝ) ::
    (es.length : ℝ) ::
    ((vs.flatMap fun v => [P v 0, P v 1, if v ∈ S.A then 1 else 0, if v ∈ S.B then 1 else 0]) ++
      skelPositions Γ vs ++
      es.flatMap fun c =>
        [(c.1 : ℝ), (c.2.1 : ℝ), (c.2.2 : ℝ),
          ((decodeEdge m vs c).elim 0 S.w),
          if (∃ e ∈ decodeEdge m vs c, e ∈ S.F) then 1 else 0])

/-- **Input for Lemma 5.6.** The reals `k`, `m`, the interior points, the skeleton vertices in cyclic order,
then for each skeleton edge the flag of its mandatory status and its stored weight. Edge codes refer to the
list `I ++ vert`. -/
noncomputable def kernelLayout {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (I : List (Fin n)) :
    List ℝ := by
  classical
  exact (I.length : ℝ) :: (m : ℝ) ::
    (coordsOf P (I ++ List.ofFn Γ.vert) ++
      (List.ofFn fun j => [if Γ.mand j then (1 : ℝ) else 0, Γ.wt j]).flatten)

end FewInnerTSP


