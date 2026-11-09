-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_Construction
-- name    : ArcKayles192_PSPACE_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:44.584808+00:00
-- url     : https://prove2.me/theorems/153abe3c-59c1-497e-9b45-32b0681d88a5
-- title:
--   The reduction graph $G_\varphi$ with $K=4n+6$, $R=m+2n+2$, its vertex classes, assignment and pass moves, and the counts $r,k,q$
-- statement:
--   Let $\varphi=C_1\wedge\cdots\wedge C_m$ be a Pos CNF instance over $x_1,\dots,x_n$. Set
--   $$K:=4n+6,\qquad R:=m+2n+2.$$
--   The graph $G_\varphi$ has the vertices
--   $$\{s,t\}\cup\{a_j,b_j\mid j\in[m]\}\cup\{v_i,t_i\mid i\in[R]\}\cup\{f_i\mid i\in[n]\}\cup\{y_i,z_i\mid i\in[K]\}$$
--   and the edges
--   $$\{st\}\cup\{sa_j,a_jb_j\mid j\in[m]\}\cup\{b_jv_i\mid j\in[m],i\in[R]\}\cup\{v_it_i\mid i\in[R]\}\cup\{v_if_i\mid i\in[n]\}\cup\{b_jf_i\mid x_i\in C_j\}\cup\{sy_i,y_iz_i\mid i\in[K]\},$$
--   so it has $2+2m+2K+2R+n$ vertices. The classes are $A=\{a_j\}$, $B=\{b_j\}$, $V=\{v_i\}$, $T=\{t_i\}$, $F=\{f_i\}$, $Y=\{y_i\}$, $Z=\{z_i\}$.
--
--   1. An **assignment move** is an edge $v_it_i$ (read as $x_i:=$ true) or $v_if_i$ (read as $x_i:=$ false) with $i\in[n]$.
--   2. A **pass move** is an edge $v_it_i$ with $i\in[n+1,R]$, or an edge $y_iz_i$ with $i\in[K]$.
--   3. For a position $S$ (a set of remaining vertices), $r=|S\cap V|$, $k=|S\cap Y|$ and $q=|S\cap B|$.
--   4. A position is **reached by assignment and pass moves** if it arises from $V(G_\varphi)$ by a sequence of legal moves (edges with both endpoints remaining), each an assignment or a pass move.
--
--   These are the objects of Claims 7–10.
--
--   **Formalization Note** Indices are 0-based (`Fin m`, `Fin R`, `Fin n`, `Fin K`). The vertex type is an inductive type with one constructor per family; $t_i$ is the constructor `ti`. Edges are listed in one orientation and symmetrized (`SimpleGraph.fromRel`). Isolated vertices are not deleted; $r,k,q$ count class members that remain.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, pp.5–6, proof of Theorem 1 (Construction, K, R, vertex and edge sets, classes A–Z, assignment and pass moves, r and k; q on p.8)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_PosCNF

namespace ArcKayles192.PSPACE

/-! # The reduction graph `G_φ` (proof of Theorem 1, pp.5–6)

Indices are 0-based: the paper's `a_j, b_j` (`j ∈ [m]`) are `a j, b j` with `j : Fin m`; its
`v_i, t_i` (`i ∈ [R]`) are `v i, ti i` with `i : Fin R`, and `v_i` for `i ∈ [n]` is `v ⟨i, _⟩`
with `i < n`; its `f_i` (`i ∈ [n]`) are `f i`; its `y_i, z_i` (`i ∈ [K]`) are `y i, z i`. -/

/-- `K = 4n + 6`. -/
def Kc (n : ℕ) : ℕ := 4 * n + 6

/-- `R = m + 2n + 2`. -/
def Rc (n m : ℕ) : ℕ := m + 2 * n + 2

/-- The vertices of `G_φ` for `n` variables and `m` clauses:
`s, t; a_j, b_j (j ∈ [m]); v_i, t_i (i ∈ [R]); f_i (i ∈ [n]); y_i, z_i (i ∈ [K])`. -/
inductive Vtx (n m : ℕ) : Type where
  | s : Vtx n m
  | t : Vtx n m
  | a : Fin m → Vtx n m
  | b : Fin m → Vtx n m
  | v : Fin (Rc n m) → Vtx n m
  | ti : Fin (Rc n m) → Vtx n m
  | f : Fin n → Vtx n m
  | y : Fin (Kc n) → Vtx n m
  | z : Fin (Kc n) → Vtx n m
  deriving DecidableEq, Fintype

/-- The index `i ∈ [n]` viewed as an index of `V` (`n ≤ R`). -/
def vIdx {n : ℕ} (m : ℕ) (i : Fin n) : Fin (Rc n m) :=
  ⟨i.val, by unfold Rc; omega⟩

/-- The listed edges of `G_φ`, each in one orientation:
`st; s a_j, a_j b_j (j ∈ [m]); b_j v_i (j ∈ [m], i ∈ [R]); v_i t_i (i ∈ [R]); v_i f_i (i ∈ [n]);
b_j f_i whenever x_i ∈ C_j; s y_i, y_i z_i (i ∈ [K])`. -/
def edgeRel (φ : PosCNF) : Vtx φ.n φ.m → Vtx φ.n φ.m → Prop
  | .s, .t => True
  | .s, .a _ => True
  | .a j, .b j' => j = j'
  | .b _, .v _ => True
  | .v i, .ti i' => i = i'
  | .v i, .f i' => i = vIdx φ.m i'
  | .b j, .f i => i ∈ φ.clause j
  | .s, .y _ => True
  | .y i, .z i' => i = i'
  | _, _ => False

/-- The graph `G_φ`: the simple graph whose edges are exactly the pairs listed in `edgeRel`. -/
def Gphi (φ : PosCNF) : SimpleGraph (Vtx φ.n φ.m) :=
  SimpleGraph.fromRel (edgeRel φ)

/-- The vertex classes `A, B, V, T, F, Y, Z` of `G_φ`. -/
def classA (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.a
/-- The class `B`. -/
def classB (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.b
/-- The class `V`. -/
def classV (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.v
/-- The class `T`. -/
def classT (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.ti
/-- The class `F`. -/
def classF (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.f
/-- The class `Y`. -/
def classY (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.y
/-- The class `Z`. -/
def classZ (n m : ℕ) : Finset (Vtx n m) := Finset.univ.image Vtx.z

/-- `r`: the number of vertices of `V` remaining in the position `S`. -/
def rCount {φ : PosCNF} (S : Finset (Vtx φ.n φ.m)) : ℕ := (S ∩ classV φ.n φ.m).card

/-- `k`: the number of vertices of `Y` remaining in the position `S`. -/
def kCount {φ : PosCNF} (S : Finset (Vtx φ.n φ.m)) : ℕ := (S ∩ classY φ.n φ.m).card

/-- `q`: the number of vertices of `B` remaining in the position `S`. -/
def qCount {φ : PosCNF} (S : Finset (Vtx φ.n φ.m)) : ℕ := (S ∩ classB φ.n φ.m).card

/-- An **assignment move**: the edge `v_i t_i` (setting `x_i` to true) or `v_i f_i` (setting `x_i`
to false), for a variable index `i ∈ [n]`. -/
def IsAssignMove (φ : PosCNF) (u w : Vtx φ.n φ.m) : Prop :=
  ∃ i : Fin φ.n, s(u, w) = s(Vtx.v (vIdx φ.m i), Vtx.ti (vIdx φ.m i)) ∨
    s(u, w) = s(Vtx.v (vIdx φ.m i), Vtx.f i)

/-- A **pass move**: the edge `v_i t_i` with `i ∈ [n+1, R]` (0-based: `n ≤ i < R`), or the edge
`y_i z_i` with `i ∈ [K]`. -/
def IsPassMove (φ : PosCNF) (u w : Vtx φ.n φ.m) : Prop :=
  (∃ i : Fin (Rc φ.n φ.m), φ.n ≤ i.val ∧ s(u, w) = s(Vtx.v i, Vtx.ti i)) ∨
    ∃ i : Fin (Kc φ.n), s(u, w) = s(Vtx.y i, Vtx.z i)

/-- The positions of Arc Kayles on `G_φ` reachable from the initial position (all vertices) by
playing **only assignment and pass moves**, each a legal move (an edge of `G_φ` with both ends
remaining). -/
inductive ReachableByAP (φ : PosCNF) : Finset (Vtx φ.n φ.m) → Prop
  | start : ReachableByAP φ Finset.univ
  | step {S : Finset (Vtx φ.n φ.m)} {u w : Vtx φ.n φ.m} :
      ReachableByAP φ S → u ∈ S → w ∈ S → (Gphi φ).Adj u w →
      (IsAssignMove φ u w ∨ IsPassMove φ u w) → ReachableByAP φ (S \ {u, w})

end ArcKayles192.PSPACE


