-- Prove2me | Definitions.Def_DisjointPathsDAG_FirstEvent
-- name    : DisjointPathsDAG_FirstEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:38.778149+00:00
-- url     : https://prove2.me/theorems/47bf14bb-f9b5-48cf-883e-ea55f78a3667
-- title:
--   Private terminals, path sums $N_i$, crossing kernels $K^w_i$, prefix tables $\Lambda_S$, and $B^w$
-- statement:
--   The objects of Section 4.1, in the setting of Theorem 4.1 (a DAG whose vertices are numbered in a topological order, edge subgraphs $H_i$, pairs $(s_i,t_i)$, and an element $x_e$ of a commutative ring for every edge).
--
--   Commodity $i$ gets a private source $\sigma_i$ and a private sink $\theta_i$; $H_i^+$ consists of $H_i$ and the arcs $\sigma_i\to s_i$, $t_i\to\theta_i$ of weight $1$, and the order puts all private sources before the real vertices and all private sinks after them. Then:
--
--   1. $N_i(a,b)$ is the total weight of the $a$–$b$ paths in $H_i^+$ (weight = product of edge weights), and $L_i(b)=N_i(\sigma_i,b)$;
--   2. for a real vertex $w$, the **crossing kernel** $K^w_i(c,e)$ is the total weight of the $c$–$e$ paths in $H^+_i$ whose vertices other than $c$ all follow $w$;
--   3. for $|S|\ge2$, a real vertex $v$ and endpoints $c_i<v$ ($i\notin S$), the **prefix table** $\Lambda_S(v;c)$ is the total weight of the tuples $(A_1,\dots,A_k)$, $A_i$ a $\sigma_i$–$v$ path for $i\in S$ and a $\sigma_i$–$c_i$ path otherwise, such that $A_i,A_j$ meet exactly in $\{v\}$ for $i,j\in S$ and are disjoint otherwise;
--   4. $\Omega(e)$ is the set of tuples with $A_i$ a $\sigma_i$–$e_i$ path; a **collision** is a vertex on two of its paths;
--   5. $Y^w_T(e_{-T})=\sum_d\Lambda_T(w;d)\prod_{i\notin T}K^w_i(d_i,e_i)$ over tuples $d_i<w$, and $B^w(e)=\sum_{|T|\ge2}Y^w_T(e_{-T})\prod_{i\in T}N_i(w,e_i)$.
--
--   They express $F$ through first collisions (Lemma 4.2).
--
--   **Formalization Note** Extended vertices are $0,\dots,k+n+k-1$: $\sigma_i=i$, real $v$ is $k+v$, $\theta_i=k+n+i$. Endpoint tuples range over all extended vertices; the private terminals of other commodities are isolated in $H^+_i$ and contribute $0$.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 4.1, pp.10–11

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph

set_option autoImplicit false

namespace DisjointPathsDAG

/-!
# Private terminals, path sums, crossing kernels, prefix tables (Section 4.1)

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 4.1, pp.10–11.

"Give commodity i a private source σi and a private sink θi, and let H+i consist of Hi and the edges
σi → si and ti → θi, whose weights are the constant 1. Extend < so that all private sources precede V
and all private sinks follow V. […] For vertices a, b of H+i, let Ni(a, b) be the total weight of the
a–b paths in H+i ; thus Ni(a, a) = 1, and Ni(a, b) = 0 unless a ≤ b. Put Li(b) := Ni(σi, b)."

"For a real vertex w, a vertex c < w of H+i, and a vertex e of H+i, let the crossing kernel Kwi(c, e) be
the total weight of the c–e paths in H+i whose vertices other than c all follow w."

"For S ⊆ [k] with |S| ≥ 2, a real vertex v, and a tuple c = (ci)i∉S of vertices ci < v of H+i, let
ΛS(v; c) be the total weight of the tuples (A1, . . . , Ak) such that Ai is a σi–v path in H+i for i ∈ S,
Ai is a σi–ci path in H+i for i ∉ S, and two paths Ai, Aj intersect exactly in {v} when i, j ∈ S and are
disjoint otherwise."

"For a tuple e = (e1, . . . , ek) of vertices of H+1, . . . , H+k, let Ω(e) be the set of tuples A of
paths A1, . . . , Ak such that Ai is a σi–ei path in H+i. […] A collision of A is a vertex lying on at
least two of its paths; collisions are real. For a real vertex w and T ⊆ [k] with |T| ≥ 2, write
e−T := (ei)i∉T and define Y wT(e−T) := ∑d ΛT(w; d) ∏i∉T Kwi(di, ei),
Bw(e) := ∑T⊆[k], |T|≥2 Y wT(e−T) ∏i∈T Ni(w, ei), where d ranges over tuples (di)i∉T of vertices
di < w of H+i."

**Formalization Note** This module bundles the Section 4.1 objects.
* The extended vertex set is `Fin (k + n + k)` ordered by value: `src i = i` (the private source
  `σᵢ`), `real v = k + v`, `snk i = k + n + i` (the private sink `θᵢ`). So the private sources precede
  the real vertices, which keep the given order, and the private sinks follow them.
* The arcs of `H⁺ᵢ` are `Sum.inl e` for `e ∈ Hᵢ` (weight `x e`), `Sum.inr false` = `σᵢ → sᵢ` and
  `Sum.inr true` = `tᵢ → θᵢ` (weight `1`). All path sums are sums over the finite sets of paths.
* Endpoint tuples and the tuples `d`, `c` range over all extended vertices. The private terminals of the
  other commodities are isolated vertices of `H⁺ᵢ`; no `σᵢ`-path ends there, so these entries contribute
  `0` and the sums are those of the page. A tuple `c = (cᵢ)_{i ∉ S}` is a full tuple whose entries in `S`
  are ignored (`endpt S v c` puts `v` there), and `d` in `Y` ranges over tuples with `dᵢ = w` for
  `i ∈ T`.
-/

variable {n m k : ℕ}

/-- The extended vertex set `σ₁ < … < σ_k < V < θ₁ < … < θ_k`. -/
abbrev XV (k n : ℕ) := Fin (k + n + k)

/-- The private source `σᵢ`. -/
def src (i : Fin k) : XV k n := ⟨i, by omega⟩

/-- The real vertex `v`. -/
def real (v : Fin n) : XV k n := ⟨k + v, by omega⟩

/-- The private sink `θᵢ`. -/
def snk (i : Fin k) : XV k n := ⟨k + n + i, by omega⟩

/-- Arcs of the extended graphs: a real edge, or (`false`) the source arc, or (`true`) the sink arc. -/
abbrev XArc (m : ℕ) := Fin m ⊕ Bool

/-- The tail of an arc of `H⁺ᵢ`. -/
def xtail (S : Setting n m k) (i : Fin k) : XArc m → XV k n
  | .inl e => real (S.G.tail e)
  | .inr false => src i
  | .inr true => real (S.pairs i).2

/-- The head of an arc of `H⁺ᵢ`. -/
def xhead (S : Setting n m k) (i : Fin k) : XArc m → XV k n
  | .inl e => real (S.G.head e)
  | .inr false => real (S.pairs i).1
  | .inr true => snk i

/-- The arcs of `H⁺ᵢ`: the edges of `Hᵢ` and the two private arcs. -/
def xok (S : Setting n m k) (i : Fin k) : XArc m → Prop
  | .inl e => e ∈ S.H i
  | .inr _ => True

/-- Arc weights: `x e` on a real edge, `1` on the private arcs. -/
def xwt {R : Type} [CommRing R] (x : Fin m → R) : XArc m → R
  | .inl e => x e
  | .inr _ => 1

/-- The finite set of `a`–`b` paths in `H⁺ᵢ`. -/
noncomputable def xpaths (S : Setting n m k) (i : Fin k) (a b : XV k n) : Finset (List (XArc m)) :=
  pathsOf (xtail S i) (xhead S i) (xok S i) a b

/-- The weight of a path: the product of its arc weights. -/
def xpathWt {R : Type} [CommRing R] (x : Fin m → R) (p : List (XArc m)) : R :=
  (p.map (xwt x)).prod

/-- `Nᵢ(a, b)`: the total weight of the `a`–`b` paths in `H⁺ᵢ`. -/
noncomputable def Npath {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R) (i : Fin k)
    (a b : XV k n) : R :=
  ∑ p ∈ xpaths S i a b, xpathWt x p

/-- `Lᵢ(b) := Nᵢ(σᵢ, b)`. -/
noncomputable def Lsum {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R) (i : Fin k)
    (b : XV k n) : R :=
  Npath S x i (src i) b

/-- The crossing kernel `Kʷᵢ(c, e)`: the total weight of the `c`–`e` paths in `H⁺ᵢ` whose vertices
other than `c` all follow the real vertex `w`. -/
noncomputable def Kker {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R) (i : Fin k)
    (w : Fin n) (c e : XV k n) : R := by
  classical
  exact ∑ p ∈ (xpaths S i c e).filter (fun p => ∀ v ∈ p.map (xhead S i), real w < v), xpathWt x p

/-- `Ω(e)`: the tuples `A` with `Aᵢ` a `σᵢ`–`eᵢ` path in `H⁺ᵢ`. -/
noncomputable def Omega (S : Setting n m k) (e : Fin k → XV k n) : Finset (Fin k → List (XArc m)) :=
  Fintype.piFinset fun i => xpaths S i (src i) (e i)

/-- The weight of a tuple of paths: the product of their weights. -/
def tupleWt {R : Type} [CommRing R] (x : Fin m → R) (A : Fin k → List (XArc m)) : R :=
  ∏ i, xpathWt x (A i)

/-- The vertex set of path `Aᵢ` (started at `σᵢ`). -/
def tupleVerts (S : Setting n m k) (A : Fin k → List (XArc m)) (i : Fin k) : Finset (XV k n) :=
  (walkVerts (xhead S i) (src i) (A i)).toFinset

/-- `v` is a collision of `A`: it lies on at least two of its paths. -/
def IsCollision (S : Setting n m k) (A : Fin k → List (XArc m)) (v : XV k n) : Prop :=
  ∃ i j, i ≠ j ∧ v ∈ tupleVerts S A i ∧ v ∈ tupleVerts S A j

/-- The earliest collision of `A` is the real vertex `w`. -/
def IsEarliestCollision (S : Setting n m k) (A : Fin k → List (XArc m)) (w : Fin n) : Prop :=
  IsCollision S A (real w) ∧ ∀ v, IsCollision S A v → real w ≤ v

/-- The endpoint tuple `e(S, v, c)`: `eᵢ = v` for `i ∈ S`, `eᵢ = cᵢ` otherwise. -/
def endpt (T : Finset (Fin k)) (v : Fin n) (c : Fin k → XV k n) : Fin k → XV k n :=
  fun i => if i ∈ T then real v else c i

/-- The prefix table `Λ_T(v; c)`: the total weight of the tuples of `Ω(e(T, v, c))` whose paths `Aᵢ`,
`Aⱼ` meet exactly in `{v}` when `i, j ∈ T` and are disjoint otherwise. -/
noncomputable def Lam {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R)
    (T : Finset (Fin k)) (v : Fin n) (c : Fin k → XV k n) : R := by
  classical
  exact ∑ A ∈ (Omega S (endpt T v c)).filter (fun A => ∀ i j, i ≠ j →
      if i ∈ T ∧ j ∈ T then tupleVerts S A i ∩ tupleVerts S A j = {real v}
      else Disjoint (tupleVerts S A i) (tupleVerts S A j)), tupleWt x A

/-- `Yʷ_T(e_{−T}) := ∑_d Λ_T(w; d) ∏_{i ∉ T} Kʷᵢ(dᵢ, eᵢ)`, `d` over the tuples with `dᵢ < w` for
`i ∉ T` (and `dᵢ = w` for `i ∈ T`, ignored by `Λ_T`). -/
noncomputable def Yt {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R)
    (T : Finset (Fin k)) (w : Fin n) (e : Fin k → XV k n) : R := by
  classical
  exact ∑ d ∈ Fintype.piFinset (fun i => if i ∈ T then ({real w} : Finset (XV k n))
      else Finset.univ.filter (· < real w)),
    Lam S x T w d * ∏ i ∈ Finset.univ.filter (· ∉ T), Kker S x i w (d i) (e i)

/-- `Bʷ(e) := ∑_{T ⊆ [k], |T| ≥ 2} Yʷ_T(e_{−T}) ∏_{i ∈ T} Nᵢ(w, eᵢ)`. -/
noncomputable def Bw {R : Type} [CommRing R] (S : Setting n m k) (x : Fin m → R) (w : Fin n)
    (e : Fin k → XV k n) : R := by
  classical
  exact ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun T => 2 ≤ T.card),
    Yt S x T w e * ∏ i ∈ T, Npath S x i (real w) (e i)

end DisjointPathsDAG


