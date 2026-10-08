-- Prove2me | Definitions.Def_MetricGenerators_FewComponents_Gadget
-- name    : MetricGenerators_FewComponents_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:30.023023+00:00
-- url     : https://prove2.me/theorems/4169c56f-d17f-4cff-afa6-1b2d4771b200
-- title:
--   The graph G built from a 3DM instance in the proof of Theorem 5 (§3.1, p. 390, Figure 3), its set T = W ∪ X ∪ Y ∪ Z, and the T-join of a matching
-- statement:
--   Let $W$, $X$, $Y$ and $H\subseteq W\times X\times Y$ be an instance of 3DM with $q=|W|=|X|=|Y|$, and let $Z$ be a further set of $q$ points disjoint from the others. Put $T:=W\cup X\cup Y\cup Z$, so $|T|=4q$. The graph $G$ has vertex set
--
--   $$V(G)=T\ \cup\ H\ \cup\ \{p_{ab} : \{a,b\}\subseteq T,\ a\neq b\},$$
--
--   with one new vertex $p_{ab}$ for every unordered pair of distinct vertices of $T$. Its edges are:
--
--   1. $a\,p_{ab}$ and $p_{ab}\,b$ for every pair $\{a,b\}$, so every two vertices of $T$ are joined by a path of length 2 through $p_{ab}$;
--   2. for every $h=(w,x,y)\in H$, the edges $hw$, $hx$, $hy$ and $hz$ for every $z\in Z$.
--
--   There are no other edges. In particular $T$ induces no edge, and every edge of $G$ has exactly one end in $T$.
--
--   For a matching $M\subseteq H$ and an indexing $Z=\{z_m : m\in M\}$, the **edge set of the matching** is
--
--   $$F_M=\bigcup\big\{\{mw,\ mx,\ my,\ mz_m\} : m=(w,x,y)\in M\big\}.$$
--
--   This is the instance of the problem MTSC that Sebő and Tannier use to reduce 3DM to MTSC.
--
--   **Formalization Note.** The vertices of $T$ are pairs $(i,j)$ with class $i\in\{0,1,2,3\}$ ($0=W$, $1=X$, $2=Y$, $3=Z$) and $j\in\{0,\dots,q-1\}$. A midpoint is indexed by a non-diagonal unordered pair of $T$-vertices, and an $H$-vertex by an element of $H$. The indexing of $Z$ by $M$ is a map $\sigma$ with $z_m=(3,\sigma(m))$; the theorem that uses $F_M$ requires $\sigma$ to be a bijection.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 390, §3.1, proof of Theorem 5 (construction of G, Figure 3); p. 391 (the T-join of a matching)

import Mathlib

namespace MetricGenerators.FewComponents

/-- The vertices of the graph `G` built from an instance `(W, X, Y, H)` of 3DM in the proof of
Theorem 5 (Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393
(2004), §3.1, p. 390):

* `t (i, j)`: the vertices of `T = W ∪ X ∪ Y ∪ Z`; the class `i : Fin 4` is `0 = W`, `1 = X`,
  `2 = Y`, `3 = Z`, and `j : Fin q` is the element of that class;
* `mid e`: the inner vertex of the path of length 2 joining the two distinct `T`-vertices of the
  unordered pair `e` (one for every pair);
* `h m`: the vertex of the triple `m ∈ H`. -/
inductive GVert (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : Type
  | t : Fin 4 × Fin q → GVert q H
  | mid : {e : Sym2 (Fin 4 × Fin q) // ¬ e.IsDiag} → GVert q H
  | h : ↥H → GVert q H
  deriving DecidableEq

/-- The `T`-vertices adjacent to the vertex of the triple `m = (w, x, y) ∈ H`: `w ∈ W`, `x ∈ X`,
`y ∈ Y` and all the points of `Z`. -/
def HNbr {q : ℕ} (m : Fin q × Fin q × Fin q) (a : Fin 4 × Fin q) : Prop :=
  a = (0, m.1) ∨ a = (1, m.2.1) ∨ a = (2, m.2.2) ∨ a.1 = 3

/-- Adjacency of the graph `G` of the proof of Theorem 5 (p. 390): a `T`-vertex is adjacent to the
midpoint of every pair containing it, and the vertex of `h = (w, x, y) ∈ H` is adjacent to `w`,
`x`, `y` and all the points of `Z`. There are no other edges (none inside `T`, none between two
`H`-vertices or two midpoints, none between an `H`-vertex and a midpoint). -/
def gadgetAdj {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)} : GVert q H → GVert q H → Prop
  | .t a, .mid e => a ∈ e.1
  | .mid e, .t a => a ∈ e.1
  | .t a, .h m => HNbr m.1 a
  | .h m, .t a => HNbr m.1 a
  | _, _ => False

/-- The graph `G` constructed from an instance of 3DM in the proof of Theorem 5 (Sebő and Tannier
2004, §3.1, p. 390, Figure 3):
"• Let V′(G) := W ∪ X ∪ Y ∪ Z ∪ H, where Z is a set disjoint from the others, |Z| = q. Let
T := W ∪ X ∪ Y ∪ Z (|T| = 4q).
• Join every pair of vertices in T by a path of length 2 (the vertex inside the path is a new
vertex of the graph). This achieves the definition of V(G).
• Join each vertex h = (w, x, y) ∈ H, to w, x, y and all the points of Z." -/
def gadget (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : SimpleGraph (GVert q H) where
  Adj := gadgetAdj
  symm := ⟨fun a b hab => by cases a <;> cases b <;> simp_all [gadgetAdj]⟩
  loopless := ⟨fun a ha => by cases a <;> simp_all [gadgetAdj]⟩

/-- The set `T = W ∪ X ∪ Y ∪ Z` of `4q` vertices of the graph `G` (p. 390). -/
def gadgetT (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) : Finset (GVert q H) :=
  (Finset.univ : Finset (Fin 4 × Fin q)).image GVert.t

/-- The edge set built from a matching in the proof of Theorem 5 (p. 391): "If M is a matching,
then Z can be indexed with M: Z = {z_m : m ∈ M}. Now ⋃{{mw, mx, my, mz_m} : m = (w, x, y) ∈ M}".
For every `m = (w, x, y) ∈ M` it contains the four edges joining the vertex of `m` to `w`, `x`,
`y` and `z_m`.

**Formalization Note.** `M ⊆ H` is passed as `hMH` (so that every `m ∈ M` is a vertex of `G`), and
the indexing of `Z` by `M` is a map `σ : M → Fin q`, `z_m = (3, σ m)`; the theorem that uses this
definition takes `σ` to be a bijection. -/
def matchingJoin {q : ℕ} {H : Finset (Fin q × Fin q × Fin q)}
    (M : Finset (Fin q × Fin q × Fin q)) (hMH : M ⊆ H) (σ : ↥M → Fin q) :
    Finset (Sym2 (GVert q H)) :=
  M.attach.biUnion fun m =>
    let v : GVert q H := GVert.h ⟨m.1, hMH m.2⟩
    {s(v, GVert.t (0, m.1.1)), s(v, GVert.t (1, m.1.2.1)), s(v, GVert.t (2, m.1.2.2)),
      s(v, GVert.t (3, σ m))}

end MetricGenerators.FewComponents


