-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_Multigraph
-- name    : ConstrainedDirSep_STSep_Multigraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:06:36.225711+00:00
-- url     : https://prove2.me/theorems/8bc1c358-acc9-417c-bea8-cd1a5f274b62
-- title:
--   Capacitated multigraphs, arc cuts, minimum cuts, parallel expansion, G + A and the split graph
-- statement:
--   A **directed multigraph** has a vertex type and an arc type; each arc has a tail and a head, so parallel arcs stay distinct. Arcs may have **capacity** $1$ or $+\infty$. For vertices $s,t$, an **$s$–$t$ arc cut** is a set $Z$ of arcs whose removal leaves no directed walk from $s$ to $t$; it is inclusion-minimal if no proper subset is one. The **value** of a finite arc set is the sum of capacities (in $\mathbb N\cup\{\infty\}$); the **minimum $s$–$t$ cut value** is the least value of a finite cut ($\infty$ if none), and a **minimum cut** is a cut attaining it.
--
--   - **Parallel expansion** $H$ of $G'$ with parameter $k$: every infinite-capacity arc is replaced by $k+1$ parallel capacity-one copies; capacity-one arcs are kept (as copy $0$).
--   - **$G+A$** for a set $A$ of ordered vertex pairs: one infinite-capacity arc is added for every pair in $A$, in parallel to any arc of $G$ already joining that pair.
--   - **Split graph** $G$ of a digraph $D$ with terminals $s,t$: every nonterminal $v$ becomes $v^-,v^+$ joined by the capacity-one split arc $e_v=(v^-,v^+)$; $s^\pm=s$, $t^\pm=t$; every arc $uv$ of $D$ becomes the infinite-capacity arc $u^+v^-$. $Z_S=\{e_v: v\in S\}$.
--   - Capacitated digraphs without parallel arcs on $\{0,\dots,n-1\}$ are encoded by $\mathrm{enc}(n)$ and two bits per ordered pair (arc present; infinite capacity); a family of pair sets by a $1$ and the $n^2$ membership bits of each member, then a $0$.
--
--   **Formalization Note.** The split graph's vertices are two copies of $\{0,\dots,n-1\}$; the second copies of $s$ and $t$ are isolated and change no reachability or cut.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 14 (PDF 17), §3 (arc cuts, capacities, value); pp. 19–20 (PDF 22–23), §5.1.1 (split graph, Theorem 5.4's G + A, parallel expansion)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Encoding

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **Directed multigraph.** Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027
submission (manuscript sha256 4dd06c29…), §3, p. 13 (PDF 16): "Auxiliary digraphs may contain
parallel arcs." Vertices form the type `V`, arcs the type `A`; every arc has a tail and a head.

**Formalization Note.** Arcs are an indexed family, not a relation, so parallel arcs (several arcs
with the same tail and head) stay distinct. -/
structure Multigraph (V A : Type*) where
  /-- the tail of an arc -/
  tail : A → V
  /-- the head of an arc -/
  head : A → V

/-- **Directed multigraph with arc capacities in `{1, +∞}`.** §3, p. 14 (PDF 17): "Auxiliary
digraphs may have arc capacities in {1, +∞}." `inf a = true` means capacity `+∞`, otherwise
capacity `1`. -/
structure CapMultigraph (V A : Type*) extends Multigraph V A where
  /-- `true` for an infinite-capacity arc, `false` for a capacity-one arc -/
  inf : A → Bool

/-- **An arc of `G − Z` from `u` to `v`.** -/
def Multigraph.avoidStep {V A : Type*} (G : Multigraph V A) (Z : Set A) (u v : V) : Prop :=
  ∃ a : A, a ∉ Z ∧ G.tail a = u ∧ G.head a = v

/-- **s–t arc cut.** §3, p. 14 (PDF 17): "an s–t arc cut is a set Z of its arcs whose removal
leaves no directed path from s to t" (walks and paths are interchangeable, §3, p. 13). -/
def Multigraph.IsArcCut {V A : Type*} (G : Multigraph V A) (s t : V) (Z : Set A) : Prop :=
  ¬ Relation.ReflTransGen (G.avoidStep Z) s t

/-- **Inclusion-minimal s–t arc cut** (§3, p. 14, PDF 17). -/
def Multigraph.IsMinimalArcCut {V A : Type*} (G : Multigraph V A) (s t : V) (Z : Set A) : Prop :=
  G.IsArcCut s t Z ∧ ∀ Z' : Set A, Z' ⊂ Z → ¬ G.IsArcCut s t Z'

/-- **Value of an arc set.** §3, p. 14 (PDF 17): "The value of an arc cut is the sum of the
capacities of its arcs", in `ℕ∞` (an infinite-capacity arc contributes `⊤`). -/
def CapMultigraph.cutValue {V A : Type*} (G : CapMultigraph V A) (Z : Finset A) : ℕ∞ :=
  ∑ a ∈ Z, if G.inf a then (⊤ : ℕ∞) else 1

/-- **Minimum s–t cut value**, the least value of a (finite) s–t arc cut, in `ℕ∞`; it is `⊤` when
no finite-value cut exists (e.g. `s = t`). -/
noncomputable def CapMultigraph.minCutValue {V A : Type*} (G : CapMultigraph V A) (s t : V) : ℕ∞ :=
  ⨅ (Z : Finset A) (_ : G.toMultigraph.IsArcCut s t (Z : Set A)), G.cutValue Z

/-- **Minimum s–t cut**: an s–t arc cut whose value is the minimum s–t cut value. -/
def CapMultigraph.IsMinCut {V A : Type*} (G : CapMultigraph V A) (s t : V) (Z : Finset A) : Prop :=
  G.toMultigraph.IsArcCut s t (Z : Set A) ∧ G.cutValue Z = G.minCutValue s t

/-- **Arcs of the parallel expansion.** §5.1.1, p. 20 (PDF 23): "replace every infinite-capacity
arc by k + 1 parallel capacity-one copies". The copy `i ∈ Fin (k + 1)` of arc `a` exists for every
`i` if `a` has infinite capacity, and only for `i = 0` (the arc itself) if `a` has capacity one. -/
def ExpArc {V A : Type*} (G : CapMultigraph V A) (k : ℕ) : Type _ :=
  {p : A × Fin (k + 1) // G.inf p.1 = true ∨ p.2 = 0}

/-- **Parallel expansion `H` of `G′`** (§5.1.1, p. 20, PDF 23; Lemma 5.5): every arc copy keeps
the tail and head of its origin and has capacity one. -/
def CapMultigraph.expand {V A : Type*} (G : CapMultigraph V A) (k : ℕ) :
    CapMultigraph V (ExpArc G k) where
  tail p := G.tail p.1.1
  head p := G.head p.1.1
  inf _ := false

/-- **A capacity-one arc of `G′` as an arc of its parallel expansion** (its unique copy `0`). -/
def CapMultigraph.unitArc {V A : Type*} (G : CapMultigraph V A) (k : ℕ) (a : A) : ExpArc G k :=
  ⟨(a, 0), Or.inr rfl⟩

/-- **No parallel arcs**: two arcs with the same tail and the same head are equal. -/
def Multigraph.NoParallel {V A : Type*} (G : Multigraph V A) : Prop :=
  ∀ a b : A, G.tail a = G.tail b → G.head a = G.head b → a = b

/-- **`G + A`.** §5.1.1, Theorem 5.4, p. 19 (PDF 22): "G + A is obtained from G by adding, for
every ordered pair in A, one infinite-capacity arc with that tail and head, in parallel to any arc
of G already joining the same pair." Arcs of `G` are `Sum.inl`, added arcs `Sum.inr`. -/
def CapMultigraph.augment {V A : Type*} (G : CapMultigraph V A) (Aug : Finset (V × V)) :
    CapMultigraph V (A ⊕ {p : V × V // p ∈ Aug}) where
  tail := Sum.elim G.tail fun p => p.1.1
  head := Sum.elim G.head fun p => p.1.2
  inf := Sum.elim G.inf fun _ => true

/-- **Arcs of the split graph** of a digraph `D` with terminals `s`, `t` (§5.1.1, p. 19, PDF 22):
one split arc `e_v` for every nonterminal `v` (`Sum.inl`), and one arc `u⁺v⁻` for every arc `uv` of
`D` (`Sum.inr`). -/
abbrev SplitArc {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) : Type :=
  {v : Fin n // v ≠ s ∧ v ≠ t} ⊕ {uv : Fin n × Fin n // D.Adj uv.1 uv.2}

/-- The vertex `v⁻` of the split graph (`Sum.inl v`; for a terminal, `s⁻ = s`, `t⁻ = t`). -/
def splitMinus {n : ℕ} (v : Fin n) : Fin n ⊕ Fin n := Sum.inl v

/-- The vertex `v⁺` of the split graph (`Sum.inr v` for a nonterminal; `s⁺ = s = Sum.inl s` and
`t⁺ = t = Sum.inl t` for the terminals, which are not split). -/
def splitPlus {n : ℕ} (s t v : Fin n) : Fin n ⊕ Fin n :=
  if v = s ∨ v = t then Sum.inl v else Sum.inr v

/-- **The split graph `G` of `D`.** §5.1.1, p. 19 (PDF 22): "For every v ∈ V(D) \ {s, t}, create
vertices v−, v+ and the capacity-one arc e_v = (v−, v+). The terminals are not split. Write
s− = s+ = s and t− = t+ = t. For every arc uv ∈ A(D), add the infinite-capacity arc u+v−."

**Formalization Note.** Vertices are `Fin n ⊕ Fin n`: `v⁻ = Sum.inl v`, `v⁺ = Sum.inr v` for a
nonterminal, and the terminals are `Sum.inl s`, `Sum.inl t`. The two vertices `Sum.inr s` and
`Sum.inr t` are isolated (no arc touches them); they change no reachability and no cut. -/
def splitGraph {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) :
    CapMultigraph (Fin n ⊕ Fin n) (SplitArc D s t) where
  tail := Sum.elim (fun v => splitMinus v.1) (fun uv => splitPlus s t uv.1.1)
  head := Sum.elim (fun v => Sum.inr v.1) (fun uv => splitMinus uv.1.2)
  inf := Sum.elim (fun _ => false) (fun _ => true)

/-- **`Z_S = {e_v : v ∈ S}`** (Lemma 5.3, p. 19, PDF 22), as a set of arcs of the split graph. -/
def splitArcsOf {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) (S : Finset (Fin n)) :
    Set (SplitArc D s t) :=
  {a | ∃ v : {v : Fin n // v ≠ s ∧ v ≠ t}, v.1 ∈ S ∧ a = Sum.inl v}

/-- **All ordered pairs of `Fin n`**, row by row. -/
def finPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

open Classical in
/-- **Input word of a capacitated digraph without parallel arcs on `Fin n`** (Theorem 5.4,
p. 19, PDF 22): `encNat n`, then for every ordered pair `(u, v)` two bits: whether an arc `uv`
exists, and whether it has infinite capacity. -/
noncomputable def encCapDigraph {n : ℕ} {A : Type*} (G : CapMultigraph (Fin n) A) : List Bool :=
  encNat n ++ (finPairs n).flatMap fun uv =>
    [decide (∃ a, G.tail a = uv.1 ∧ G.head a = uv.2),
     decide (∃ a, G.tail a = uv.1 ∧ G.head a = uv.2 ∧ G.inf a = true)]

/-- **Output word of a family of sets of ordered pairs** `A_1, …, A_m ⊆ V(G) × V(G)` (Theorem 5.4):
for each member the bit `true` followed by its membership bits over `finPairs n`, then `false`. -/
noncomputable def encPairFamily {n : ℕ} (fam : List (Finset (Fin n × Fin n))) : List Bool :=
  fam.flatMap (fun Aug => true :: charBits (· ∈ Aug) (finPairs n)) ++ [false]

end ConstrainedDirSep.STSep


