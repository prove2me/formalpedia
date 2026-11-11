-- Prove2me | Definitions.Def_ReconfRes_Frozen_Construction
-- name    : ReconfRes_Frozen_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:23:21.358904+00:00
-- url     : https://prove2.me/theorems/fd19c317-c1be-4bd0-ae86-484c38a0ddc8
-- title:
--   The modified frozen construction of §3.13 (b = n+2k+2, W = β+q+1), the decoders X(R) and I(R), and the canonical proofs R_X with indexed units P_v, Q_v
-- statement:
--   Fix a simple graph $J_0$ on $n\ge2$ vertices, $1\le K\le n-1$ and $k\ge2$. Put $b=n+2k+2$; $J$ replaces every vertex of $J_0$ by $b$ independent twins and every edge by all edges between the twin groups; $m=bn$, $\ell=bK$, $q=m-\ell$, $r=q-1$, $\beta=4m-1$, $W=\beta+q+1$, $\alpha=10m+r-2$.
--
--   Heads $T,U,a_v,b_v$ ($v\in V(J)$); any rooted full binary tree with root $T$ and leaves $a_v$, any with root $U$ and leaves $b_v$, and a distinct head for every other internal tree vertex; $\mathcal H$ is the set of these heads, and $A$ one more head. $D_h$ is the set of children of $h$ (parent before child in either tree, $T$ before $U$, $a_v$ before $b_u$ for $uv\in E(J)$). Facts $z_h$, $f_v$, $p_1,\dots,p_r$; $X_T=\{f_v\}$, $X_{a_v}=X_{b_v}=\{f_v\}$, $X_U=\{p_j\}$, $X_h=\emptyset$ otherwise.
--   $$C_h=\{h,\neg A,\neg z_h\}\cup\{\neg d:d\in D_h\}\cup\{\neg x:x\in X_h\},\quad C_A=\{A\}\cup\{\neg z_h\}\cup\{\neg p_j\},\quad G=\{\neg A\}\cup\{\neg h:h\in\mathcal H\}.$$
--   The frozen inventory has one node of each $C_h$, $C_A$, $G$, $z_h$, $p_j$ and two unit nodes $P_v$, $Q_v$ of each $f_v$. A **tight** refutation is a lean refutation of $F$ (the set of these clauses) with this axiom multiset and size at most $2\alpha-1$. $v\in X(R)$ iff resolution nodes with pivots $f_v$, $a_v$, $b_v$ exist with the $f_v$-pivot node an ancestor of both others; $I(R)$ is the set of original vertices with at least two twins in $X(R)$.
--
--   The **canonical proof** $R_X$ of an independent $X\subseteq V(J)$ (Lemma 3.58) is the comb whose goal path, starting at $G$, expands $T$ prepared by deleting $f_v$ with $P_v$ for $v\in X$; the first-tree internal heads; for each $v\notin X$ raw $a_v$ then deletion of $f_v$ with $Q_v$; $U$ and the second-tree internal heads; for each $v\in X$ the packet $a_v,b_v$, deletion of $f_v$ with $Q_v$; for each $v\notin X$ the $b_v$ prepared with $P_v$; $A$; and the deletions of all $z_h,p_j$.
--
--   **Formalization Note.** Trees are `FBTree`s whose leaf list is a permutation of $V(J)$; internal vertices are addressed by their paths. The orders of tree internals (consistent with the dependencies) and of the final deletions are `CanonOrders`; the orders of the private $T$ deletions, unselected pairs, selected packets and prepared $b$ heads are `SetOrders`. `IsCombPresentation` says that a refutation with indexed sources is, up to renaming, the comb of these events, its clauses computed by resolution along the comb.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 72–76 (construction, X(R), Lemma 3.58), p. 80 (modified parameters, I(R)), p. 81 (P_v, Q_v)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover

open MultiplierAssoc206.Resolution Classical

noncomputable section

namespace ReconfRes.Frozen

/-!
# The frozen construction of §3.13 in its modified form (p. 80), its decoders and its canonical
proofs

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.13: construction
pp. 72–73, the decoder `X(R)` p. 73 and test (∗) p. 74, canonical proofs (Lemma 3.58) pp. 75–76,
the modified parameters and the decoder `I(R)` p. 80, the indexed fact units `P_v`, `Q_v` p. 81.

Data: a simple graph `J₀` on `Fin n`, an integer `K`, the fixed locality `k`, and two rooted full
binary trees whose leaves are the vertices of `J` (each exactly once): the paper says "choose" a
tree, so every such pair is allowed. With `b = n + 2k + 2`, the graph `J` has the vertices
`Fin n × Fin b` (`b` independent twins per vertex of `J₀`, all edges between the twin groups of
adjacent vertices); `m = bn`, `ℓ = bK`, `q = m − ℓ`, `r = q − 1`, `β = 4m − 1`, `W = β + q + 1`,
`α = 10m + r − 2`.

An internal vertex of a tree is addressed by its path from the root (`false` = left child); the
root of the first tree carries the head `T`, that of the second `U`, a leaf `v` carries `a_v`
(first tree) or `b_v` (second tree), and every other internal vertex its own head `i1 p` or
`i2 p`.
-/

/-- A rooted full binary tree with leaves labelled in `τ`: every internal vertex has exactly two
children. -/
inductive FBTree (τ : Type) where
  | leaf : τ → FBTree τ
  | node : FBTree τ → FBTree τ → FBTree τ

namespace FBTree

variable {τ : Type}

/-- The leaves, left to right. -/
def leaves : FBTree τ → List τ
  | leaf v => [v]
  | node l r => l.leaves ++ r.leaves

/-- The subtree at a path from the root (`false` = left). -/
def subtreeAt : FBTree τ → List Bool → Option (FBTree τ)
  | t, [] => some t
  | leaf _, _ :: _ => none
  | node l _, false :: p => l.subtreeAt p
  | node _ r, true :: p => r.subtreeAt p

/-- The paths of the internal vertices. -/
def internalPaths : FBTree τ → List (List Bool)
  | leaf _ => []
  | node l r => [] :: (l.internalPaths.map (false :: ·) ++ r.internalPaths.map (true :: ·))

/-- Every element of `τ` is a leaf, exactly once. -/
def LeavesExactly [Fintype τ] (t : FBTree τ) : Prop := t.leaves.Nodup ∧ ∀ v, v ∈ t.leaves

end FBTree

/-- The heads `T`, `U`, `a_v`, `b_v` and the internal tree heads. -/
inductive Head (τ : Type) where
  | T | U
  | a (v : τ) | b (v : τ)
  | i1 (p : List Bool) | i2 (p : List Bool)
  deriving DecidableEq

/-- The variables of the construction: heads, the extra head `A`, compensators `z_h`, vertex
facts `f_v` and ballast facts `p_j`. -/
inductive CVar (τ : Type) where
  | hd (h : Head τ) | A | z (h : Head τ) | f (v : τ) | p (j : ℕ)
  deriving DecidableEq

/-- The source occurrences (the frozen inventory): one defining axiom `C h` per head, `C_A`, the
goal `G`, one unit per compensator and ballast fact, and the two indexed units `P v`, `Q v` of
each vertex fact (p. 81). -/
inductive Src (τ : Type) where
  | C (h : Head τ) | CA | G | z (h : Head τ) | p (j : ℕ) | P (v : τ) | Q (v : τ)
  deriving DecidableEq

/-- The data of the modified construction. -/
structure ConstrData where
  /-- number of vertices of `J₀` -/
  n : ℕ
  /-- the bound `K` -/
  K : ℕ
  /-- the fixed locality `k` -/
  k : ℕ
  /-- the source graph `J₀` -/
  J0 : SimpleGraph (Fin n)
  /-- the first tree (root `T`, leaves `a_v`) -/
  t1 : FBTree (Fin n × Fin (n + 2 * k + 2))
  /-- the second tree (root `U`, leaves `b_v`) -/
  t2 : FBTree (Fin n × Fin (n + 2 * k + 2))

namespace ConstrData

variable (D : ConstrData)

/-- Twin group size `b = n + 2k + 2`. -/
abbrev b : ℕ := D.n + 2 * D.k + 2
/-- The vertices of `J`. -/
abbrev TV : Type := Fin D.n × Fin (D.n + 2 * D.k + 2)

/-- The hypotheses of the construction: `n ≥ 2`, `1 ≤ K ≤ n − 1`, `k ≥ 2`, and both trees have
the vertices of `J` as leaves, each exactly once. -/
def Valid : Prop :=
  2 ≤ D.n ∧ 1 ≤ D.K ∧ D.K + 1 ≤ D.n ∧ 2 ≤ D.k ∧ D.t1.LeavesExactly ∧ D.t2.LeavesExactly

/-- `m = bn`. -/
def m : ℕ := D.b * D.n
/-- `ℓ = bK`. -/
def ℓ : ℕ := D.b * D.K
/-- `q = m − ℓ`. -/
def q : ℕ := D.m - D.ℓ
/-- `r = q − 1`. -/
def r : ℕ := D.q - 1
/-- `β = 4m − 1`. -/
def β : ℕ := 4 * D.m - 1
/-- `W = β + q + 1`. -/
def W : ℕ := D.β + D.q + 1
/-- `α = 10m + r − 2`, the number of source occurrences. -/
def α : ℕ := 10 * D.m + D.r - 2

/-- Adjacency in `J`: twins of adjacent vertices of `J₀`. -/
def J : SimpleGraph D.TV := D.J0.comap Prod.fst

/-- The head of the vertex at path `p` of the first tree. -/
def head1 (p : List Bool) : Head D.TV :=
  match D.t1.subtreeAt p with
  | some (.leaf v) => .a v
  | some (.node _ _) => if p = [] then .T else .i1 p
  | none => .T

/-- The head of the vertex at path `p` of the second tree. -/
def head2 (p : List Bool) : Head D.TV :=
  match D.t2.subtreeAt p with
  | some (.leaf v) => .b v
  | some (.node _ _) => if p = [] then .U else .i2 p
  | none => .U

/-- The internal non-root heads of the first tree. -/
def inner1 : Finset (Head D.TV) :=
  ((D.t1.internalPaths.filter fun p => p ≠ []).toFinset).image Head.i1

/-- The internal non-root heads of the second tree. -/
def inner2 : Finset (Head D.TV) :=
  ((D.t2.internalPaths.filter fun p => p ≠ []).toFinset).image Head.i2

/-- The set `𝓗` of all heads (`|𝓗| = 4m − 2`). -/
def heads : Finset (Head D.TV) :=
  {Head.T, Head.U} ∪ Finset.univ.image Head.a ∪ Finset.univ.image Head.b ∪ D.inner1 ∪ D.inner2

/-- `D_h`: the children of `h` under the dependencies (parent before child in either tree,
`T` before `U`, `a_v` before `b_u` whenever `uv ∈ E(J)`). -/
def deps : Head D.TV → Finset (Head D.TV)
  | .T => {D.head1 [false], D.head1 [true], Head.U}
  | .U => {D.head2 [false], D.head2 [true]}
  | .i1 p => {D.head1 (p ++ [false]), D.head1 (p ++ [true])}
  | .i2 p => {D.head2 (p ++ [false]), D.head2 (p ++ [true])}
  | .a v => (Finset.univ.filter fun u => D.J.Adj v u).image Head.b
  | .b _ => ∅

/-- The ballast indices `1, …, r`. -/
def ballast : Finset ℕ := Finset.Icc 1 D.r

/-- `X_h`: the facts of the defining axiom of `h`. -/
def Xh : Head D.TV → Finset (CVar D.TV)
  | .T => Finset.univ.image CVar.f
  | .a v => {CVar.f v}
  | .b v => {CVar.f v}
  | .U => D.ballast.image CVar.p
  | _ => ∅

/-- `C_h = {h, ¬A, ¬z_h} ∪ {¬d : d ∈ D_h} ∪ {¬x : x ∈ X_h}`. -/
def Ch (h : Head D.TV) : Clause (CVar D.TV) :=
  {(CVar.hd h, true), (CVar.A, false), (CVar.z h, false)} ∪
    (D.deps h).image (fun d => (CVar.hd d, false)) ∪ (D.Xh h).image (fun x => (x, false))

/-- `C_A = {A} ∪ {¬z_h : h ∈ 𝓗} ∪ {¬p_j : 1 ≤ j ≤ r}`. -/
def CA : Clause (CVar D.TV) :=
  {(CVar.A, true)} ∪ D.heads.image (fun h => (CVar.z h, false)) ∪
    D.ballast.image (fun j => (CVar.p j, false))

/-- The negative goal `G = {¬A} ∪ {¬h : h ∈ 𝓗}`. -/
def Gc : Clause (CVar D.TV) :=
  {(CVar.A, false)} ∪ D.heads.image (fun h => (CVar.hd h, false))

/-- The source occurrences of the frozen inventory. -/
def srcs : Finset (Src D.TV) :=
  D.heads.image Src.C ∪ {Src.CA, Src.G} ∪ D.heads.image Src.z ∪ D.ballast.image Src.p ∪
    Finset.univ.image Src.P ∪ Finset.univ.image Src.Q

/-- The clause of each source occurrence; `P v` and `Q v` are the two unit nodes of `f_v`. -/
def inv : Src D.TV → Clause (CVar D.TV)
  | .C h => D.Ch h
  | .CA => D.CA
  | .G => D.Gc
  | .z h => {(CVar.z h, true)}
  | .p j => {(CVar.p j, true)}
  | .P v => {(CVar.f v, true)}
  | .Q v => {(CVar.f v, true)}

/-- The formula `F` of the construction: the set of the inventory clauses. -/
def formula : CNF (CVar D.TV) := D.srcs.image D.inv

/-- The prescribed frozen axiom multiset: one node of each `C_h`, `C_A`, `G`, `z_h`, `p_j` and two
unit nodes of each `f_v`. -/
def inventory : Multiset (Clause (CVar D.TV)) := D.srcs.val.map D.inv

/-- A tight refutation: a lean refutation of `F` with the prescribed axiom multiset and size at
most `2α − 1`. -/
def IsTight (R : ProofDag (CVar D.TV)) : Prop :=
  R.IsRefutationOf D.formula ∧ R.IsLean ∧ R.axiomMultiset = D.inventory ∧ R.size + 1 ≤ 2 * D.α

/-- The ancestry-selected set `X(R)` (test (∗), p. 74): `v ∈ X(R)` iff there are resolution nodes
with pivots `f_v`, `a_v`, `b_v` such that the `f_v`-pivot node is an ancestor of both the `a_v`-
and the `b_v`-pivot nodes. -/
def selected (R : ProofDag (CVar D.TV)) : Finset D.TV :=
  Finset.univ.filter fun v => ∃ x y z,
    R.HasPivot x (CVar.f v) ∧ R.HasPivot y (CVar.hd (Head.a v)) ∧
    R.HasPivot z (CVar.hd (Head.b v)) ∧ R.Anc x y ∧ R.Anc x z

/-- `I(R)`: the original vertices whose twin groups contain at least two members of `X(R)`. -/
def decoded (R : ProofDag (CVar D.TV)) : Finset (Fin D.n) :=
  Finset.univ.filter fun u =>
    2 ≤ (Finset.univ.filter fun c : Fin (D.n + 2 * D.k + 2) => (u, c) ∈ D.selected R).card

end ConstrData

/-! ## Comb-shaped proofs and their presentations -/

/-- A goal-path event: the side premise is the source `side`, privately resolved in order with the
unit sources of `prep` (each with its fact variable); the goal path then resolves on `pivot`. -/
structure Event (ι V : Type) where
  /-- the side source -/
  side : ι
  /-- private unit deletions applied to the side source, in order -/
  prep : List (ι × V)
  /-- the goal-path pivot -/
  pivot : V

/-- Nodes of a comb proof: the sources, the `j`-th private resolution of event `i`, and the goal
resolution of event `i`. -/
inductive CombNode (ι : Type) where
  | src (s : ι) | pr (i j : ℕ) | gl (i : ℕ)
  deriving DecidableEq

section Comb

variable {ι V : Type} [DecidableEq ι] [DecidableEq V]

/-- Number of private deletions of event `i`. -/
def prepLen (es : List (Event ι V)) (i : ℕ) : ℕ := ((es[i]?).map fun e => e.prep.length).getD 0

/-- The nodes of the comb proof of the start source `start` and the events `es` over the sources
`S`. -/
def combNodes (S : Finset ι) (es : List (Event ι V)) : Finset (CombNode ι) :=
  S.image CombNode.src ∪
    (Finset.range es.length).biUnion (fun i => (Finset.range (prepLen es i)).image (CombNode.pr i)) ∪
    (Finset.range es.length).image CombNode.gl

/-- The parents of a comb node: the private chain of event `i` starts at its side source and
resolves successively with its units; the goal path starts at `start` and resolves at event `i`
with the top of the private chain of `i`. -/
def combParents (start : ι) (es : List (Event ι V)) : CombNode ι → Finset (CombNode ι)
  | .src _ => ∅
  | .pr i j =>
    match es[i]? with
    | none => ∅
    | some e =>
      {if j = 0 then CombNode.src e.side else CombNode.pr i (j - 1)} ∪
        (((e.prep[j]?).map fun u => ({CombNode.src u.1} : Finset (CombNode ι))).getD ∅)
  | .gl i =>
    match es[i]? with
    | none => ∅
    | some e =>
      {if i = 0 then CombNode.src start else CombNode.gl (i - 1),
       if e.prep.length = 0 then CombNode.src e.side else CombNode.pr i (e.prep.length - 1)}

/-- The side clause of an event after its first `j` private deletions. -/
def sideLabel (inv : ι → Clause V) (e : Event ι V) (j : ℕ) : Clause V :=
  (e.prep.take j).foldl (fun c u => c.erase (u.2, false)) (inv e.side)

/-- The goal-path clause after the events `es`: each event resolves the current goal clause with
its prepared side clause on its pivot. -/
def goalLabel (inv : ι → Clause V) (start : ι) (es : List (Event ι V)) : Clause V :=
  es.foldl (fun g e => (sideLabel inv e e.prep.length).erase (e.pivot, true) ∪ g.erase (e.pivot, false))
    (inv start)

/-- The clause of each comb node. -/
def combLabel (inv : ι → Clause V) (start : ι) (es : List (Event ι V)) : CombNode ι → Clause V
  | .src s => inv s
  | .pr i j => ((es[i]?).map fun e => sideLabel inv e (j + 1)).getD ∅
  | .gl i => goalLabel inv start (es.take (i + 1))

/-- The sink of a comb proof: the last goal-path node. -/
def combSink (start : ι) (es : List (Event ι V)) : CombNode ι :=
  if es.length = 0 then CombNode.src start else CombNode.gl (es.length - 1)

/-- `(R, pos)` presents the comb proof of `start` and `es` with sources `S` and clauses `inv`: a
bijection from the comb nodes onto the nodes of `R` carries parents to edges, comb clauses to
labels, the comb sink to the sink, and each source `s ∈ S` to the indexed node `pos s`. -/
def IsCombPresentation (inv : ι → Clause V) (S : Finset ι) (start : ι) (es : List (Event ι V))
    (R : ProofDag V) (pos : ι → Fin R.n) : Prop :=
  ∃ e : CombNode ι → Fin R.n,
    Set.BijOn e (combNodes S es : Set (CombNode ι)) Set.univ ∧
    (∀ x ∈ combNodes S es, ∀ y ∈ combNodes S es,
      ((e x, e y) ∈ R.edges ↔ x ∈ combParents start es y)) ∧
    (∀ x ∈ combNodes S es, R.label (e x) = combLabel inv start es x) ∧
    R.sink = e (combSink start es) ∧
    ∀ s ∈ S, pos s = e (CombNode.src s)

end Comb

/-! ## Canonical proofs (Lemma 3.58, used in Lemma 3.62) -/

namespace ConstrData

variable (D : ConstrData)

/-- The orders fixed once for the construction: of the internal non-root heads of each tree
(consistent with the dependencies) and of the final deletions of all `z_h` and `p_j`. -/
structure CanonOrders where
  /-- order of the first-tree internal heads -/
  ord1 : List (Head D.TV)
  /-- order of the second-tree internal heads -/
  ord2 : List (Head D.TV)
  /-- order of the final compensator and ballast deletions -/
  final : List (Src D.TV)

/-- Validity of the fixed orders: each lists its set exactly once, and no head is listed before
a head it is a child of. -/
def CanonOrders.Valid (O : D.CanonOrders) : Prop :=
  O.ord1.Nodup ∧ O.ord1.toFinset = D.inner1 ∧ O.ord1.Pairwise (fun x y => x ∉ D.deps y) ∧
  O.ord2.Nodup ∧ O.ord2.toFinset = D.inner2 ∧ O.ord2.Pairwise (fun x y => x ∉ D.deps y) ∧
  O.final.Nodup ∧ O.final.toFinset = D.heads.image Src.z ∪ D.ballast.image Src.p

/-- The orders chosen for one independent set `X`: of the private deletions at `T` (members of
`X`), of the unselected pairs `a_v, d_v` (non-members), of the selected packets `a_v, b_v, d_v`
(members), and of the prepared `b_v` (non-members). -/
structure SetOrders where
  /-- private deletions at `T` -/
  privT : List D.TV
  /-- unselected pairs -/
  unsel : List D.TV
  /-- selected packets -/
  sel : List D.TV
  /-- prepared unselected `b` heads -/
  prepB : List D.TV

/-- The set orders list `X` (resp. its complement) exactly once each. -/
def SetOrders.ValidFor (L : D.SetOrders) (X : Finset D.TV) : Prop :=
  L.privT.Nodup ∧ L.privT.toFinset = X ∧ L.sel.Nodup ∧ L.sel.toFinset = X ∧
  L.unsel.Nodup ∧ L.unsel.toFinset = Xᶜ ∧ L.prepB.Nodup ∧ L.prepB.toFinset = Xᶜ

/-- The pivot variable of a final deletion. -/
def finalVar : Src D.TV → CVar D.TV
  | .z h => CVar.z h
  | .p j => CVar.p j
  | _ => CVar.A

/-- The goal-path events of the canonical proof `R_X` (p. 75–76): expand `T` prepared by deleting
`f_v` (unit `P_v`) for `v ∈ X`; the first-tree internal heads; for each `v ∉ X` the raw `a_v`
followed by deletion of `f_v` (unit `Q_v`); `U` and the second-tree internal heads; for each
`v ∈ X` the packet `a_v`, `b_v`, `d_v` (deletion of `f_v` with `Q_v`); for each `v ∉ X` the `b_v`
prepared with `P_v`; `A`; and the deletions of all `z_h`, `p_j`. The goal path starts at `G`. -/
def canonEvents (O : D.CanonOrders) (L : D.SetOrders) : List (Event (Src D.TV) (CVar D.TV)) :=
  [⟨Src.C Head.T, L.privT.map (fun v => (Src.P v, CVar.f v)), CVar.hd Head.T⟩] ++
  O.ord1.map (fun h => ⟨Src.C h, [], CVar.hd h⟩) ++
  L.unsel.flatMap (fun v =>
    [⟨Src.C (Head.a v), [], CVar.hd (Head.a v)⟩, ⟨Src.Q v, [], CVar.f v⟩]) ++
  [⟨Src.C Head.U, [], CVar.hd Head.U⟩] ++
  O.ord2.map (fun h => ⟨Src.C h, [], CVar.hd h⟩) ++
  L.sel.flatMap (fun v =>
    [⟨Src.C (Head.a v), [], CVar.hd (Head.a v)⟩, ⟨Src.C (Head.b v), [], CVar.hd (Head.b v)⟩,
     ⟨Src.Q v, [], CVar.f v⟩]) ++
  L.prepB.map (fun v => ⟨Src.C (Head.b v), [(Src.P v, CVar.f v)], CVar.hd (Head.b v)⟩) ++
  [⟨Src.CA, [], CVar.A⟩] ++
  O.final.map (fun s => ⟨s, [], D.finalVar s⟩)

/-- `(R, pos)` is a canonical proof of `X` for the fixed orders `O` and the set orders `L`, with
its source occurrences indexed by `pos`. -/
def IsCanonical (O : D.CanonOrders) (X : Finset D.TV) (L : D.SetOrders)
    (R : ProofDag (CVar D.TV)) (pos : Src D.TV → Fin R.n) : Prop :=
  SetOrders.ValidFor D L X ∧ IsCombPresentation D.inv D.srcs Src.G (D.canonEvents O L) R pos

end ConstrData

end ReconfRes.Frozen


