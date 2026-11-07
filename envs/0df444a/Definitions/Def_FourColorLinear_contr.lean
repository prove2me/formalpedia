-- Prove2me | Definitions.Def_FourColorLinear_contr
-- name    : FourColorLinear_contr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:53.469426+00:00
-- url     : https://prove2.me/theorems/1e8deaf0-3430-4cb1-9068-25d9648a30e1
-- title:
--   The contraction $B^{\mathcal K}_H$ of Kempe edges in the faces of $B$
-- statement:
--   Let $B$ and $H$ be subgraphs of a plane graph $P$, and $K$ its Kempe edges. In each face $\Phi$ of $B$, delete the parts of $H$ not Kempe connected to $B$; make a copy $v_\Phi$, joined to $v$ by an **attachment edge**, at each appearance of a vertex $v$ of $B$ on $\Phi$ with incident edges of $H$; move the Kempe edges to the copies; and contract each component strictly inside $\Phi$ to a **Kempe node**.
--
--   The result is determined by two facts over $B$: which appearances get an attachment edge, and which attachment edges meet at one Kempe node. This definition computes them from connectivity through contracted edges. It also fixes the following.
--
--   1. The Kempe connectivity and the graph of the result. A vertex that appears twice on a face gets parallel attachment edges, so the plane structure is on darts.
--   2. What it means for the result to be a plane graph containing $B$: a rotation system that agrees with $P$ on $B$, has each attachment edge at its appearance, and has Euler genus $0$.
--   3. The contraction of a union of earlier contractions, and the union itself, with which (2)–(4) of the paper are stated.
--
--   **Formalization Note** When a component contains a cycle, the rotation around its Kempe node is not determined by the construction, so only its existence is asserted.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §2.2, pp.15, 17

import Mathlib
import Definitions.Def_FourColorLinear_FaceOf

open PlanarQueue.Genus

namespace FourColorLinear

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The dart of a Kempe edge from `H` strictly inside a face of the subgraph with edge set `Be`. -/
def ContractedDart (K Be H : Set (Sym2 V)) (d : G.Dart) : Prop :=
  d.edge ∈ H ∧ d.edge ∈ K ∧ d.edge ∉ Be

open Classical in
/-- Where a contracted dart starts: at the appearance of its tail if the tail is on `B` (the copy
`v_Φ` of arXiv:2610.39753, held version, sha256 4dce39c5…, p.15), at the tail otherwise. -/
noncomputable def endOf (S : EmbeddingScheme G) (Bv : Set V) (Be : Set (Sym2 V)) (d : G.Dart) :
    Appearance S Be ⊕ V :=
  if d.fst ∈ Bv then .inl (appOf S Be d) else .inr d.fst

/-- A contracted edge joins the two places where its darts start. -/
def LinkRel (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Bv : Set V) (Be H : Set (Sym2 V))
    (y y' : Appearance S Be ⊕ V) : Prop :=
  ∃ d : G.Dart, ContractedDart K Be H d ∧ y = endOf S Bv Be d ∧ y' = endOf S Bv Be d.symm

/-- What a contraction adds to `B`: which appearances get an attachment edge, and which attachment
edges end at the same Kempe node. Two contractions with equal `CRes` are the same graph on `V(B)` and
Kempe nodes, with attachment edges at the same places in the rotation at each vertex of `B`. -/
@[ext] structure CRes (S : EmbeddingScheme G) (Be : Set (Sym2 V)) where
  /-- the appearances with an attachment edge -/
  attached : Set (Appearance S Be)
  /-- two attached appearances are joined to one Kempe node -/
  same : Appearance S Be → Appearance S Be → Prop

/-- The contraction `B^K_H` in the faces of `B`, arXiv:2610.39753, p.15: "First we delete all parts of
H in Φ that are not Kempe connected to B. Next, for each appearance of a vertex v on the boundary of
Φ, having some incident edges in H, we make a copy v_Φ inside Φ, attached to v by a new Kempe edge
vv_Φ, called an 'attachment edge'. … Moreover, we move each Kempe edge vw ∈ Φ so it becomes a Kempe
edge v_Φw. … Finally, we contract all Kempe edges strictly inside Φ, calling the result Kempe nodes."

**Formalization Note** `K ⊆ E(G)` is the set of Kempe edges, a parameter ("we allow ourselves to add
auxiliary Kempe edges", p.14). `B` is `(Bv, Be)`. A component not reaching an appearance has no
attachment: that is the deletion. The rotation at a Kempe node is not canonical when the component
has a cycle, so it is not part of `CRes`; `IsPlaneContraction` asserts that a planar one exists. -/
def contr (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Bv : Set V) (Be H : Set (Sym2 V)) :
    CRes S Be where
  attached := {a | ∃ d : G.Dart, ContractedDart K Be H d ∧ d.fst ∈ Bv ∧ appOf S Be d = a}
  same a a' :=
    (∃ d : G.Dart, ContractedDart K Be H d ∧ d.fst ∈ Bv ∧ appOf S Be d = a) ∧
    (∃ d : G.Dart, ContractedDart K Be H d ∧ d.fst ∈ Bv ∧ appOf S Be d = a') ∧
    Relation.EqvGen (LinkRel S K Bv Be H) (.inl a) (.inl a')

/-- The Kempe nodes of a contraction. -/
def CRes.Node {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) : Type :=
  Quot fun a b : r.attached => r.same a b

/-- The Kempe node of an attached appearance. -/
def CRes.nodeOf {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) (a : r.attached) :
    r.Node := Quot.mk _ a

/-- The Kempe edges of the result of a contraction: edges of `B` in `K`, and attachment edges. -/
def CRes.kempeGraph {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (K : Set (Sym2 V)) (r : CRes S Be) :
    SimpleGraph (V ⊕ r.Node) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .inl u, .inl v => s(u, v) ∈ Be ∧ s(u, v) ∈ K
    | .inl v, .inr N => ∃ a : r.attached, a.1.vertex = v ∧ r.nodeOf a = N
    | _, _ => False

/-- All edges of the result of a contraction: edges of `B`, and attachment edges. -/
def CRes.graph {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) :
    SimpleGraph (V ⊕ r.Node) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .inl u, .inl v => s(u, v) ∈ Be
    | .inl v, .inr N => ∃ a : r.attached, a.1.vertex = v ∧ r.nodeOf a = N
    | _, _ => False

/-- The darts of the result of a contraction: those of `B`, and for each attachment edge one dart out
of the vertex (`false`) and one out of the Kempe node (`true`). Parallel attachment edges occur when
a vertex appears twice on a face. -/
abbrev CRes.Dart {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) : Type :=
  {d : G.Dart // d.edge ∈ Be} ⊕ (r.attached × Bool)

/-- The tail of a dart of the result. -/
def CRes.tail {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) :
    r.Dart → V ⊕ r.Node
  | .inl d => .inl d.1.fst
  | .inr (a, false) => .inl a.1.vertex
  | .inr (a, true) => .inr (r.nodeOf a)

/-- The reversed dart of the result. -/
def CRes.rev {S : EmbeddingScheme G} {Be : Set (Sym2 V)} (r : CRes S Be) : r.Dart → r.Dart
  | .inl d => .inl ⟨d.1.symm, by simpa using d.2⟩
  | .inr (a, b) => .inr (a, !b)

/-- `B^K_H` is a plane graph containing `B` (arXiv:2610.39753, p.15, Lemma 10): a rotation system on
its darts which, at each vertex of `B`, is the rotation of `G` on `B`-edges with each attachment
edge at its own appearance, and whose Euler genus `2c − |V| + |E| − |F|` is 0. As in
`EmbeddingScheme.eulerGenus`, an isolated vertex counts as one face. -/
def IsPlaneContraction (S : EmbeddingScheme G) (Bv : Set V) {Be : Set (Sym2 V)} (r : CRes S Be) :
    Prop :=
  ∃ ρ : Equiv.Perm r.Dart,
    (∀ x, r.tail (ρ x) = r.tail x) ∧
    (∀ x y, r.tail x = r.tail y → ∃ k : ℕ, (ρ ^ k) x = y) ∧
    -- the rotation at the vertices of `B`
    (∀ (d' : {d : G.Dart // d.edge ∈ Be}) (ha : appOf S Be (S.rot.symm d'.1) ∈ r.attached),
      ρ (.inr (⟨_, ha⟩, false)) = .inl d') ∧
    (∀ (d : {d : G.Dart // d.edge ∈ Be}),
      (∀ ha : appOf S Be d.1 ∈ r.attached, ρ (.inl d) = .inr (⟨_, ha⟩, false)) ∧
      (appOf S Be d.1 ∉ r.attached → ∃ d' : {d : G.Dart // d.edge ∈ Be},
        appOf S Be (S.rot.symm d'.1) = appOf S Be d.1 ∧ ρ (.inl d) = .inl d')) ∧
    -- Euler's formula
    (2 * (Nat.card (r.graph.induce {x | ∀ v, x = .inl v → v ∈ Bv}).ConnectedComponent : ℤ)
        - (Bv.ncard + Nat.card r.Node : ℕ) + (Be.ncard + r.attached.ncard : ℕ)
        - (Nat.card (Quot fun x y : r.Dart => y = ρ (r.rev x)) +
            {x : V ⊕ r.Node | (∀ v, x = .inl v → v ∈ Bv) ∧ ∀ y, r.tail y ≠ x}.ncard : ℕ) = 0)

/-- The places of a contraction `B^K_{H}` in which `H` is itself a union of earlier contractions
`B_i^K_{H_i}` (arXiv:2610.39753, pp.15, 17): appearances on `B`, vertices off `B`, Kempe nodes of the
pieces, the latter represented by the attached appearances on `B_i`. -/
abbrev Place2 {ι : Type} (S : EmbeddingScheme G) (Be : Set (Sym2 V)) (Bei : ι → Set (Sym2 V)) :
    Type :=
  Appearance S Be ⊕ V ⊕ (Σ i, Appearance S (Bei i))

/-- A place of `B` or off `B`, as a place of `Place2`. -/
def toPlace2 {ι : Type} {S : EmbeddingScheme G} {Be : Set (Sym2 V)} {Bei : ι → Set (Sym2 V)} :
    Appearance S Be ⊕ V → Place2 S Be Bei
  | .inl a => .inl a
  | .inr v => .inr (.inl v)

/-- The Kempe edges of `⋃ B_i^K_{H_i}` strictly inside faces of `B`, with the rule that Kempe
nodes of a piece are single places: edges of `B_i` in `K` off `B`; attachment edges of the pieces,
at the place of the dart that gave rise to them; the identification of attached appearances. -/
inductive Link2 {ι : Type} (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Bv : Set V)
    (Be : Set (Sym2 V)) (Bvi : ι → Set V) (Bei Hi : ι → Set (Sym2 V)) :
    Place2 S Be Bei → Place2 S Be Bei → Prop
  | edge (i : ι) (d : G.Dart) (h₁ : d.edge ∈ Bei i) (h₂ : d.edge ∈ K) (h₃ : d.edge ∉ Be) :
      Link2 S K Bv Be Bvi Bei Hi (toPlace2 (endOf S Bv Be d)) (toPlace2 (endOf S Bv Be d.symm))
  | attach (i : ι) (d : G.Dart) (h₁ : ContractedDart K (Bei i) (Hi i) d) (h₂ : d.fst ∈ Bvi i) :
      Link2 S K Bv Be Bvi Bei Hi (toPlace2 (endOf S Bv Be d))
        (.inr (.inr ⟨i, appOf S (Bei i) d⟩))
  | node (i : ι) (a a' : Appearance S (Bei i)) (h : (contr S K (Bvi i) (Bei i) (Hi i)).same a a') :
      Link2 S K Bv Be Bvi Bei Hi (.inr (.inr ⟨i, a⟩)) (.inr (.inr ⟨i, a'⟩))

/-- An appearance on `B` carrying a Kempe edge of `⋃ B_i^K_{H_i}`. -/
def Attached2 {ι : Type} (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Bv : Set V)
    (Be : Set (Sym2 V)) (Bvi : ι → Set V) (Bei Hi : ι → Set (Sym2 V)) (a : Appearance S Be) : Prop :=
  ∃ (i : ι) (d : G.Dart), d.fst ∈ Bv ∧ appOf S Be d = a ∧
    ((d.edge ∈ Bei i ∧ d.edge ∈ K ∧ d.edge ∉ Be) ∨
      (ContractedDart K (Bei i) (Hi i) d ∧ d.fst ∈ Bvi i))

/-- The contraction `B^K_{⋃ B_i^K_{H_i}}` of a union of contractions, in the faces of `B`
(arXiv:2610.39753, (2) p.15 and (3) p.17). -/
def contr2 {ι : Type} (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Bv : Set V) (Be : Set (Sym2 V))
    (Bvi : ι → Set V) (Bei Hi : ι → Set (Sym2 V)) : CRes S Be where
  attached := {a | Attached2 S K Bv Be Bvi Bei Hi a}
  same a a' := Attached2 S K Bv Be Bvi Bei Hi a ∧ Attached2 S K Bv Be Bvi Bei Hi a' ∧
    Relation.EqvGen (Link2 S K Bv Be Bvi Bei Hi) (.inl a) (.inl a')

/-- The union `⋃ B_i^K_{H_i}` of contractions placed on `B ⊇ ⋃ B_i`, as in (2) and (4) of
arXiv:2610.39753, pp.15, 17: an attachment edge of a piece keeps its place, and two attachment edges
are at one Kempe node exactly when they are in some piece. -/
def cUnion {ι : Type} (S : EmbeddingScheme G) (K : Set (Sym2 V)) (Be : Set (Sym2 V))
    (Bvi : ι → Set V) (Bei Hi : ι → Set (Sym2 V)) : CRes S Be where
  attached := {a | ∃ (i : ι) (d : G.Dart), ContractedDart K (Bei i) (Hi i) d ∧ d.fst ∈ Bvi i ∧
    appOf S Be d = a}
  same a a' := ∃ (i : ι) (d d' : G.Dart),
    ContractedDart K (Bei i) (Hi i) d ∧ d.fst ∈ Bvi i ∧ appOf S Be d = a ∧
    ContractedDart K (Bei i) (Hi i) d' ∧ d'.fst ∈ Bvi i ∧ appOf S Be d' = a' ∧
    (contr S K (Bvi i) (Bei i) (Hi i)).same (appOf S (Bei i) d) (appOf S (Bei i) d')

end FourColorLinear


