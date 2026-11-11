-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_SPQRTree
-- name    : SnarlSPQR_Snarls_SPQRTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:27:42.283088+00:00
-- url     : https://prove2.me/theorems/5284f542-6742-46e9-8e17-c138823350b2
-- title:
--   SPQR trees of biconnected multigraphs (the paper's recursive definition), skeletons, virtual edges, Q-node omission and expansions
-- statement:
--   Let $H$ be a biconnected multigraph with at least two edges, and let $e=\{s,t\}\in E(H)$ be a **reference edge**. The **SPQR tree** of $H$ with respect to $e$ is defined by recursion on graphs consisting of a set $F$ of real edges of $H$ together with one reference edge $\{s,t\}$. The recursion has four cases.
--
--   - **Trivial case.** The graph is exactly two parallel edges between $s$ and $t$. The tree is a single Q-node.
--   - **Parallel case.** The split pair $\{s,t\}$ has $k+1\ge 3$ split components $H_0,\dots,H_k$, where $H_0$ is the reference edge. The root is a P-node whose skeleton consists of $k+1$ parallel edges $e_0=e,e_1,\dots,e_k$.
--   - **Series case.** Otherwise $\{s,t\}$ has exactly two split components, the reference edge and $H'$. If $H'$ is a sequence of blocks $H_1,\dots,H_k$ ($k\ge2$) separated by cutvertices $c_1,\dots,c_{k-1}$ in this order from $c_0=s$ to $c_k=t$, the root is an S-node whose skeleton is the cycle $e_0=e$, $e_i=\{c_{i-1},c_i\}$.
--   - **Rigid case.** None of the above applies. Let $\{s_1,t_1\},\dots,\{s_k,t_k\}$ ($k\ge1$) be the maximal split pairs with respect to $\{s,t\}$, and let $H_i$ be the union of the split components of $\{s_i,t_i\}$ other than the one containing $e$. The root is an R-node whose skeleton is the graph with each $H_i$ replaced by the edge $e_i=\{s_i,t_i\}$. A split pair $\{u,v\}$ is **maximal** with respect to $\{s,t\}$ if, for every other split pair $\{u',v'\}$, the vertices $u,v,s,t$ lie in one split component of $\{u',v'\}$.
--
--   Except in the trivial case, the root has a child $\mu_i$ for each $i$, and $\mu_i$ is the SPQR tree of $H_i\cup e_i$ with respect to $e_i$. The edge $e_i$ of the parent's skeleton is the **virtual edge** pertaining to $\mu_i$. Finally a Q-node for $e$ becomes a child of the root.
--
--   **Omitting Q-nodes** turns every virtual edge pertaining to a Q-node into a real edge and removes the Q-nodes. For a tree edge $\{\nu,\mu\}$, the **expansion** of the virtual edge pertaining to $\mu$ is the subgraph induced by the real edges in the skeletons on $\mu$'s side of the tree. The expansion of a real edge is that edge alone.
--
--   **Formalization Note.** A tree is `Tree V E`: either `q f s t` (a Q-node) or `node k s t cs` (an S-, P- or R-node with reference edge $\{s,t\}$ and children `cs`). Slot $0$ of a node's skeleton is its reference edge, and slot $i+1$ is the virtual edge of child $i$; for an S-node the slots are in cycle order. `IsDecomp ends F s t T` is the inductive predicate implementing the four cases on the graph `pgraph ends F s t`, whose reference edge is the virtual edge `none`. `IsSPQRTree H e T` applies it to $H-e$ with a reference edge having the endpoints of $e$. The root's slot $0$ stands for the Q-node of $e$, so in the Q-less tree it is the real edge $e$. The nodes of the Q-less tree are the non-Q subtrees. `sideEdges` and `slotExp` give the edge sets of the expansions.
--
--   Readings:
--   - the maximal split pairs of the rigid case are taken distinct from $\{s,t\}$, because $\{s,t\}$ itself meets the printed maximality condition and the recursion would otherwise repeat;
--   - every edge of the rigid skeleton other than $e$ is one of the $e_i$, since every real edge lies in some $H_i$.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), pp. 6–8, §2.4 (split pairs, split components, maximal split pairs, the recursive definition, Q-node omission, expansions)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_Multigraph

open Classical

namespace SnarlSPQR.Snarls

/-!
# SPQR trees (§2.4, pp. 6–8)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), §2.4, pp. 6–8.

**The paper's recursive definition.** Let `H` be a biconnected multigraph with at least two edges
and `e = {s, t}` a reference edge. The SPQR tree of `H` with respect to `e` is built by recursion
on graphs of the form "a set `F` of real edges of `H` plus one reference edge `{s, t}`":

* *Trivial case*: the graph is exactly two parallel edges between `s` and `t` (one real edge `f`
  plus the reference edge): a single Q-node.
* *Parallel case*: the split pair `{s, t}` has `k + 1 ≥ 3` split components `H₀, …, H_k`, `H₀`
  the reference edge: a P-node whose skeleton is `k + 1` parallel edges `e₀ = e, e₁, …, e_k`,
  with a child for each `H_i ∪ e_i` (reference edge `e_i = {s, t}`).
* *Series case*: otherwise `{s, t}` has exactly two split components, the reference edge and
  `H'`, and `H'` is a sequence of blocks `H₁, …, H_k` (`k ≥ 2`) separated by cutvertices
  `c₁, …, c_{k−1}` in this order from `c₀ = s` to `c_k = t`: an S-node whose skeleton is the cycle
  `e₀ = e, e_i = {c_{i−1}, c_i}`, with a child for each `H_i ∪ e_i`.
* *Rigid case*: none of the above. Let `{s₁, t₁}, …, {s_k, t_k}` (`k ≥ 1`) be the maximal split
  pairs with respect to `{s, t}` and `H_i` the union of the split components of `{s_i, t_i}`
  other than the one containing `e`: an R-node whose skeleton is the graph with every `H_i`
  replaced by `e_i = {s_i, t_i}`, with a child for each `H_i ∪ e_i`.

Finally a Q-node for the first reference edge `e` is made a child of the root.

**Encoding.** A tree is `Tree V E`: a Q-node `q f s t` (real edge `f`, endpoints `s, t`) or a node
`node k s t cs` of kind `k ∈ {S, P, R}` whose reference edge has endpoints `{s, t}` and whose
children (in order) are `cs`. The skeleton of `node k s t cs` has one edge per *slot*: slot `0` is
its reference edge `{s, t}` (pertaining to the parent) and slot `i + 1` is the virtual edge
`{s_i, t_i}` pertaining to the child `cs[i]` (whose reference edge has the same endpoints). Its
vertices are the endpoints of its slots. For an S-node the slot order `0, 1, …, k` is the cycle
order of the skeleton.

`IsDecomp ends F s t T` says that `T` is the SPQR tree (with Q-nodes) of the graph
`pgraph ends F s t` formed by the real edges `F` and a virtual reference edge `{s, t}`, built by
the four cases above. `IsSPQRTree H e T` says that `T` is the SPQR tree of `H` with respect to
the reference edge `e ∈ E(H)`: `T` is the decomposition of `H − e` plus a reference edge with the
endpoints of `e`; the extra Q-node of `e` is not stored, and the root's slot `0` stands for it.

**Q-nodes omitted** (p. 8): every virtual edge pertaining to a Q-node becomes a real edge and
Q-nodes are removed. So the nodes of the Q-less tree are the `node`s of `T`; in the skeleton of
`μ`, slot `i + 1` is real iff `cs[i]` is a Q-node, and slot `0` is real iff `μ` is the root (it is
then the real edge `e`).

**Expansions** (p. 8): for a tree edge `{ν, μ}`, the expansion of the virtual edge pertaining to
`μ` is the subgraph induced by the real edges in the skeletons of the component of `T − {ν, μ}`
containing `μ`; the expansion of a real edge is the edge alone. `slotExp` returns its edge set.

Readings: in the rigid case the maximal split pairs are taken distinct from `{s, t}` (the pair
`{s, t}` itself satisfies the printed maximality condition, and taking it would make the
recursion repeat the same graph); a split component is the paper's (see `IsSplitComponent`).
-/

/-- The type of an inner SPQR-tree node. -/
inductive NodeKind where
  | S
  | P
  | R
  deriving DecidableEq

/-- An SPQR tree with Q-nodes: `q f s t` is a Q-node for the real edge `f` with endpoints `s, t`;
`node k s t cs` is an S-, P- or R-node with reference edge `{s, t}` and children `cs`. -/
inductive Tree (V E : Type*) where
  | q (f : E) (s t : V)
  | node (k : NodeKind) (s t : V) (cs : List (Tree V E))

namespace Tree

variable {V E : Type*}

/-- The endpoints of the reference edge of a tree node. -/
def refPair : Tree V E → Sym2 V
  | q _ s t => s(s, t)
  | node _ s t _ => s(s, t)

/-- Is this a Q-node? -/
def isQ : Tree V E → Bool
  | q _ _ _ => true
  | node _ _ _ _ => false

/-- The kind of a node (`none` for a Q-node). -/
def kind? : Tree V E → Option NodeKind
  | q _ _ _ => none
  | node k _ _ _ => some k

/-- The children of a node (none for a Q-node). -/
def children : Tree V E → List (Tree V E)
  | q _ _ _ => []
  | node _ _ _ cs => cs

mutual
/-- All subtrees (every node of the tree, Q-nodes included), in preorder, the tree first. -/
def subtrees : Tree V E → List (Tree V E)
  | q f s t => [q f s t]
  | node k s t cs => node k s t cs :: subtreesList cs
/-- The subtrees of a list of trees. -/
def subtreesList : List (Tree V E) → List (Tree V E)
  | [] => []
  | c :: cs => subtrees c ++ subtreesList cs
end

/-- The real edges of a subtree: the edges of its Q-nodes. -/
noncomputable def realEdges (T : Tree V E) : Finset E :=
  ((T.subtrees.filterMap fun x => match x with
    | q f _ _ => some f
    | node _ _ _ _ => none)).toFinset

/-- The nodes of the Q-less tree inside `T` (the non-Q subtrees, one entry per node). -/
def qlessNodes (T : Tree V E) : List (Tree V E) := T.subtrees.filter fun x => !x.isQ

/-- The slots (skeleton edges, by endpoints) of a node: slot `0` is the reference edge, slot
`i + 1` the virtual edge of child `i`. A Q-node's skeleton is its real edge plus its reference
edge, both with endpoints `{s, t}`. -/
def slots : Tree V E → List (Sym2 V)
  | q _ s t => [s(s, t), s(s, t)]
  | node _ s t cs => s(s, t) :: cs.map refPair

/-- The vertices of the skeleton of a node: the endpoints of its slots. -/
noncomputable def skelVerts (μ : Tree V E) : Finset V :=
  μ.slots.toFinset.biUnion fun p => p.toFinset

end Tree

namespace MGraph

variable {V E : Type*}

/-- The graph formed by the real edges `F` and a virtual reference edge `{s, t}` (edge `none`). -/
noncomputable def pgraph (ends : E → Sym2 V) (F : Finset E) (s t : V) : MGraph V (Option E) where
  verts := (F.biUnion fun f => (ends f).toFinset) ∪ {s, t}
  edges := insert none (F.map ⟨some, Option.some_injective E⟩)
  ends := fun o => o.elim s(s, t) ends

/-- The real edges of a subgraph of a `pgraph`. -/
noncomputable def realOf (C : MGraph V (Option E)) : Finset E :=
  C.edges.preimage some (Option.some_injective E).injOn

/-- The subgraph of `K` induced by the real edges `F'`. -/
noncomputable def realSub (K : MGraph V (Option E)) (F' : Finset E) : MGraph V (Option E) :=
  K.edgeSub (F'.map ⟨some, Option.some_injective E⟩)

/-- Parallel case: the split components of `{s, t}` other than the reference edge are exactly the
subgraphs induced by the real edge sets `Fs`, listed once each, and there are at least two of them
(so `k + 1 ≥ 3` in all). -/
def PShape (K : MGraph V (Option E)) (s t : V) (Fs : List (Finset E)) : Prop :=
  2 ≤ Fs.length ∧ Fs.Nodup ∧
    ∀ C, (K.IsSplitComponent s t C ∧ C ≠ K.edgeSub {none}) ↔ ∃ F' ∈ Fs, C = K.realSub F'

/-- Series case: `{s, t}` has exactly two split components, the reference edge and `H'`, and `H'`
is a sequence of blocks `H₁, …, H_k` (`k ≥ 2`) separated by its cutvertices `c₁, …, c_{k−1}` in
this order from `c₀ = s` to `c_k = t`. The list `bl` holds `(E(H_i), c_{i−1}, c_i)`. -/
def SShape (K : MGraph V (Option E)) (s t : V) (bl : List (Finset E × V × V)) : Prop :=
  ∃ H' : MGraph V (Option E), H' ≠ K.edgeSub {none} ∧
    (∀ C, K.IsSplitComponent s t C ↔ C = K.edgeSub {none} ∨ C = H') ∧
    2 ≤ bl.length ∧ (bl.map Prod.fst).Nodup ∧
    bl.head?.map (fun b => b.2.1) = some s ∧ bl.getLast?.map (fun b => b.2.2) = some t ∧
    (∀ i (h : i + 1 < bl.length), (bl[i]'(by omega)).2.2 = (bl[i + 1]'h).2.1) ∧
    (∀ b ∈ bl, b.2.1 ≠ b.2.2 ∧ b.2.1 ∈ (K.realSub b.1).verts ∧ b.2.2 ∈ (K.realSub b.1).verts) ∧
    (∀ B, H'.IsBlock B ↔ ∃ b ∈ bl, B = K.realSub b.1) ∧
    (∀ x, H'.IsCutvertex x ↔ ∃ i, ∃ (h : i + 1 < bl.length), x = (bl[i]'(by omega)).2.2)

/-- The maximal split pairs of `K` with respect to `{s, t}` (p. 6): `{u, v}` is a split pair such
that for every other split pair `{u', v'}` the vertices `u, v, s, t` lie in one split component of
`{u', v'}`. -/
def IsMaxSplitPair (K : MGraph V (Option E)) (s t u v : V) : Prop :=
  K.IsSplitPair u v ∧ ∀ u' v', K.IsSplitPair u' v' → s(u', v') ≠ s(u, v) →
    ∃ C, K.IsSplitComponent u' v' C ∧ u ∈ C.verts ∧ v ∈ C.verts ∧ s ∈ C.verts ∧ t ∈ C.verts

/-- The real edges of `H_i`: the union of the split components of `{u, v}` except the one
containing the reference edge. -/
noncomputable def rigidPart (K : MGraph V (Option E)) (F : Finset E) (u v : V) : Finset E :=
  F.filter fun f => ∃ C, K.IsSplitComponent u v C ∧ none ∉ C.edges ∧ some f ∈ C.edges

/-- Rigid case: the pairs `{s_i, t_i}` of `rl` are the maximal split pairs with respect to
`{s, t}` other than `{s, t}`, each once, `k ≥ 1`, and `E(H_i)` is `rigidPart`. -/
def RShape (K : MGraph V (Option E)) (F : Finset E) (s t : V) (rl : List (Finset E × V × V)) :
    Prop :=
  1 ≤ rl.length ∧ (rl.map fun r => s(r.2.1, r.2.2)).Nodup ∧
    (∀ u v, (K.IsMaxSplitPair s t u v ∧ s(u, v) ≠ s(s, t)) ↔
      ∃ r ∈ rl, s(r.2.1, r.2.2) = s(u, v)) ∧
    ∀ r ∈ rl, r.1 = K.rigidPart F r.2.1 r.2.2

end MGraph

open MGraph in
/-- `IsDecomp ends F s t T`: `T` is the SPQR tree (Q-nodes included) of the graph formed by the
real edges `F` (with endpoint map `ends`) and the virtual reference edge `{s, t}`, built by the
recursive definition of p. 6–7. -/
inductive IsDecomp {V E : Type*} (ends : E → Sym2 V) : Finset E → V → V → Tree V E → Prop
  | trivial (f : E) (s t : V) (h : ends f = s(s, t)) : IsDecomp ends {f} s t (.q f s t)
  | parallel (F : Finset E) (s t : V) (kids : List (Finset E × Tree V E))
      (hshape : PShape (pgraph ends F s t) s t (kids.map Prod.fst))
      (hkids : ∀ p ∈ kids, IsDecomp ends p.1 s t p.2) :
      IsDecomp ends F s t (.node .P s t (kids.map Prod.snd))
  | series (F : Finset E) (s t : V) (kids : List ((Finset E × V × V) × Tree V E))
      (hshape : SShape (pgraph ends F s t) s t (kids.map Prod.fst))
      (hkids : ∀ p ∈ kids, IsDecomp ends p.1.1 p.1.2.1 p.1.2.2 p.2) :
      IsDecomp ends F s t (.node .S s t (kids.map Prod.snd))
  | rigid (F : Finset E) (s t : V) (kids : List ((Finset E × V × V) × Tree V E))
      (hnotTrivial : ¬ ∃ f, F = {f} ∧ ends f = s(s, t))
      (hnotP : ¬ ∃ Fs, PShape (pgraph ends F s t) s t Fs)
      (hnotS : ¬ ∃ bl, SShape (pgraph ends F s t) s t bl)
      (hshape : RShape (pgraph ends F s t) F s t (kids.map Prod.fst))
      (hkids : ∀ p ∈ kids, IsDecomp ends p.1.1 p.1.2.1 p.1.2.2 p.2) :
      IsDecomp ends F s t (.node .R s t (kids.map Prod.snd))

namespace MGraph

variable {V E : Type*}

/-- `T` is the SPQR tree of `H` with respect to the reference edge `e ∈ E(H)` (pp. 6–7): the
recursive decomposition of `H − e` together with a reference edge with the endpoints of `e`. The
Q-node of `e` added at the end is implicit: it pertains to slot `0` of the root. -/
def IsSPQRTree (H : MGraph V E) (e : E) (T : Tree V E) : Prop :=
  e ∈ H.edges ∧ ∃ s t, H.ends e = s(s, t) ∧ IsDecomp H.ends (H.edges.erase e) s t T

end MGraph

namespace Tree

variable {V E : Type*}

/-- `μ` is a node of the Q-less tree `T` (a non-Q subtree). -/
def IsNode (T μ : Tree V E) : Prop := μ ∈ T.subtrees ∧ μ.isQ = false

/-- `μ` is a node of the Q-less tree `T` and a child of the node `ν` (both non-Q). -/
def IsChildOf (T μ ν : Tree V E) : Prop := T.IsNode ν ∧ T.IsNode μ ∧ μ ∈ ν.children

/-- `μ` and `ν` are adjacent nodes of the Q-less tree `T`. -/
def Adjacent (T μ ν : Tree V E) : Prop := T.IsChildOf μ ν ∨ T.IsChildOf ν μ

/-- For adjacent `μ, ν` of `T` (an SPQR tree of a graph with edge set `EH`), the real edges on
`μ`'s side of the tree edge `{μ, ν}`: the edge set of the expansion of the virtual edge of
`skeleton(ν)` pertaining to `μ`. -/
noncomputable def sideEdges (EH : Finset E) (T μ ν : Tree V E) : Finset E :=
  if T.IsChildOf μ ν then μ.realEdges else EH \ ν.realEdges

/-- The endpoints of the tree edge `{μ, ν}` (the endpoints of both of its virtual edges): the
reference pair of the child. -/
noncomputable def treeEdgePair (T μ ν : Tree V E) : Sym2 V :=
  if T.IsChildOf μ ν then μ.refPair else ν.refPair

/-- Slot `i` of the skeleton of the node `μ` of the SPQR tree `T` is a real edge once Q-nodes are
omitted: slot `0` of the root (the reference edge `e`), or a slot whose child is a Q-node. Every
other slot is a virtual edge. -/
def slotReal (T μ : Tree V E) (i : ℕ) : Prop :=
  match i with
  | 0 => μ = T
  | j + 1 => ∃ c, μ.children[j]? = some c ∧ c.isQ = true

/-- The edge set of the expansion of slot `i` of the skeleton of the node `μ` of the Q-less tree
`T` (an SPQR tree of a graph with edge set `EH` and reference edge `e`): slot `0` of the root is
the real edge `e`; slot `0` of another node pertains to its parent (all real edges outside `μ`'s
subtree); slot `j + 1` is the real edge of a Q-child or pertains to the child `cs[j]` (the real
edges of its subtree). -/
noncomputable def slotExp (EH : Finset E) (e : E) (T μ : Tree V E) (i : ℕ) : Finset E :=
  match i with
  | 0 => if μ = T then {e} else EH \ μ.realEdges
  | j + 1 => match μ.children[j]? with
    | some c => c.realEdges
    | none => ∅

/-- The skeleton of the node `μ` has the two vertices `u ≠ v` nonadjacent: both are skeleton
vertices and no slot joins them. -/
def NonadjacentInSkel (μ : Tree V E) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ μ.skelVerts ∧ v ∈ μ.skelVerts ∧ s(u, v) ∉ μ.slots

end Tree

end SnarlSPQR.Snarls


