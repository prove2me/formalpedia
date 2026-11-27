-- Prove2me | Definitions.Def_NetBilinear_Supplement_VerticallyConnected
-- name    : NetBilinear_Supplement_VerticallyConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:43:07.025946+00:00
-- url     : https://prove2.me/theorems/9ac66ca0-0c7e-41eb-b35e-9ef59a6a4605
-- title:
--   Definition 2: a collection of subnetworks of the parallel networks is vertically connected through connection nodes $C_v$ and connection arcs $C_a$
-- statement:
--   Let $G=(V,A)$ be a network and $\bar G$ its undirected variant. For $j\in M$ the **parallel network** $G^j$ is a replica of $G$ (Definition 1); a node or arc of $G^j$ carries the name of its original in $G$, so a node $v\in V$ is adjacent (an arc $a\in A$ is incident) to a node of a subnetwork of $G^j$ when its replica in $G^j$ is.
--
--   Let $\dot G_1,\dots,\dot G_r$ be subnetworks of parallel networks, and let $C_v\subseteq V$ and $C_a\subseteq A$. The collection is **vertically connected through $C_v$ and $C_a$** if there is an ordering $s_1,\dots,s_r$ of $1,\dots,r$ such that for each $i=1,\dots,r-1$ one of the following holds:
--   1. some arc $a\in C_a$ is incident to a node of $\dot G_{s_{i+1}}$ and to a node of some $\dot G_{s_t}$, $t\le i$;
--   2. there are nodes $v_1,\dots,v_p\in C_v$, each adjacent in $G$ to the previous one, such that $v_1$ is adjacent to a node of $\dot G_{s_{i+1}}$ (or $v_1$ is itself a node of $\dot G_{s_{i+1}}$) and $v_p$ is adjacent to a node of some $\dot G_{s_t}$, $t\le i$.
--
--   Vertical connectivity of the trees of the forests $\bar F^j$ through the connection nodes and arcs is condition (ii) of Proposition 4 and a hypothesis of Theorem 3.
--
--   **Formalization Note** The collection is a finite family of node sets indexed by a type `ι`, and the ordering is a bijection with `Fin r`. Only node sets enter the definition, so the replica index of each subnetwork and its arcs are not arguments. Adjacency is adjacency in $\bar G$. As printed, the clause "if $v_1$ is in $\dot G_{s_{i+1}}$ it counts as adjacent" is applied to $v_1$ only.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Definition 1, pp.11–12 (parallel networks and the naming convention), Definition 2, p.12

import Mathlib
import Definitions.Def_NetBilinear_Network

namespace NetBilinear.Supplement

variable {V A : Type*}

/-- **A node `v` is adjacent to a node of a subnetwork with node set `S`**: `v` is adjacent in
`Ḡ` (joined by an arc of `G`, in either direction) to some node of `S`.
arXiv:2302.14151v2, §3.2, p.12, the convention after Definition 1: a node of `G` is adjacent to
a node of a subnetwork of the parallel network `G^j` when its replica in `G^j` is. -/
def AdjToSet (G : Network V A) (v : V) (S : Set V) : Prop :=
  ∃ w ∈ S, G.underlying.Adj v w

/-- **An arc `a` is incident to a node of a subnetwork with node set `S`**: its tail or its
head lies in `S`. arXiv:2302.14151v2, §3.2, p.12 (same convention). -/
def ArcIncToSet (G : Network V A) (a : A) (S : Set V) : Prop :=
  G.tail a ∈ S ∨ G.head a ∈ S

/-- **The link of Definition 2 from the subnetwork with node set `S` to the subnetwork with
node set `S'`** through the connection nodes `Cv` and connection arcs `Ca`
(arXiv:2302.14151v2, Definition 2, p.12): either
(i) an arc `a ∈ Ca` is incident to a node of `S` and to a node of `S'`, or
(ii) there are nodes `v₁, …, v_p ∈ Cv` (`p ≥ 1`), each adjacent to the previous one in `G`,
such that `v₁` is adjacent to a node of `S` — or `v₁` is itself in `S` ("if node v1 is in
Ġ^{s_{i+1}}, it counts as an adjacent node to the connection node v1") — and `v_p` is
adjacent to a node of `S'`.

**Formalization Note.** The walk `v₁, …, v_p` is a nonempty list of nodes of `Cv` that is a
chain for adjacency in `Ḡ`. As printed, the "in counts as adjacent" clause is stated for `v₁`
only, so it is applied to `v₁` only. -/
def VLink (G : Network V A) (Cv : Set V) (Ca : Set A) (S S' : Set V) : Prop :=
  (∃ a ∈ Ca, ArcIncToSet G a S ∧ ArcIncToSet G a S') ∨
    ∃ (v₁ : V) (rest : List V),
      (∀ v ∈ v₁ :: rest, v ∈ Cv) ∧ (v₁ :: rest).IsChain G.underlying.Adj ∧
      (AdjToSet G v₁ S ∨ v₁ ∈ S) ∧ AdjToSet G ((v₁ :: rest).getLast (List.cons_ne_nil _ _)) S'

/-- **Definition 2 (vertical connectivity).**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, Definition 2, p.12: "Consider a collection of networks Ġk = (V̇k, Ȧk), for
k = 1,...,r, where each Ġk is a subnetwork of a parallel networks Gj for some j ∈ M. We say that
this collection is vertically connected through the connection nodes Cv ⊆ V and connection arcs
Ca ⊆ A if there exists an ordering s1,s2,...,sr of indices 1,...,r such that for each
i = 1,...,r − 1, there exists either (i) an arc a ∈ Ca such that a is incident to a node of
Ġsi+1 and it is incident to a node of some subnetworks among Ġs1,...,Ġsi, or (ii) a set of
nodes v1,...,vp ∈ Cv, each adjacent to the previous one in the original network G, such that v1
is adjacent to a node of Ġsi+1 and vp is adjacent to a node of some subnetworks among
Ġs1,...,Ġsi. In this definition, if node v1 is in Ġsi+1, it counts as an adjacent node to the
connection node v1."

The collection is indexed by a finite type `ι`, the subnetwork `b` having node set `nodes b`.
The ordering is a bijection `e : ι ≃ Fin r`; every subnetwork other than the first one is
linked (`VLink`) to some subnetwork earlier in the ordering.

**Formalization Note.** Definition 2 refers only to the node sets of the subnetworks, to
adjacency and incidence in `G` (by the naming convention after Definition 1, p.12, the replica
of `v` in every `G^j` is again called `v`), and to `Cv`, `Ca`. So neither the replica index `j`
nor the arc sets `Ȧk` of the subnetworks enter, and they are not arguments. -/
def VerticallyConnected (G : Network V A) {ι : Type*} [Fintype ι] (nodes : ι → Set V)
    (Cv : Set V) (Ca : Set A) : Prop :=
  ∃ e : ι ≃ Fin (Fintype.card ι), ∀ b : ι, 0 < (e b).val →
    ∃ c : ι, e c < e b ∧ VLink G Cv Ca (nodes b) (nodes c)

end NetBilinear.Supplement


