-- Prove2me | Definitions.Def_SingleExpBisect_Main_Graphs
-- name    : SingleExpBisect_Main_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:39:21.474669+00:00
-- url     : https://prove2.me/theorems/0a5a0b1c-2218-416b-bd32-b1c9db604bee
-- title:
--   Connected S–T cuts, important cuts, adh_H, rooted tree decompositions with adhesion and edge-unbreakability
-- statement:
--   All graphs are finite, simple and undirected; a graph $H$ on $n$ vertices has vertex set $\{0,\dots,n-1\}$ (Lean `SimpleGraph (Fin n)`), and $|\delta_H(A)|$ is the number of edges with exactly one end in $A$ (published `MinBisectFPT.cutSize`).
--
--   - For disjoint $S,T\subseteq V(H)$, a **connected $S$–$T$ cut** is a set $C$ with $S\subseteq C\subseteq V(H)\setminus T$ and $H[C]$ connected. It is **important** if no connected $S$–$T$ cut $D\supsetneq C$ has $|\delta_H(D)|\le|\delta_H(C)|$.
--   - For $T\subseteq V(H)$, $\mathrm{adh}_H(T)$ is the maximum of $|N_H(C)|$ over the components $C$ of $H-T$, and $0$ if $H-T$ is empty ($N_H$ the open neighbourhood, published `nbr`; components via the published `IsComponent`).
--   - A **rooted tree decomposition** of $G$ is the published data `MinBisectFPT.RootedTD` (nodes, a parent array, a bag per node) such that exactly one node (the root) has no parent and the tree of the parent array with the bags satisfies the published tree-decomposition axioms (`RobertsonSeymour1986.GM5.IsTreeDecomposition`: covering, every edge in a bag, the bags containing a vertex form a subtree). Bags may be empty.
--   - Its **adhesion is at most $a$** if $|B_t\cap B_{t'}|\le a$ for every node $t$ with parent $t'$.
--   - It is **$(q,k)$-edge-unbreakable** if every bag $B_t$ is $(q,k)$-edge-unbreakable in $G$: $\min\{|A\cap B_t|,|B_t\setminus A|\}\le q$ for every $A\subseteq V(G)$ with $|\delta_G(A)|\le k$ (published `IsEdgeUnbreakable` with $V(H)$ the whole vertex set).
--   - `IsSec3Decomp G T k`: the decompositions of Section 3, i.e. rooted, adhesion at most $2k$, $(2k,k)$-edge-unbreakable in $G$, at most $\max(n,1)$ nodes, and every bag nonempty when $n>0$ (the construction of Theorem 1.1, pp. 23, 35; at $n=0$ use one empty bag). There is no connectivity requirement on $G$.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §2, pp. 13–14 (connected and important cuts, tree decompositions, adhesion); §1.1, p. 4 (edge-unbreakability); §5, p. 31 (adh_H); §3.1, p. 15 and p. 35 (the decomposition of Section 3)

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_MinBisectFPT_RootedTD
import Definitions.Def_MinBisectFPT_IsUnbreakableTD

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- **Connected S–T cut.** Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and
Matching Cut via a New Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §2, p. 13:
"Let S, T ⊆ V(H) be disjoint. A connected S–T cut is a cut C of H such that S ⊆ C ⊆ V(H) \ T and
H[C] is connected."

**Formalization Note.** The graph `H` lives on `Fin n` and `V(H)` is all of `Fin n`. Mathlib's
`Connected` includes nonemptiness; every use has `S` nonempty, so `C ⊇ S` is nonempty anyway. -/
def IsConnCut {n : ℕ} (H : SimpleGraph (Fin n)) (S T C : Finset (Fin n)) : Prop :=
  S ⊆ C ∧ Disjoint C T ∧ (H.induce (C : Set (Fin n))).Connected

/-- **Important connected S–T cut.** ibid., §2, p. 13: "It is important if there is no connected
S–T cut D ⊋ C with |δ_H(D)| ≤ |δ_H(C)|." `cutSize` is the published `|δ_H(·)|`. -/
def IsImportantConnCut {n : ℕ} (H : SimpleGraph (Fin n)) (S T C : Finset (Fin n)) : Prop :=
  IsConnCut H S T C ∧
    ∀ D : Finset (Fin n), C ⊂ D → IsConnCut H S T D → cutSize H C < cutSize H D

/-- **`adh_H(T)`.** ibid., §5, p. 31: "For T ⊆ V(H), let adh_H(T) be the maximum of |N_H(C)| over
the components C of H − T, or zero if H − T is empty." A component of `H − T` is a component of
`H[V(H) \ T]` (published `IsComponent`), and `N_H` is the published open neighbourhood `nbr`. -/
noncomputable def adh {n : ℕ} (H : SimpleGraph (Fin n)) (T : Finset (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun C => IsComponent H (Finset.univ \ T) C)).sup (fun C => (nbr H C).card)

/-- **Rooted tree decomposition.** ibid., §2, pp. 13–14: a tree `T` with bags `B_t ⊆ V(H)`
covering `V(H)`, every edge inside a bag, and for every vertex the nodes whose bag contains it
inducing a connected subtree; "a rooted tree decomposition additionally has a designated root."

**Formalization Note.** The data is the published `MinBisectFPT.RootedTD` (node count, parent array
with `none` at the root, bags). The tree is the graph of the parent array, and the three axioms are
the published `RobertsonSeymour1986.GM5.IsTreeDecomposition` (its path axiom (iii) is equivalent
to the connected-subtree axiom). Exactly one node has no parent: the designated root. Bags may be
empty (no extra condition). -/
def IsRootedTreeDecomp {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) : Prop :=
  (∃! r, T.parent r = none) ∧
    RobertsonSeymour1986.GM5.IsTreeDecomposition G T.treeGraph T.bag

/-- **Adhesion at most `a`.** ibid., §2, p. 14: "For tt′ ∈ E(T), the set B_t ∩ B_t′ is the adhesion
of tt′; the adhesion of the decomposition is the maximum size of an adhesion, or zero if T has no
edge." Every tree edge is `{t, parent t}`, whose adhesion is the published `T.adhesion t`
(`∅` at the root). -/
def AdhesionLE {n : ℕ} (T : RootedTD n) (a : ℕ) : Prop :=
  ∀ t, (T.adhesion t).card ≤ a

/-- **(q, k)-edge-unbreakable decomposition of `G`.** ibid., §1.1, p. 4: "A tree decomposition of H
is (q, k)-edge-unbreakable if every bag is (q, k)-edge-unbreakable", where X is
(q, k)-edge-unbreakable in H "if min{|A ∩ X|, |X \ A|} ≤ q for every A ⊆ V(H) with |δ_H(A)| ≤ k"
(published `IsEdgeUnbreakable` with `V(H) = univ`). Unbreakability is in the whole graph `G`. -/
def IsEdgeUnbreakableDecomp {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (q k : ℕ) : Prop :=
  ∀ t, IsEdgeUnbreakable G Finset.univ (T.bag t) q k

/-- **The decompositions of Section 3.** ibid., §3.1, p. 15: "Fix a rooted tree decomposition T with
bags B_t supplied by Theorem 1.1": a rooted tree decomposition of `G` with adhesion at most `2k`,
every bag (2k, k)-edge-unbreakable in `G`, and the size guarantees of the construction
(pp. 23, 35): at most `n` nodes and nonempty bags when `n > 0`. For the empty graph
we allow the one-node empty-bag decomposition. No connectivity of `G` is assumed. -/
def IsSec3Decomp {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (k : ℕ) : Prop :=
  IsRootedTreeDecomp G T ∧ AdhesionLE T (2 * k) ∧ IsEdgeUnbreakableDecomp G T (2 * k) k ∧
    T.N ≤ max n 1 ∧ (0 < n → ∀ t, (T.bag t).Nonempty)

end SingleExpBisect.Main


