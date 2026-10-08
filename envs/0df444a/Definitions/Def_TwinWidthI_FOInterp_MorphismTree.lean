-- Prove2me | Definitions.Def_TwinWidthI_FOInterp_MorphismTree
-- name    : TwinWidthI_FOInterp_MorphismTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:06.117822+00:00
-- url     : https://prove2.me/theorems/e7d10006-ff35-44fb-ba95-844c65a8ad7d
-- title:
--   §7.1–7.3, §8 — morphism-trees, automorphisms in (G, P), reductions, reducts, sequence graphs, pruned shuffles, E_k(G, P)
-- statement:
--   Let $G$ be a finite simple graph on $V$ and $\mathcal P$ a partition of $V$.
--
--   **Morphism-trees.** A node of a morphism-tree is identified with the tuple $(v_1,\dots,v_i)$ of vertices along its current path; the root $\varepsilon$ is the empty tuple and the parent of $(v_1,\dots,v_i)$ is $(v_1,\dots,v_{i-1})$. A morphism-tree is a set of tuples containing $\varepsilon$ and closed under prefixes. The *complete $\ell$-morphism-tree* $MT_\ell(V)$ consists of all tuples of length at most $\ell$, with repetitions allowed.
--
--   **Automorphisms and equivalence.** An *automorphism* of a morphism-tree $T$ in $(G,\mathcal P)$ is a bijection $f$ of $T$ onto itself commuting with the parent relation such that, for every node $x$ and every descendant $y$ of $x$, writing $m(z)$ for the last entry of the tuple $z$:
--   1. $m(x)=m(y)$ if and only if $m(f(x))=m(f(y))$;
--   2. $m(x)m(y)\in E(G)$ if and only if $m(f(x))m(f(y))\in E(G)$;
--   3. $m(x)$ and $m(f(x))$ lie in the same part of $\mathcal P$.
--
--   Two distinct sibling nodes $x,x'$ are *equivalent* if some automorphism swaps them. "In $G$" means with the one-part partition. The *$x,x'$-reduction* deletes $x'$ and all its descendants; a *reduction* of $T$ is the result of a finite sequence (possibly empty) of such steps, each performed in the current tree; a *reduct* is a reduction with no equivalent pair of siblings.
--
--   **Red graph and sequence graphs.** The red graph $G_{\mathcal P}$ has the parts of $\mathcal P$ as vertices, two distinct parts being adjacent when they are not homogeneous. For a tuple $S=(v_1,\dots,v_i)$ with $v_j$ in the part $X_j$, the *$\ell$-sequence graph* $\mathrm{sg}_\ell(S)$ on $[i]$ has an edge $jk$, $j<k$, when the distance between $X_j$ and $X_k$ in $G_{\mathcal P}$ is at most $3^{\ell-k}$. The *local root* of $v_k$ in $S$ is $X_j$ for the least index $j$ of the connected component of $k$. $S$ is a *connected tuple rooted at $X$* if $\mathrm{sg}_\ell(S)$ is connected and $v_1\in X$. For a tree $T$ and a part $X$, $T_X$ consists of $\varepsilon$ and the nodes of $T$ that are connected tuples rooted at $X$; $MT_\ell(G,\mathcal P,X)=MT_\ell(V)_X$. A morphism-tree in $(G,\mathcal P,X)$ is one contained in $MT_\ell(G,\mathcal P,X)$.
--
--   **Pruned shuffle.** For a family of morphism-trees $T_X$ in $(G,\mathcal P,X)$, one per part $X$, the *pruned $\ell$-shuffle* consists of the tuples $S$ of length at most $\ell$ such that, for every connected component $K$ of $\mathrm{sg}_\ell(S)$, the subtuple $S|_K$ is a node of $T_X$, where $X$ is the local root of the entries of $K$.
--
--   **Indistinguishability.** $E_k(G,\mathcal P)$ is the graph on $V$ in which $uu'$ is an edge when the depth-1 nodes $(u)$ and $(u')$ are equivalent siblings in some reduction of $MT_k(V)$ performed in $(G,\mathcal P)$. The partition $I_k(G,\mathcal P)$ consists of the connected components of $E_k(G,\mathcal P)$. Section 8 uses $k=\ell+2$.
--
--   These objects carry the proof that interpretations preserve bounded twin-width (Lemmas 7.3, 7.11–7.14, 8.4–8.6).
--
--   **Formalization Note.** Every tree in Sections 7–8 is a reduction of a complete morphism-tree, so a node is determined by the tuple of vertices on its current path, the paper's own "abuse of language" (p. 3:30); morphism-trees are therefore sets of lists `Set (List V)`. The automorphism conditions for a node $x$ and a descendant $y$ are stated for every pair of entries of one tuple. Equivalent siblings are required to be distinct ($v\neq v'$). The sequence graph uses 0-based list indices, so the paper's exponent $3^{\ell-k}$ appears as $3^{\ell-(k+1)}$. Distances in $G_{\mathcal P}$ are extended distances in $\mathbb N\cup\{\infty\}$ (`SimpleGraph.edist`): parts in different components of $G_{\mathcal P}$ are at distance $\infty$, never $0$; $G_{\mathcal P}$ is realised on all subsets of $V$, with the non-parts isolated. The pruned shuffle is given by its characterisation rather than as "shuffle, then prune": in an unpruned node the entries whose local root is $X$ come from the tree of $X$, and distinct components have distinct local roots, so a node of the pruned shuffle is determined by its tuple and its restriction to each component is a node of the tree of the component's local root (the argument of the proof of Lemma 7.13, p. 3:38). A family over all parts covers the paper's families $X_1,\dots,X_p$ of distinct parts by taking $T_X=\{\varepsilon\}$ for the other parts. $E_k$ takes the tree depth $k$ explicitly; the paper's $E_{\ell+2}$ is `Eind G P (ℓ + 2)`, and $I_{\ell+2}$ is represented by connectivity in `Eind G P (ℓ + 2)`.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:30–3:32 §7.1–7.2 (morphism-trees, MT_ℓ(V), isomorphisms, equivalent siblings, reductions, reducts), p. 3:34 (automorphisms in (G, P)), pp. 3:35–3:36 §7.3 (sequence graph, local root, connected tuples, (T, m)_X, MT_ℓ(G, P, X), pruned shuffle), p. 3:42 §8 ((ℓ+2)-indistinguishability, E_{ℓ+2}(G, P), I_{ℓ+2}(G, P))

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting

namespace TwinWidthI.FOInterp

open Finset

/-! ### Morphism-trees as sets of tuples (§7.1–7.2, pp. 3:30–3:32)

Every tree of Sections 7–8 is a reduction of a complete morphism-tree `MT_ℓ(V)`, in which a node
is determined by the tuple of vertices along its current path ("as an abuse of language, we may
identify a node `(u₁, …, uᵢ)` to its current path", p. 3:30). A morphism-tree is therefore
encoded as a set of lists of vertices: the root `ε` is `[]`, the parent of `s ++ [v]` is `s`,
and `m(s ++ [v]) = v`. -/

/-- p. 3:30: a (tuple-encoded) morphism-tree: a set of tuples containing the root `[]` and closed
under taking prefixes (the parent relation is the prefix relation). -/
def IsTupleTree {V : Type*} (T : Set (List V)) : Prop :=
  [] ∈ T ∧ ∀ s ∈ T, ∀ t : List V, t <+: s → t ∈ T

/-- p. 3:30: the complete `ℓ`-morphism-tree `MT_ℓ(V)`: all tuples of elements of `V` (repetitions
allowed) of length at most `ℓ`. -/
def MT (V : Type*) (ℓ : ℕ) : Set (List V) := {s | s.length ≤ ℓ}

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- pp. 3:30–3:31, 3:34: `f` is an automorphism of the morphism-tree `T` in the partitioned graph
`(G, P)`:
1. `f` is a bijection from `T` onto `T`;
2. `f` commutes with the parent relation (it preserves lengths and prefixes);
3. for every node `s` and entries `s[a]`, `s[b]` of its current path (that is, a node `x` and a
   descendant `y` of `x`), `m(x) = m(y) ↔ m(f x) = m(f y)`, `m(x)m(y) ∈ E(G) ↔ m(f x)m(f y) ∈ E(G)`,
   and `m(x)`, `m(f x)` lie in the same part of `P`.

"An automorphism in `G`" (no partition) is the case `P = ⊤`, the partition with one part. -/
def IsAuto (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (T : Set (List V))
    (f : List V → List V) : Prop :=
  Set.BijOn f T T ∧
  (∀ s ∈ T, (f s).length = s.length ∧ ∀ k : ℕ, f (s.take k) = (f s).take k) ∧
  ∀ s ∈ T, ∀ a b : ℕ, ∀ x y x' y' : V,
    s[a]? = some x → s[b]? = some y → (f s)[a]? = some x' → (f s)[b]? = some y' →
      ((x = y ↔ x' = y') ∧ (G.Adj x y ↔ G.Adj x' y') ∧ P.part x = P.part x')

/-- p. 3:31, p. 3:34: the distinct sibling nodes `s ++ [v]` and `s ++ [v']` of `T` are equivalent
in `(G, P)`: some automorphism of `T` in `(G, P)` swaps them. -/
def EquivSiblings (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (T : Set (List V))
    (s : List V) (v v' : V) : Prop :=
  s ++ [v] ∈ T ∧ s ++ [v'] ∈ T ∧ v ≠ v' ∧
    ∃ f, IsAuto G P T f ∧ f (s ++ [v]) = s ++ [v'] ∧ f (s ++ [v']) = s ++ [v]

/-- p. 3:32: `T'` is the `x, x'`-reduction of `T` for two equivalent siblings `x = s ++ [v]`,
`x' = s ++ [v']`: all descendants of `x'` (including `x'`) are deleted. -/
def ReductionStep (G : SimpleGraph V) (P : Finpartition (univ : Finset V))
    (T T' : Set (List V)) : Prop :=
  ∃ s v v', EquivSiblings G P T s v v' ∧ T' = {t ∈ T | ¬ (s ++ [v']) <+: t}

/-- p. 3:32, p. 3:34: `T'` is a reduction of `T` in `(G, P)`: obtained by iterating
`x, x'`-reductions (possibly none). -/
def IsReduction (G : SimpleGraph V) (P : Finpartition (univ : Finset V))
    (T T' : Set (List V)) : Prop :=
  Relation.ReflTransGen (ReductionStep G P) T T'

/-- p. 3:32: `T'` is a reduct of `T` in `(G, P)`: a reduction of `T` in which no pair of siblings
is equivalent. -/
def IsReduct (G : SimpleGraph V) (P : Finpartition (univ : Finset V))
    (T T' : Set (List V)) : Prop :=
  IsReduction G P T T' ∧ ∀ s v v', ¬ EquivSiblings G P T' s v v'

/-! ### The red graph, sequence graphs, connected tuples (§7.3, p. 3:35) -/

/-- p. 3:32, p. 3:35: the red graph `G_P` of a partition, here on all of `Finset V`: two distinct
parts of `P` are adjacent iff they are not homogeneous. Sets that are not parts of `P` are
isolated, so distances between parts are those of `G_P`. -/
def redGraph (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) :
    SimpleGraph (Finset V) where
  Adj X Y := X ∈ P.parts ∧ Y ∈ P.parts ∧ X ≠ Y ∧ ¬ TwinWidthI.BoolWidth.Homogeneous G X Y
  symm := ⟨by
    intro X Y h
    refine ⟨h.2.1, h.1, h.2.2.1.symm, fun hh => h.2.2.2 ?_⟩
    rcases hh with hh | hh
    · exact Or.inl fun x hx y hy => (hh y hy x hx).symm
    · exact Or.inr fun x hx y hy e => hh y hy x hx e.symm⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- p. 3:35: the `ℓ`-sequence graph `sg_ℓ(S)` of a tuple `S = (v₁, …, vᵢ)` on the index set
`[i]` (here `Fin i`, 0-based): for `j < k` there is an edge `jk` iff the distance in `G_P`
between the part of `v_j` and the part of `v_k` is at most `3^{ℓ−k}`, with the paper's 1-based
`k` (hence the exponent `ℓ − (k + 1)` for the 0-based index `k`). Distances are in `ℕ∞`, so
parts in different components of `G_P` are at distance `⊤`. -/
def seqGraph (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (S : List V) :
    SimpleGraph (Fin S.length) :=
  SimpleGraph.fromRel fun j k => j < k ∧
    (redGraph G P).edist (P.part S[j]) (P.part S[k]) ≤ ((3 ^ (ℓ - (k.val + 1)) : ℕ) : ℕ∞)

open Classical in
/-- p. 3:35: the minimum index of the connected component of `k` in `sg_ℓ(S)`. The part of `P`
containing the entry at this index is the local root of `v_k` in `S`. -/
noncomputable def lrootIdx (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ)
    (S : List V) (k : Fin S.length) : Fin S.length :=
  (univ.filter fun j => (seqGraph G P ℓ S).Reachable j k).min' ⟨k, by simp⟩

/-- p. 3:35: the local root of `v_k` in `S`, a part of `P`. -/
noncomputable def localRoot (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ)
    (S : List V) (k : Fin S.length) : Finset V :=
  P.part S[lrootIdx G P ℓ S k]

/-- p. 3:35: `S` is a connected tuple rooted at `X`: its sequence graph `sg_ℓ(S)` is connected
(in particular `S` is non-empty) and its first entry lies in `X`. -/
def IsConnectedTuple (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ)
    (S : List V) (X : Finset V) : Prop :=
  (seqGraph G P ℓ S).Connected ∧ ∃ h : 0 < S.length, S[0] ∈ X

/-- p. 3:35: `(T, m)_X`: the root together with the nodes of `T` whose current path is a
connected tuple rooted at `X`. -/
def restrictTo (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ)
    (T : Set (List V)) (X : Finset V) : Set (List V) :=
  {s ∈ T | s = [] ∨ IsConnectedTuple G P ℓ s X}

/-- p. 3:35: `MT_ℓ(G, P, X) = MT_ℓ(G, P)_X`. -/
def MTX (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (X : Finset V) :
    Set (List V) :=
  restrictTo G P ℓ (MT V ℓ) X

/-- p. 3:35: `T` is an `ℓ`-morphism-tree in `(G, P, X)`: a tuple tree all of whose non-root
nodes are connected tuples rooted at `X`, of length at most `ℓ`. -/
def IsTreeIn (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (X : Finset V)
    (T : Set (List V)) : Prop :=
  IsTupleTree T ∧ T ⊆ MTX G P ℓ X

open Classical in
/-- The subtuple of `S` induced by the connected component of the index `k` in `sg_ℓ(S)`,
entries kept in their order in `S`. -/
noncomputable def compSubtuple (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ) (S : List V)
    (k : Fin S.length) : List V :=
  ((List.finRange S.length).filter fun j =>
      decide ((seqGraph G P ℓ S).Reachable j k)).map fun j => S[j]

/-- p. 3:36: the pruned `ℓ`-shuffle of a family of morphism-trees `F X`, `X` a part of `P`, with
`F X` a morphism-tree in `(G, P, X)` (a part that takes no part in the shuffle has `F X = {[]}`).
A tuple `S` of length at most `ℓ` is a node iff, for every connected component `K` of `sg_ℓ(S)`,
the subtuple `S|_K` is a node of `F X`, where `X` is the local root of the entries of `K`.

This characterises the paper's "usual shuffle, then prune the irrelevant nodes": in an unpruned
node every entry whose local root is `X` comes from the tree of `X`, and the entries coming from
the tree of `X` are exactly those of the component with local root `X` (distinct components have
distinct local roots). -/
def prunedShuffle (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (ℓ : ℕ)
    (F : Finset V → Set (List V)) : Set (List V) :=
  {S | S.length ≤ ℓ ∧
    ∀ k : Fin S.length, compSubtuple G P ℓ S k ∈ F (localRoot G P ℓ S k)}

/-! ### Indistinguishability (§8, p. 3:42) -/

/-- p. 3:42: the graph `E_k(G, P)` (used with `k = ℓ + 2`): `u u'` is an edge iff the depth-1
nodes `(u)` and `(u')` are equivalent siblings (of `ε`) in some reduction of `MT_k(G, P)`,
reductions performed in `(G, P)`. -/
def Eind (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (k : ℕ) : SimpleGraph V where
  Adj u u' := ∃ T, IsReduction G P (MT V k) T ∧ EquivSiblings G P T [] u u'
  symm := ⟨by
    rintro u u' ⟨T, hT, h1, h2, hne, f, hf, hf1, hf2⟩
    exact ⟨T, hT, h2, h1, hne.symm, f, hf, hf2, hf1⟩⟩
  loopless := ⟨fun _ ⟨_, _, _, _, hne, _⟩ => hne rfl⟩

end TwinWidthI.FOInterp


