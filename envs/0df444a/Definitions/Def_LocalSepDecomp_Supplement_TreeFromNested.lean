-- Prove2me | Definitions.Def_LocalSepDecomp_Supplement_TreeFromNested
-- name    : LocalSepDecomp_Supplement_TreeFromNested
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:45:21.70235+00:00
-- url     : https://prove2.me/theorems/dc6f9b32-01d5-4ded-a895-2758b46d1f1a
-- title:
--   All bottlenecks, $N^{\le k}(G)$ and $N(G)$; stars, splitting stars and the tree-decomposition candidate $T(N)$ (Construction 2.3)
-- statement:
--   Let $G$ be a (simple, not necessarily finite) graph. Separations, their orientations, the partial order $(A,B)\ge(C,D)\iff A\subseteq C,\ B\supseteq D$, bottlenecks and Construction 3.6 are those of the mission.
--
--   1. $\mathcal B(G)$ is the set of **all bottlenecks** of $G$, of every order $j\in\mathbb N$. With this choice of $\mathcal B$, Construction 3.6 gives $N^{<k}(G)$, $N^k(G)$, the set $N^{\le k}(G):=N^{<k}(G)\cup N^k(G)$ and $N(G):=\bigcup_{k\in\mathbb N}N^k(G)$.
--   2. For a set $N$ of separations, $\mathrm{ori}(N)$ is the set of all orientations $(A,B),(B,A)$ of the separations $\{A,B\}\in N$.
--   3. A set $\sigma$ of oriented separations is a **star** if $(A,B)\ge(D,C)$ for every two distinct $(A,B),(C,D)\in\sigma$; its **interior** is $\mathrm{int}(\sigma)=\bigcap_{(A,B)\in\sigma}B$ (all of $V(G)$ for $\sigma=\emptyset$).
--   4. A **splitting star** of $N$ is a star $\sigma$ such that $\{A,B\}\in N$ and $(B,A)\notin\sigma$ for every $(A,B)\in\sigma$, and such that every $\{C,D\}\in N$ has an orientation $(C,D)$ with $(C,D)\ge(A,B)$ for some $(A,B)\in\sigma$.
--   5. **Construction 2.3.** The candidate $T(N)=(T,\mathcal V)$ has as nodes the splitting stars of $N$ and as edges the separations in $N$, where $\{A,B\}$ joins the node $t_1\ni(A,B)$ and the node $t_2\ni(B,A)$. The bag of a node $t$ is $\mathrm{int}(t)$ and its part is the induced subgraph $G[\mathrm{int}(t)]$.
--
--   These are the objects of Theorems 3.12 and 3.13: the canonical nested sets of separations built from all bottlenecks, and the tree-decompositions they define.
--
--   **Formalization Note** The paper observes (p.17) that for infinite $N$ an orientation may lie in no splitting star, in which case $T$ is not defined. The edges of $T(N)$ are therefore the $\{A,B\}\in N$ both of whose orientations lie in a splitting star; the theorems assert, as part of their conclusions, that every element of $\mathrm{ori}(N)$ lies in a splitting star, so that the edge set is all of $N$. An orientation lies in at most one splitting star (p.16); the end is picked by choice among them.
-- source:
--   Jacobs, Knappe, Kurkofka, Canonical Graph Decompositions via Local Separations, preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §2.2 p.14 (ori(S)), p.16 (stars, interior, splitting stars), Construction 2.3 p.17, p.12 (N^{≤k} := N^{<k} ∪ N^k), Construction 3.6 p.21 (B = the set of all bottlenecks)

import Mathlib
import Definitions.Def_LocalSepDecomp_Bottlenecks
import Definitions.Def_LocalSepDecomp_Decompositions

set_option autoImplicit false

namespace LocalSepDecomp.Supplement

/-! # The set of all bottlenecks, `N^{≤k}(G)` and `N(G)` for it; stars, splitting stars and the
candidate tree-decomposition `T(N)` of Construction 2.3

R. W. Jacobs, P. Knappe, J. Kurkofka, *Canonical Graph Decompositions via Local Separations*,
preprint (STOC 2027 submission, arXiv:2501.16170; sha256 9a11d48d…), §2.2 (p.14, ori(S)),
p.16 (stars, interiors, splitting stars), Construction 2.3 (p.17), p.12 (`N^{≤k} := N^{<k} ∪ N^k`),
Construction 3.6 (p.21: "without reference to any set B … B the set of all bottlenecks").

**Formalization Note.**
1. Oriented separations are pairs `(A, B) : Set V × Set V`; `(A, B) ⩾ (C, D)` is the published
   `sepGe` (`A ⊆ C ∧ B ⊇ D`, the 6th-edition convention of the paper).
2. `T(N)` has as nodes the splitting stars of `N` and as edges the elements `{A, B} ∈ N`; the edge
   `{A, B}` joins the splitting star containing `(A, B)` and the one containing `(B, A)`. The paper
   notes (p.17) that for infinite `N` an orientation may lie in no splitting star, in which case
   `T` is not defined; the edge type is therefore the set of those `{A, B} ∈ N` both of whose
   orientations lie in a splitting star, and every theorem using `T(N)` asserts in addition
   (`AllOriInSplittingStars`) that every element of `ori(N)` lies in a splitting star, so that the
   edge set is all of `N`. An orientation lies in at most one splitting star (p.16); the end is
   chosen by `Classical.choose` among them.
3. Bags are `int(t) = ⋂_{(A,B) ∈ t} B` (`= V(G)` for the empty star) and parts are `G[int(t)]`. -/

open SimpleGraph

universe u

variable {V : Type u}

/-- The set of **all bottlenecks** of `G`, of every order `j ∈ ℕ` (p.21, p.23). -/
def allBottlenecks (G : SimpleGraph V) : Set (Set (Sym2 (Set V))) :=
  {β | ∃ j : ℕ, IsBottleneck G j β}

/-- **`N^{≤k}(G) := N^{<k}(G) ∪ N^k(G)`** (p.12) of Construction 3.6 (p.21) for the set of all
bottlenecks of `G`. -/
def Nle (G : SimpleGraph V) (k : ℕ) : Set (Sym2 (Set V)) :=
  Nlt G (allBottlenecks G) k ∪ Nk G (allBottlenecks G) k

/-- **`N(G) := ⋃_k N^k(G)`** of Construction 3.6 (p.21) for the set of all bottlenecks of `G`. -/
def Nfull (G : SimpleGraph V) : Set (Sym2 (Set V)) :=
  Nall G (allBottlenecks G)

/-- `ori(N)` (p.14): all orientations `(A, B)` of the separations `{A, B} ∈ N`. -/
def sepOri (G : SimpleGraph V) (N : Set (Sym2 (Set V))) : Set (Set V × Set V) :=
  {p | IsSep G p ∧ unorientSep p ∈ N}

/-- A set `σ` of oriented separations is a **star** (p.16): `(A, B) ⩾ (D, C)` for every two
distinct `(A, B), (C, D) ∈ σ`. -/
def IsSepStar (σ : Set (Set V × Set V)) : Prop :=
  ∀ p ∈ σ, ∀ q ∈ σ, p ≠ q → sepGe p (q.2, q.1)

/-- The **interior** `int(σ) = ⋂_{(A,B) ∈ σ} B` of a star (p.16). -/
def starInterior (σ : Set (Set V × Set V)) : Set V :=
  ⋂ p ∈ σ, p.2

/-- A **splitting star** of `N` (p.16): a star `σ` such that `{A, B} ∈ N` and `(B, A) ∉ σ` for every
`(A, B) ∈ σ`, and such that every `{C, D} ∈ N` has an orientation `(C, D)` with `(C, D) ⩾ (A, B)`
for some `(A, B) ∈ σ`. -/
def IsSplittingStar (N : Set (Sym2 (Set V))) (σ : Set (Set V × Set V)) : Prop :=
  IsSepStar σ ∧ (∀ p ∈ σ, unorientSep p ∈ N ∧ (p.2, p.1) ∉ σ) ∧
    ∀ u ∈ N, ∃ q : Set V × Set V, unorientSep q = u ∧ ∃ p ∈ σ, sepGe q p

/-- The oriented separation `p` lies in some splitting star of `N`. -/
def InSplittingStar (N : Set (Sym2 (Set V))) (p : Set V × Set V) : Prop :=
  ∃ σ, IsSplittingStar N σ ∧ p ∈ σ

/-- Every element of `ori(N)` lies in a splitting star of `N` (so that every `{A, B} ∈ N` has the
two ends required by Construction 2.3). -/
def AllOriInSplittingStars (G : SimpleGraph V) (N : Set (Sym2 (Set V))) : Prop :=
  ∀ p ∈ sepOri G N, InSplittingStar N p

theorem unorientSep_out (u : Sym2 (Set V)) : unorientSep (Quot.out u) = u :=
  Quot.out_eq u

theorem unorientSep_swap (p : Set V × Set V) : unorientSep (p.2, p.1) = unorientSep p :=
  Sym2.eq_swap

/-- The edges of `T(N)`: the `{A, B} ∈ N` both of whose orientations lie in a splitting star (all
of `N` under `AllOriInSplittingStars`). -/
def TEdge (N : Set (Sym2 (Set V))) : Type u :=
  {u : Sym2 (Set V) // u ∈ N ∧ ∀ p : Set V × Set V, unorientSep p = u → InSplittingStar N p}

/-- The splitting star containing `p` (unique, p.16; chosen). -/
noncomputable def splitStarOf (N : Set (Sym2 (Set V))) (p : Set V × Set V)
    (h : InSplittingStar N p) : {σ : Set (Set V × Set V) // IsSplittingStar N σ} :=
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The candidate **`T(N) = (T, V)`** (Construction 2.3, p.17): the nodes of `T` are the splitting
stars of `N`, its edges are the separations in `N`, where `{A, B}` joins the nodes `t₁ ∋ (A, B)`
and `t₂ ∋ (B, A)`; the bag of `t` is `int(t)` and its part is `G[int(t)]`. -/
noncomputable def Tdecomp (G : SimpleGraph V) (N : Set (Sym2 (Set V))) : GraphDecomp.{u, u} G where
  Node := {σ : Set (Set V × Set V) // IsSplittingStar N σ}
  Edge := TEdge N
  ends e := s(splitStarOf N (Quot.out e.1) (e.2.2 _ (unorientSep_out e.1)),
    splitStarOf N ((Quot.out e.1).2, (Quot.out e.1).1)
      (e.2.2 _ ((unorientSep_swap _).trans (unorientSep_out e.1))))
  part t := (⊤ : G.Subgraph).induce (starInterior t.1)

end LocalSepDecomp.Supplement


