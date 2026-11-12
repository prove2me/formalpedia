-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_DynamicSplitting
-- name    : DynEdgeColorLLL_Main_DynamicSplitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:23.170837+00:00
-- url     : https://prove2.me/theorems/d1755fd2-c6aa-4fe6-9fda-34c5a3b17e71
-- title:
--   One update of the dynamic splitting — Search, critical failures, affected regions and the graph Ĝ
-- statement:
--   Fix one update that inserts or deletes the edge $e=\{u,v\}$, $u\ne v$, turning $G^{old}$ into $G^{new}$. Both instances use the same directions and categories for every edge.
--
--   **Failure discovery (§6.2.1).** The initial Search calls are $(u,\mathrm{path}_{e,R})$, $(v,\mathrm{path}_{e,R})$ and every pair of $F^{old}$ whose old cluster contains one of them. A Search call on a pair that is a seed failure after the update calls Search on $(w,P(b))$ when $b\ne r_T$ and $\deg_{\bar E^{new}_b}(w)>U_{\mathrm{dep}(b)}$, and on every pair of its new cluster. Each pair is visited at most once, so the visited pairs form the least set closed under these rules. $F^{new}$ keeps the unvisited pairs of $F^{old}$ and contains a visited pair exactly when it is a seed failure after the update.
--
--   **Critical failures (Definition 7).** $(w,a)$ is a critical failure if, for $\alpha=old$ or $\alpha=new$, it is a seed failure in $T^\alpha$ and either $a=r_T$ or $(w,P(a))$ is not a seed failure in $T^\alpha$.
--
--   **Affected regions and $\hat G$ (Definition 8).** For a critical failure $(w,a)$, the affected region $R_{w,a}$ is the $\rho_{\mathrm{dep}(a)}$-hop neighbourhood of $w$ in $\bar E^\cup_a=\bar E^{old}_a\cup\bar E^{new}_a$. The graph $\hat G$ has vertex set
--   $$\hat V=\{\langle x,a\rangle:x\in V(R_{w,a})\text{ for some critical failure }(w,a)\},$$
--   a horizontal edge between $\langle x,a\rangle$ and $\langle y,a\rangle$ whenever $x,y$ lie in a common $R_{w,a}$, and a vertical edge between $\langle x,a\rangle$ and $\langle x,b\rangle$ for comparable $a\ne b$ with both in $\hat V$. $\hat K(\langle w,a\rangle)$ is the component of $\langle w,a\rangle$ in $\hat G$, and is empty if $\langle w,a\rangle\notin\hat V$.
--
--   **Randomness.** For Lemmas 20 and 21, the directions and categories of all pairs at all depths $d<R$ are independent and uniform. Probabilities and expectations are normalized counts over this finite space. The conditioning of Lemma 20 fixes all choices at depths below $\mathrm{dep}(a)$, the depth-$\mathrm{dep}(a)$ choices of every pair that is not an edge of $\bar E^\cup_a$ incident to $w$, and all choices of $e$.
--
--   **Formalization Note.** Category $i$ of the finite space stands for the paper's $i+1\in[m_d]$. Pairs of vertices that are not edges also carry choices, which no statement reads.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §6.2 and §6.2.1 Failure Discovery Stage, printed p. 28 (PDF p. 30); §6.2.2 Definitions 7–8, the affected region and K̂, printed pp. 34–35 (PDF pp. 36–37)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting

namespace DynEdgeColorLLL.Main

/-! # One update of the dynamic splitting: failure discovery, critical failures and `Ĝ`

Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §6.2 and §6.2.1 "Failure
Discovery Stage", printed p. 28 (PDF p. 30); §6.2.2, Definitions 7–8, printed pp. 34–35
(PDF pp. 36–37).

* An update replaces `G^old` by `G^new`, inserting or deleting the edge `e = {u, v}`, `u ≠ v`. The
  random choices of every edge are shared by the two instances.
* **Search.** Each pair is visited at most once, so the set of visited pairs is the least set that
  contains the initial calls (`(u, path_{e,R})`, `(v, path_{e,R})` and every pair of `F^old` whose
  old cluster contains one of these two) and that, for every visited pair `(w, b)` which is a seed
  failure after the update, contains `(w, P(b))` when `b ≠ r_T` and `deg_{Ē^new_b}(w) > U_{dep(b)}`,
  and every pair of the new cluster of `(w, b)`. A visited pair is in `F^new` iff it is a seed
  failure after the update; an unvisited pair is in `F^new` iff it is in `F^old`.
* **Randomness.** For Lemmas 20–21 the directions and categories at depths `0, …, R-1` of all
  pairs `Sym2 V` are independent and uniform (`dir ∈ {LC, RC}`, `cat ∈ [m_d]`), i.e. the uniform
  law on the finite space `RandSpace`; probabilities and expectations are normalised counts. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G'` arises from `G` by inserting the non-edge `{u, v}` or deleting the edge `{u, v}`,
`u ≠ v`. -/
def IsEdgeUpdate (G G' : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ((¬ G.Adj u v ∧ G' = G ⊔ SimpleGraph.edge u v) ∨
    (G.Adj u v ∧ G' = G.deleteEdges {s(u, v)}))

/-- The pairs visited by the Search calls of the failure discovery stage (§6.2.1). -/
inductive Visited (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V) (u v : V)
    (Fold : Set (V × List Bool)) : V × List Bool → Prop
  | init_u : Visited Δ E Gold Gnew c u v Fold (u, routePath c s(u, v) (depthR Δ E))
  | init_v : Visited Δ E Gold Gnew c u v Fold (v, routePath c s(u, v) (depthR Δ E))
  | init_old (p : V × List Bool) : p ∈ Fold →
      (InCluster Δ E Gold c p (u, routePath c s(u, v) (depthR Δ E)) ∨
        InCluster Δ E Gold c p (v, routePath c s(u, v) (depthR Δ E))) →
      Visited Δ E Gold Gnew c u v Fold p
  | up (p : V × List Bool) : Visited Δ E Gold Gnew c u v Fold p → IsSeedFailure Δ E Gnew c p →
      p.2 ≠ [] → U Δ p.2.length < edgeDeg (idealEdges Gnew c p.2) p.1 →
      Visited Δ E Gold Gnew c u v Fold (p.1, p.2.dropLast)
  | cluster (p q : V × List Bool) : Visited Δ E Gold Gnew c u v Fold p →
      IsSeedFailure Δ E Gnew c p → InCluster Δ E Gnew c p q →
      Visited Δ E Gold Gnew c u v Fold q

/-- `F^new`: the seed-failure set after all Search calls of the update `{u, v}`. -/
def searchResult (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V) (u v : V)
    (Fold : Set (V × List Bool)) : Set (V × List Bool) :=
  {p | (p ∈ Fold ∧ ¬ Visited Δ E Gold Gnew c u v Fold p) ∨
    (Visited Δ E Gold Gnew c u v Fold p ∧ IsSeedFailure Δ E Gnew c p)}

/-- Definition 7 (critical failure) for the update `G^old → G^new`: for some `α ∈ {old, new}`,
`(w, a)` is a seed failure in `T^α` and either `a = r_T` or `(w, P(a))` is not a seed failure in
`T^α`. -/
def IsCriticalFailure (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V)
    (p : V × List Bool) : Prop :=
  ∃ G ∈ ({Gold, Gnew} : Set (SimpleGraph V)),
    IsSeedFailure Δ E G c p ∧ (p.2 = [] ∨ ¬ IsSeedFailure Δ E G c (p.1, p.2.dropLast))

/-- `Ē^∪_a = Ē^old_a ∪ Ē^new_a`. -/
noncomputable def idealUnion (Gold Gnew : SimpleGraph V) (c : Choices V) (a : List Bool) :
    Finset (Sym2 V) :=
  idealEdges Gold c a ∪ idealEdges Gnew c a

/-- The vertex set of the affected region `R_{w,a}`: the `ρ_{dep(a)}`-hop neighbourhood of `w` in
`Ē^∪_a`. -/
def affectedRegion (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V) (w : V)
    (a : List Bool) : Set V :=
  {x | ∃ P : (SimpleGraph.fromEdgeSet (idealUnion Gold Gnew c a : Set (Sym2 V))).Walk w x,
    P.length ≤ rhod Δ E a.length}

/-- `V̂` (Definition 8): the pairs `⟨x, a⟩` with `x ∈ V(R_{w,a})` for some critical failure
`(w, a)`. -/
def hatVertices (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V) :
    Set (V × List Bool) :=
  {p | ∃ w, IsCriticalFailure Δ E Gold Gnew c (w, p.2) ∧
    p.1 ∈ affectedRegion Δ E Gold Gnew c w p.2}

/-- The edges of `Ĝ` (Definition 8): horizontal edges between `⟨x, a⟩` and `⟨y, a⟩` when `x, y`
lie in a common affected region `R_{w,a}`, and vertical edges between `⟨x, a⟩` and `⟨x, b⟩`, both
in `V̂`, for comparable `a ≠ b`. -/
def hatRel (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V)
    (p q : V × List Bool) : Prop :=
  (p.2 = q.2 ∧ ∃ w, IsCriticalFailure Δ E Gold Gnew c (w, p.2) ∧
      p.1 ∈ affectedRegion Δ E Gold Gnew c w p.2 ∧ q.1 ∈ affectedRegion Δ E Gold Gnew c w p.2) ∨
    (p.1 = q.1 ∧ p.2 ≠ q.2 ∧ (p.2 <+: q.2 ∨ q.2 <+: p.2) ∧
      p ∈ hatVertices Δ E Gold Gnew c ∧ q ∈ hatVertices Δ E Gold Gnew c)

/-- The graph `Ĝ = (V̂, Ê)` of Definition 8 (on `V × T`; pairs outside `V̂` are isolated). -/
def hatGraph (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V) :
    SimpleGraph (V × List Bool) :=
  SimpleGraph.fromRel (hatRel Δ E Gold Gnew c)

/-- `K̂(⟨w, a⟩)`: the component of `⟨w, a⟩` in `Ĝ` if `⟨w, a⟩ ∈ V̂`, and empty otherwise. -/
def hatComponent (Δ : ℕ) (E : ℝ) (Gold Gnew : SimpleGraph V) (c : Choices V)
    (p : V × List Bool) : Set (V × List Bool) :=
  {q | p ∈ hatVertices Δ E Gold Gnew c ∧ (hatGraph Δ E Gold Gnew c).Reachable p q}

/-- The random choices at depths `0, …, R-1` of every pair of `Sym2 V`: a direction in `Bool` and
a category in `Fin m_d` (category `i` stands for the paper's `i + 1 ∈ [m_d]`). -/
abbrev RandSpace (V : Type*) (Δ : ℕ) (E : ℝ) :=
  (Sym2 V → Fin (depthR Δ E) → Bool) × (Sym2 V → (j : Fin (depthR Δ E)) → Fin (md Δ j))

/-- The choices encoded by a point of `RandSpace` (unused depths `≥ R` get `LC` and category 0). -/
noncomputable def RandSpace.toChoices {Δ : ℕ} {E : ℝ} (ω : RandSpace V Δ E) : Choices V where
  dir e j := if h : j < depthR Δ E then ω.1 e ⟨j, h⟩ else false
  cat e j := if h : j < depthR Δ E then (ω.2 e ⟨j, h⟩).val + 1 else 0

open Classical in
/-- The probability of an event under independent uniform choices: the fraction of points of the
finite space `RandSpace` where it holds. -/
noncomputable def randProb (Δ : ℕ) (E : ℝ) (P : RandSpace V Δ E → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card (RandSpace V Δ E) : ℝ)

/-- The expectation of `X` under independent uniform choices. -/
noncomputable def randExp (Δ : ℕ) (E : ℝ) (X : RandSpace V Δ E → ℝ) : ℝ :=
  (∑ ω, X ω) / (Fintype.card (RandSpace V Δ E) : ℝ)

/-- `ω` agrees with `ω₀` on all choices of the pair `e`. -/
def AgreeOnEdge {Δ : ℕ} {E : ℝ} (e : Sym2 V) (ω₀ ω : RandSpace V Δ E) : Prop :=
  ∀ j, ω.1 e j = ω₀.1 e j ∧ ω.2 e j = ω₀.2 e j

/-- The conditioning of Lemma 20 for the vertex `w`, the node `a` and the updated pair `e`: `ω`
agrees with `ω₀` on all choices at depths smaller than `dep(a)`, on the depth-`dep(a)` choices of
every pair that is not an edge of `Ē^∪_a` incident to `w` (`Ē^∪_a` is determined by the choices at
depths `< dep(a)`, so it is computed from `ω₀`), and on all choices of `e`. -/
noncomputable def AgreeLemma20 {Δ : ℕ} {E : ℝ} (Gold Gnew : SimpleGraph V) (w : V)
    (a : List Bool) (e : Sym2 V) (ω₀ ω : RandSpace V Δ E) : Prop :=
  (∀ (f : Sym2 V) (j : Fin (depthR Δ E)), j.val < a.length →
      ω.1 f j = ω₀.1 f j ∧ ω.2 f j = ω₀.2 f j) ∧
    (∀ (f : Sym2 V) (j : Fin (depthR Δ E)), j.val = a.length →
      ¬ (f ∈ idealUnion Gold Gnew ω₀.toChoices a ∧ w ∈ f) →
      ω.1 f j = ω₀.1 f j ∧ ω.2 f j = ω₀.2 f j) ∧
    AgreeOnEdge e ω₀ ω

end DynEdgeColorLLL.Main


