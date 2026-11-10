-- Prove2me | Definitions.Def_MinColorPath_MinorFree_Closures
-- name    : MinColorPath_MinorFree_Closures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:44.982668+00:00
-- url     : https://prove2.me/theorems/d9a0da62-bab7-49d9-b57c-3d1cf042c6ff
-- title:
--   Color closure, color expansion, (strong) base closure; coverings and covering number of a walk
-- statement:
--   Let $\mathcal D=(D,P',\mathrm{cl}')$ be the $d$-diagram of a subgraph $G'$ and $A\subseteq V(D)$. The **color closure** of $A$ is $A\cup\bigcup_{v\in A\cap V(G')}\mathrm{cl}'(v)$; the **color expansion** is $A\cup\{\tau\in P':N_D[\tau]\cap P'\cap A\ne\emptyset\}$; the **base closure** is $A^+=A\cup\bigcup_{\tau\in A\cap P'}(V_\tau(\mathcal D)\cap V(G'))$; the **strong base closure** is
--   $$A^+\cup\{v\in V(G')\cap V_0(\mathcal G): N_{G'}(v)\subseteq A^+\}.$$
--   Each operation applied to every bag of a tree decomposition gives the corresponding operation on the decomposition.
--
--   A **covering** of a walk $\pi$ is a set $\{(\pi_1,\tau_1),\dots,(\pi_r,\tau_r)\}$ of subwalks $\pi_i$ and colors $\tau_i\in P$ such that every occurrence on $\pi$ of a vertex outside $V_0(\mathcal G)$ lies in some $\pi_i$, and $\tau_i\in\mathrm{cl}(v)$ for every vertex $v$ of $\pi_i$. The **covering number** of $\pi$ is the least size of a covering.
--
--   **Formalization Note.** The operations act on `Finset (DV cl H)`; `widthAfter cl H 𝒯 f` is the chromatic width of the bagwise image. A walk enters as its vertex list, a subwalk as a run of positions `(i, j)`, so occurrences are distinguished; `coveringNumber` is an `sInf` over ℕ, taken over a nonempty set for every colored graph (singleton runs work), so it is a genuine minimum.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 41 (§7.1), p. 43 (bagwise operations), p. 44 (coverings)

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

/-!
# Closures and expansions in a d-diagram; coverings of walks (pp. 41, 43, 44)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), §7.1 (p. 41: color closure, color expansion, (strong) base
closure; p. 43: the same operations applied bagwise to a tree decomposition) and §7.2 (p. 44:
coverings and the covering number of a walk).

Conventions.
* `D` is the `d`-diagram of a subgraph `G'` (a `G.Subgraph`); sets of its vertices are finite
  sets of `V(G') ⊕ P'`.
* A walk enters as its vertex list; a subwalk is a run `[i, j]` of consecutive positions
  (0-based), so occurrences of a repeated vertex are distinguished. A covering is a finite set of
  pairs (run, color); its size is its cardinality. The covering number is the least size of a
  covering. For a colored graph every walk has a covering (one singleton run per colored position,
  with one of its colors), so the infimum is over a nonempty set.
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

section Closures

variable {G : SimpleGraph V} (cl : V → Finset C) (H : G.Subgraph)

/-- Color closure (p. 41): `A ∪ ⋃_{v ∈ A ∩ V(G')} cl'(v)`. -/
def colorClosure (A : Finset (DV cl H)) : Finset (DV cl H) :=
  A ∪ Finset.univ.filter fun y => ∃ τ, y = Sum.inr τ ∧ ∃ v, Sum.inl v ∈ A ∧ τ.1 ∈ cl v.1

/-- Color expansion in the `d`-diagram (p. 41): `A ∪ {τ ∈ P' : N_D[τ] ∩ P' ∩ A ≠ ∅}`. -/
def colorExpansion (d : ℕ) (A : Finset (DV cl H)) : Finset (DV cl H) :=
  A ∪ Finset.univ.filter fun y => ∃ τ, y = Sum.inr τ ∧
    ∃ τ', Sum.inr τ' ∈ A ∧ (τ' = τ ∨ (diagGraph cl d H).Adj (Sum.inr τ) (Sum.inr τ'))

/-- Base closure (p. 41): `A ∪ ⋃_{τ ∈ A ∩ P'} (V_τ(D) ∩ V(G'))`. -/
def baseClosure (A : Finset (DV cl H)) : Finset (DV cl H) :=
  A ∪ Finset.univ.filter fun y => ∃ v, y = Sum.inl v ∧ ∃ τ, Sum.inr τ ∈ A ∧ τ.1 ∈ cl v.1

/-- Strong base closure (p. 41): with `A⁺` the base closure,
`A⁺ ∪ {v ∈ V(G') ∩ V_0(G) : N_{G'}(v) ⊆ A⁺}`. -/
def strongBaseClosure (A : Finset (DV cl H)) : Finset (DV cl H) :=
  baseClosure cl H A ∪ Finset.univ.filter fun y => ∃ v, y = Sum.inl v ∧ cl v.1 = ∅ ∧
    ∀ u : ↥(subVerts H), H.Adj v.1 u.1 → (Sum.inl u : DV cl H) ∈ baseClosure cl H A

/-- The chromatic width of the bagwise image `(T, f ∘ β)` of a tree decomposition. -/
def widthAfter {D : SimpleGraph (DV cl H)} (𝒯 : RTD D)
    (f : Finset (DV cl H) → Finset (DV cl H)) : ℕ :=
  Finset.univ.sup fun x => (colSet (diagCl cl H) (f (𝒯.bag x))).card

/-- `|A ∩ (V(G') ∩ V_0(G))|`: the uncolored base vertices in `A`. -/
def uncoloredBaseCount (A : Finset (DV cl H)) : ℕ :=
  ((subVerts H).filter fun v => baseIn A v ∧ cl v = ∅).card

end Closures

/-- A covering of the walk with vertex list `l` (p. 44): a set of pairs `((i, j), τ)` where
`[i, j]` is a run of positions of `l` and `τ ∈ P`, such that (i) every position holding a
vertex outside `V_0(G)` lies in some run, and (ii) `τ ∈ cl(v)` for every vertex `v` of the run. -/
def IsCovering (P : Finset C) (cl : V → Finset C) (l : List V)
    (cov : Finset ((ℕ × ℕ) × C)) : Prop :=
  (∀ e ∈ cov, e.1.1 ≤ e.1.2 ∧ e.1.2 < l.length ∧ e.2 ∈ P ∧
      ∀ k (hk : k < l.length), e.1.1 ≤ k → k ≤ e.1.2 → e.2 ∈ cl l[k]) ∧
    ∀ k (hk : k < l.length), cl l[k] ≠ ∅ → ∃ e ∈ cov, e.1.1 ≤ k ∧ k ≤ e.1.2

/-- The covering number of the walk with vertex list `l` (p. 44). -/
def coveringNumber (P : Finset C) (cl : V → Finset C) (l : List V) : ℕ :=
  sInf {r | ∃ cov, IsCovering P cl l cov ∧ cov.card = r}

end

end MinColorPath.MinorFree


