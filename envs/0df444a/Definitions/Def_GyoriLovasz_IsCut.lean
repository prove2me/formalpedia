-- Prove2me | Definitions.Def_GyoriLovasz_IsCut
-- name    : GyoriLovasz_IsCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:17.959798+00:00
-- url     : https://prove2.me/theorems/cb8dd6b5-cd3c-4f52-9ee6-c8090e2aa008
-- title:
--   Cut separating a vertex from the terminals; minimum and tightest minimum cuts
-- statement:
--   For $v\in V\setminus T$, a **cut separating $v$ from $T$** is a partition $C=(L_C,S_C,R_C)$ of $V$ such that $v\in R_C$, $T\subseteq L_C\cup S_C$, and no edge goes from $R_C$ to $L_C$. Its size is $|C|=|S_C|$. A **minimum cut** has the least size among all cuts separating $v$ from $T$.
--
--   The **tightest minimum cut** (Definition 2.8) is the intersection of all minimum cuts, where (Definition 2.5) the intersection has as left side the intersection of the left sides, as right side the union of the right sides, and as separator all remaining vertices. This item defines the predicate "$(L,S,R)$ is the tightest minimum cut": it is a minimum cut, $L$ is the intersection of the left sides of all minimum cuts, and $R$ is the union of their right sides.
--
--   **Formalization Note** The tightest cut is pinned by all minimum cuts, not by inclusion-minimality of one cut. Its existence (Corollary 2.7) is a clause of the mission's statement of Lemma 3.1.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 2.3, pp.14–15; Definition 2.5, p.15; Definition 2.8, p.17

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **Cut separating `v` from `T`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.3, pp.14–15: "a partition C = (L_C, S_C, R_C) of V such
that: v ∈ R_C, T ⊆ L_C ∪ S_C (equivalently, T ∩ R_C = ∅), and there is no directed edge from R_C to L_C." -/
structure IsCut {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (v : V)
    (L S R : Finset V) : Prop where
  cover : L ∪ S ∪ R = G.verts
  disj_LS : Disjoint L S
  disj_LR : Disjoint L R
  disj_SR : Disjoint S R
  mem_R : v ∈ R
  terminals : T ⊆ L ∪ S
  no_arc : ∀ a ∈ G.arcs, a.1 ∈ R → a.2 ∉ L

/-- A minimum cut separating `v` from `T`: its size `|S_C|` is least among all such cuts (Definition 2.3,
p.15; Lemma 2.4, p.15). -/
def IsMinCut {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (v : V) (L S R : Finset V) : Prop :=
  IsCut G T v L S R ∧ ∀ L' S' R', IsCut G T v L' S' R' → S.card ≤ S'.card

/-- **Tightest minimum cut.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.8, p.17: "the cut obtained by intersecting all minimum cuts
separating v from T", with the intersection of Definition 2.5, p.15: `L` is the intersection of the left
sides, `R` is the union of the right sides, and the separator contains all remaining vertices.

**Formalization Note.** A predicate on `(L, S, R)`, not "some inclusion-minimal cut": `L` and `R` are pinned
over all minimum cuts, and being a minimum cut itself pins `S`. Existence is a clause of `lemma_3_1`. -/
def IsTightest {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (v : V)
    (L S R : Finset V) : Prop :=
  IsMinCut G T v L S R ∧
    (∀ x, x ∈ L ↔ ∀ L' S' R', IsMinCut G T v L' S' R' → x ∈ L') ∧
    (∀ x, x ∈ R ↔ ∃ L' S' R', IsMinCut G T v L' S' R' ∧ x ∈ R')

end GyoriLovasz


