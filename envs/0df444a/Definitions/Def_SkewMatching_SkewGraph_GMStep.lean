-- Prove2me | Definitions.Def_SkewMatching_SkewGraph_GMStep
-- name    : SkewMatching_SkewGraph_GMStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:39.953685+00:00
-- url     : https://prove2.me/theorems/0563b78c-922c-449f-811c-cde23c885c57
-- title:
--   Lemma 23 (ii) — Grow, Merge, and the pauses of the resumable search
-- statement:
--   The search of Lemma 23 changes its partition through two operations, for the current $H$.
--
--   1. **Grow:** a pair $\{v,v'\}\subseteq M$ leaves $M$; $v$ is added to $A$ and $v'$ to $A'$.
--   2. **Merge:** for a nonempty $S\subseteq A$ and fragments $X_{i_1},\dots,X_{i_r}$ with $r\ge 0$, the sets $S,S',X_{i_1},\dots,X_{i_r}$ are replaced by the single fragment $S\cup S'\cup X_{i_1}\cup\dots\cup X_{i_r}$, which receives a barrier edge from $A$.
--
--   The initial partition has $A=\{s\}$, $A'=\{s'\}$ and $k=0$. The **pauses** are generated from it: on an initial sub-multigraph the search grows and merges to its first pause, and after symmetric pairs are inserted it resumes, growing and merging to the next pause.
--
--   **Formalization Note** "Receives a barrier edge from $A$" is an edge of $H$ from the new $A$ into the new fragment; that it is the only one is required at the pause, where the partition must be a barrier. The paper only sketches this search.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 23 (ii), pp.15–16

import Mathlib
import Definitions.Def_SkewMatching_Partition

namespace SkewMatching

namespace SkewGraph

open scoped Classical

variable {V E : Type*} (G : SkewGraph V E)

/-- One operation of **Lemma 23 (ii)**, pp.15–16, on the partition of the search in `H`.

* **Grow:** a pair `{v, v′} ⊆ M` leaves `M`; `v` is added to `A` and `v′` to `A′`.
* **Merge:** for a nonempty `S ⊆ A` and fragments `X_{i₁}, …, X_{i_r}` (`r ≥ 0`), the sets
  `S, S′, X_{i₁}, …, X_{i_r}` are replaced by the single fragment `S ∪ S′ ∪ X_{i₁} ∪ ⋯ ∪ X_{i_r}`, which receives a
  barrier edge from `A`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Lemma 23 (ii), p.16.

**Formalization Note.** "Receives a barrier edge from `A`" is an edge of `H` from the new `A` into the new fragment. Its
uniqueness is demanded at the pause (`IsBarrier`), not at each intermediate step. -/
inductive GMStep [Fintype V] (H : Finset E) : Partition V → Partition V → Prop
  | grow (P : Partition V) (v : V) (hv : v ∈ G.restM P) (hv' : G.σV v ∈ G.restM P) :
      GMStep H P ⟨insert v P.A, P.frags⟩
  | merge (P : Partition V) (S : Finset V) (Xs rest : List (Finset V))
      (hS : S ⊆ P.A) (hne : S.Nonempty) (hperm : P.frags.Perm (Xs ++ rest))
      (hedge : ∃ e ∈ H, G.tail e ∈ P.A \ S ∧ G.head e ∈ S ∪ G.symm S ∪ Xs.toFinset.biUnion id) :
      GMStep H P ⟨P.A \ S, (S ∪ G.symm S ∪ Xs.toFinset.biUnion id) :: rest⟩

/-- A finite sequence of Grow and Merge operations. -/
def GMSeq [Fintype V] (H : Finset E) : Partition V → Partition V → Prop :=
  Relation.ReflTransGen (G.GMStep H)

/-- The initial partition of Lemma 23 (ii), p.16: `A = {s}`, `A′ = {s′}`, `k = 0`. -/
def startPart (s : V) : Partition V := ⟨{s}, []⟩

/-- The pauses of the resumable search of **Lemma 23**, pp.15–16, from the source `s`. The search starts on an initial
sub-multigraph, grows and merges to its first pause; after symmetric pairs are inserted it resumes, and grows and merges to the
next pause. -/
inductive Paused [Fintype V] (s : V) : Finset E → Partition V → Prop
  | start (H₀ : Finset E) (P : Partition V) (hH : G.SymmClosed H₀)
      (hseq : G.GMSeq H₀ (startPart s) P) (hp : G.IsPause H₀ s P) : Paused s H₀ P
  | resume (H H' : Finset E) (P P' : Partition V) (hprev : Paused s H P) (hsub : H ⊆ H')
      (hH : G.SymmClosed H') (hseq : G.GMSeq H' P P') (hp : G.IsPause H' s P') : Paused s H' P'

end SkewGraph

end SkewMatching


