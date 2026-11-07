-- Prove2me | Definitions.Def_SmoothedMIS_gatherAlg
-- name    : SmoothedMIS_gatherAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:36.890635+00:00
-- url     : https://prove2.me/theorems/57935c5f-375e-4f57-afd7-0c4401ef7d7e
-- title:
--   The procedure $\mathrm{Gather}(H,A,r)$
-- statement:
--   Let $H$ be a graph whose vertices have distinct identifiers, let $A\subseteq V(H)$ be known to its members, and let $r\ge1$. For $v\in A$, $C_v$ is the component of $H[A]$ containing $v$, labelled by identifiers.
--
--   The procedure runs $r+1$ rounds:
--   1. in the first round every vertex learns which neighbours lie in $A$, and each $v\in A$ forms its list $\mathrm{adj}_A(v)=(\mathrm{ID}(v),\{\mathrm{ID}(u):u\in N_H(v)\cap A\})$;
--   2. in each of the next $r$ rounds every vertex, in $A$ or not, forwards all lists it holds;
--   3. (Check) $v\in A$ forms the graph $M_v$ whose vertices are the identifiers with a received list and whose edges are the pairs reported by these lists, its component $K_v$ containing $v$, and the set $L_v$ of lists of the vertices of $K_v$; $L_v$ is **closed** if every identifier named as a neighbour in a list of $L_v$ has its own list;
--   4. (Output) $v$ outputs $K_v$ if $L_v$ is closed, and $\bot$ otherwise.
--
--   Step 2 of Algorithm 1 runs $\mathrm{Gather}(\mathcal G,\mathcal A,\ell)$, and Lemma 2.4 states its guarantees.
--
--   **Formalization Note** The procedure is a LOCAL algorithm with input "membership in $A$" and output a graph labelled by identifiers or $\bot$; it ignores the random tapes, and vertices outside $A$ output $\bot$.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §2 "A Gathering Primitive", pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_SmoothedMIS_LocalAlg

namespace SmoothedMIS

/-- A graph whose vertices are identifiers: a vertex set `V ⊆ ℕ` and an adjacency `E` on `ℕ`
(only its edges inside `V` are meant). -/
structure LGraph where
  /-- vertices (identifiers) -/
  V : Set ℕ
  /-- edges -/
  E : SimpleGraph ℕ

/-- Local state of a node in `Gather`: a round counter, its identifier, whether it lies in `A`,
and the adjacency lists `(ID(u), {ID(w) : w ∈ N_H(u) ∩ A})` it knows. -/
structure GState where
  /-- rounds done -/
  round : ℕ
  /-- own identifier -/
  id : ℕ
  /-- membership in `A` -/
  inA : Bool
  /-- lists received so far -/
  lists : Set (ℕ × Set ℕ)

/-- The graph `M_v` of a set of lists (p.11): its vertices are the identifiers that have a list,
its edges the pairs reported by these lists. -/
def listsGraph (L : Set (ℕ × Set ℕ)) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun x y =>
    (∃ S, (x, S) ∈ L) ∧ (∃ S, (y, S) ∈ L) ∧ ∃ S, (x, S) ∈ L ∧ y ∈ S

/-- The vertex set of the component `K_v` of `M_v` containing the identifier `x`. -/
def listsComp (L : Set (ℕ × Set ℕ)) (x : ℕ) : Set ℕ :=
  {y | (∃ S, (y, S) ∈ L) ∧ (listsGraph L).Reachable x y}

/-- The lists of the vertices of `K` are **closed**: every identifier appearing as a neighbour in
one of them has its own list (p.11). -/
def listsClosed (L : Set (ℕ × Set ℕ)) (K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∀ S, (x, S) ∈ L → ∀ y ∈ S, ∃ S', (y, S') ∈ L

/-- The edges of `E` with both ends in `K`. -/
def restrictGraph (E : SimpleGraph ℕ) (K : Set ℕ) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun x y => x ∈ K ∧ y ∈ K ∧ E.Adj x y

open Classical in
/-- **The procedure `Gather(H, A, r)`** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed
Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §2, "The procedure Gather(H, A, r)",
p.11), as a LOCAL algorithm whose input is membership in `A` and whose output is a graph
(`some`) or `⊥` (`none`):

* round 1: every node broadcasts its identifier and membership in `A`; each `v ∈ A` forms
  `adj_A(v) = (ID(v), {ID(u) : u ∈ N_H(v) ∩ A})`;
* rounds 2, …, r + 1 (Collect): every node, in `A` or not, broadcasts all lists it holds and adds
  the lists it receives;
* Check / Output (local): `v ∈ A` forms `M_v`, its component `K_v`, and outputs `K_v` if the
  lists of `K_v` are closed, `⊥` otherwise. Nodes outside `A` output `⊥`.

**Formalization Note** The procedure runs `r + 1` rounds and ignores the random tapes. The
output graph is labelled by identifiers: vertex set `K_v`, edges of `M_v` inside `K_v`. -/
noncomputable def gatherAlg (r : ℕ) : LocalAlg Unit Bool (Option LGraph) where
  State := GState
  Msg := ℕ × Bool × Set (ℕ × Set ℕ)
  rounds := fun _ => r + 1
  init := fun _ i b _ => ⟨0, i, b, ∅⟩
  send := fun s => (s.id, s.inA, s.lists)
  step := fun s ms =>
    if s.round = 0 then
      ⟨1, s.id, s.inA,
        if s.inA = true then {(s.id, {x | ∃ L, (x, true, L) ∈ ms})} else ∅⟩
    else
      ⟨s.round + 1, s.id, s.inA, s.lists ∪ {p | ∃ m ∈ ms, p ∈ m.2.2}⟩
  out := fun s =>
    if s.inA = true ∧ listsClosed s.lists (listsComp s.lists s.id) then
      some ⟨listsComp s.lists s.id, restrictGraph (listsGraph s.lists) (listsComp s.lists s.id)⟩
    else none

open Classical in
/-- The output of node `v` after running `Gather(H, A, r)` with identifiers `ids` and tapes
`tape`. -/
noncomputable def gatherOut {V : Type} [Fintype V] (H : SimpleGraph V) (A : Set V)
    (ids : V → ℕ) (r : ℕ) (tape : V → ℕ → Bool) (v : V) : Option LGraph :=
  (gatherAlg r).output H () ids (fun u => decide (u ∈ A)) tape v

/-- The vertex set of `C_v`, the component of `H[A]` containing `v` (empty if `v ∉ A`). -/
def compSet {V : Type} (H : SimpleGraph V) (A : Set V) (v : V) : Set V :=
  {u | ∃ (hv : v ∈ A) (hu : u ∈ A), (H.induce A).Reachable ⟨v, hv⟩ ⟨u, hu⟩}

/-- `C_v` labelled by identifiers: vertex set `ids(C_v)`, edges the pairs `{ids u, ids w}` with
`u, w ∈ C_v` adjacent in `H`. -/
def labComp {V : Type} (H : SimpleGraph V) (A : Set V) (ids : V → ℕ) (v : V) : LGraph :=
  ⟨ids '' compSet H A v, SimpleGraph.fromRel fun x y =>
    ∃ u ∈ compSet H A v, ∃ w ∈ compSet H A v, ids u = x ∧ ids w = y ∧ H.Adj u w⟩

end SmoothedMIS


