-- Prove2me | Definitions.Def_DynConnWC_Op
-- name    : DynConnWC_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:26.18222+00:00
-- url     : https://prove2.me/theorems/a6a7a147-cbaf-47db-a5a0-36042900e81f
-- title:
--   Operations of fully dynamic connectivity, valid sequences, the graph $G_t$ and the correct answer
-- statement:
--   The graph is simple and undirected on the fixed vertex set $V=\{0,\dots,n-1\}$ and starts empty. An **operation** is an insertion of an absent edge $\{u,v\}$, a deletion of a present edge, or a query asking whether $u$ and $v$ are connected. A sequence of operations is **valid** when its updates, in order, form a valid stream from the empty graph; queries are unconstrained.
--
--   For a sequence $\sigma$, $G_t$ is the graph after the updates among the first $t$ operations, and $m_t$ is its number of edges. The correct answer to a query $(u,v)$ in a graph $G$ is the word $1$ if $u$ and $v$ are connected in $G$, and $0$ otherwise.
--
--   Every statement of the mission is about these objects.
--
--   **Formalization Note** Vertices are `Fin n`. Updates and stream validity are the published `PunctSketch.Update` and `PunctSketch.IsValidStream`, which add no condition beyond the source's. Positions in a sequence are $0$-based, so the operation $\sigma[t]$ sees the graph `graphAt σ t`.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), §1, p.1 (PDF 2); §2, p.3 (PDF 4)

import Mathlib
import Definitions.Def_PunctSketch_Update
import Definitions.Def_PunctSketch_IsValidStream

set_option autoImplicit false

namespace DynConnWC

/-! # Operations of fully dynamic connectivity

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), §1, p.1 and §2, p.3: "Let G = (V, E) be a simple undirected graph
on the fixed vertex set V = {0, . . . , n −1}, where n ≥ 2 … We initialize the dynamic algorithm
with E = ∅. An insertion adds an absent edge, and a deletion removes a present edge"; "queries ask
whether two given vertices are connected".

**Formalization Note.** Vertices are `Fin n`. An update is the published
`PunctSketch.Update n` (an edge `{u, v}` and an insert/delete bit), and validity of the update
stream is the published `PunctSketch.IsValidStream` (two distinct endpoints, an insertion only of
an absent edge, a deletion only of a present one, starting from the empty graph). A sequence of
operations interleaves updates with queries; it is **valid** when its updates, in order, form a
valid stream (queries are unconstrained). Positions are 0-based: `graphAt σ t` is the graph after
the updates among the first `t` operations, so the graph seen by the operation `σ[t]` is
`graphAt σ t`. The correct answer to a query is the bit `1` if its two vertices are connected
(reachable) in that graph and `0` otherwise. -/

/-- An operation: insert the edge `{u, v}`, delete it, or ask whether `u` and `v` are connected. -/
inductive Op (n : ℕ) where
  | ins (u v : Fin n)
  | del (u v : Fin n)
  | query (u v : Fin n)
  deriving DecidableEq

variable {n : ℕ}

/-- The update carried by an operation (`none` for a query). -/
def Op.toUpdate? : Op n → Option (PunctSketch.Update n)
  | .ins u v => some ⟨u, v, true⟩
  | .del u v => some ⟨u, v, false⟩
  | .query _ _ => none

/-- Whether an operation is an update (an insertion or a deletion). -/
def Op.IsUpdate (o : Op n) : Prop := o.toUpdate?.isSome

instance (o : Op n) : Decidable o.IsUpdate := by unfold Op.IsUpdate; infer_instance

/-- The updates of a sequence of operations, in order, queries skipped. -/
def updatesOf (σ : List (Op n)) : List (PunctSketch.Update n) := σ.filterMap Op.toUpdate?

/-- A sequence of operations is valid when its updates form a valid stream from the empty graph. -/
def Valid (σ : List (Op n)) : Prop := PunctSketch.IsValidStream (updatesOf σ)

/-- The number of updates (insertions and deletions) in a sequence of operations. -/
def numUpdates (σ : List (Op n)) : ℕ := (updatesOf σ).length

/-- The graph after the updates among the first `t` operations of `σ` (from the empty graph). -/
noncomputable def graphAt (σ : List (Op n)) (t : ℕ) : SimpleGraph (Fin n) :=
  PunctSketch.streamGraph (updatesOf (σ.take t))

open Classical in
/-- `m_t`: the number of edges after the first `t` operations. -/
noncomputable def edgeCount (σ : List (Op n)) (t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Sym2 (Fin n))).filter (fun e => e ∈ (graphAt σ t).edgeSet)).card

open Classical in
/-- The correct answer word to a connectivity query `(u, v)` in the graph `G`: `1` if `u` and `v`
are connected in `G`, `0` otherwise. -/
noncomputable def correctBit (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  if G.Reachable u v then 1 else 0

end DynConnWC


