-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic
-- name    : DecrNbhdCover_Supplement_FullyDynamic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:57.406023+00:00
-- url     : https://prove2.me/theorems/db7a79b2-df99-48ff-89bb-427301caface
-- title:
--   Fully dynamic graphs and approximate distance and shortest-path queries
-- statement:
--   A **fully dynamic graph** starts with the vertices $0,\dots,n-1$ and no edges (with $n=0$: no vertices). Its updates are: insertion of an edge with a positive integer length between two distinct present vertices; deletion of a present edge; insertion of an absent vertex; deletion of a present isolated vertex. The $j$-th edge insertion of the run creates edge number $j$. For an operation sequence, $k$ is the number of updates, $L$ the largest inserted length, and the number of insertions is the number of edges that ever lie in the graph.
--
--   The **query clauses** with approximation factor $\beta$ and time bounds $T_d,T_p,T_n$ are:
--
--   1. A distance query $(u,v)$ on present vertices is answered with a value $\hat d\in[0,\infty]$ such that
--   $$\mathrm{dist}_G(u,v)\le\hat d\le\beta\cdot\mathrm{dist}_G(u,v),$$
--   in at most $T_d$ steps.
--   2. A path query $(u,v)$ on distinct present vertices is answered either with a (possibly non-simple) $u$-$v$ path $P$ in $G$ of length at most $\beta\cdot\mathrm{dist}_G(u,v)$, in at most $T_p\,(|E(P)|+1)$ steps, or with "no such path", and then $u$ and $v$ are disconnected and the answer takes at most $T_n$ steps.
--
--   The clauses are stated for any run described by the output and the time of each of its windows, so that they apply both to a word-RAM program and to a reduction with an oracle. The **update time** of such a run is the time outside query windows, initialization included.
--
--   **Formalization Note** Operations are words: `0, u, v, ℓ`, `1, e`, `2, v`, `3, v`, `4, u, v` (distance query), `5, u, v` (path query). $k$, $L$ and the number of insertions are functions of the whole operation sequence, which a program reads online and cannot know in advance.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorems 9.2, 9.3, pp.67–68 (PDF 71–72); Theorem 10.4, pp.80–81 (PDF 84–85); Theorem 10.20, p.89 (PDF 93)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Fully dynamic graphs and approximate distance and shortest-path queries (Theorems 9.2, 9.3, 10.4, 10.20)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Theorems 9.2 and 9.3, pp.67–68 (PDF 71–72); Theorem 10.4, pp.80–81
(PDF 84–85); Theorem 10.20, p.89 (PDF 93).

**Formalization Note.** Operations: `0, u, v, ℓ` inserts an edge joining `u` and `v` with length `ℓ`; `1, e` deletes edge `e`; `2, v` inserts
the isolated vertex `v`; `3, v` deletes the isolated vertex `v`; `4, u, v` is an approximate distance query; `5, u, v` an approximate
shortest-path query. The `j`-th edge insertion of the whole run creates the edge number `j` (from `0`), so an update never has to choose a
name. The graph is determined by the operations alone. Distance answers are `0` (the value `∞`) or `1, p, q` (the rational `p/q`); path
answers are `0` ("no such path") or `1, k, e₁, …, e_k`. The number `k` of updates, the largest inserted length `L` and the number `m` of edges
that ever lie in `G` are functions of the whole operation sequence, which the program reads online and so cannot know in advance. -/

/-- An update of a fully dynamic graph. -/
inductive FDUpd where
  | ins (u v ℓ : ℕ)
  | del (e : ℕ)
  | insV (v : ℕ)
  | delV (v : ℕ)

/-- A fully dynamic graph with the number of the next inserted edge. -/
structure FDState where
  g : Graph ℕ ℕ
  next : ℕ

namespace FDUpd

/-- The update is valid: an inserted edge joins two distinct present vertices and has a positive length; a deleted edge is present; an
inserted vertex is absent; a deleted vertex is present and isolated. -/
def Ok (s : FDState) : FDUpd → Prop
  | .ins u v ℓ => u ∈ s.g.V ∧ v ∈ s.g.V ∧ u ≠ v ∧ 0 < ℓ
  | .del e => e ∈ s.g.E
  | .insV v => v ∉ s.g.V
  | .delV v => v ∈ s.g.V ∧ s.g.incident v = ∅

/-- The effect of an update. -/
def apply (s : FDState) : FDUpd → FDState
  | .ins u v ℓ => { g := { s.g with E := s.g.E ∪ {s.next}, ends := Function.update s.g.ends s.next (u, v),
                                     len := Function.update s.g.len s.next ℓ },
                    next := s.next + 1 }
  | .del e => { s with g := { s.g with E := s.g.E \ {e} } }
  | .insV v => { s with g := { s.g with V := s.g.V ∪ {v} } }
  | .delV v => { s with g := { s.g with V := s.g.V \ {v} } }

/-- The words of an update. -/
def words : FDUpd → List ℕ
  | .ins u v ℓ => [0, u, v, ℓ]
  | .del e => [1, e]
  | .insV v => [2, v]
  | .delV v => [3, v]

end FDUpd

/-- An operation on a fully dynamic graph: an update or a query. -/
inductive FDOp where
  | upd (u : FDUpd)
  | dist (u v : ℕ)
  | path (u v : ℕ)

namespace FDOp

/-- The words of an operation. -/
def words : FDOp → List ℕ
  | .upd u => u.words
  | .dist u v => [4, u, v]
  | .path u v => [5, u, v]

/-- Whether an operation is a query. -/
def isQ : FDOp → Bool
  | .upd _ => false
  | _ => true

/-- The update part of an operation. -/
def updPart : FDOp → List FDUpd
  | .upd u => [u]
  | _ => []

end FDOp

/-- The protocol of a fully dynamic graph: the windows report nothing that changes a state, and query windows output answers. -/
def fdProtocol : Protocol FDOp Empty Unit where
  opWords := FDOp.words
  isQuery := FDOp.isQ
  enc := fun r => nomatch r
  step := fun _ r => nomatch r
  st₀ := ()

/-- The graph on the vertices `0, …, n-1` with no edges. -/
def FDState.init (n : ℕ) : FDState :=
  ⟨ofEdges n [], 0⟩

/-- The graph after the first `t` operations, starting from `n` isolated vertices. -/
def fdAt (n : ℕ) (σ : List FDOp) (t : ℕ) : FDState :=
  ((σ.take t).flatMap FDOp.updPart).foldl FDUpd.apply (FDState.init n)

/-- The updates of the sequence. -/
def fdUpdates (σ : List FDOp) : List FDUpd :=
  σ.flatMap FDOp.updPart

/-- The number `k` of updates. -/
def fdK (σ : List FDOp) : ℕ :=
  (fdUpdates σ).length

/-- The number of edge insertions, i.e. of edges that ever lie in the graph. -/
def fdInsertions (σ : List FDOp) : ℕ :=
  ((fdUpdates σ).filter (fun u => match u with | .ins _ _ _ => true | _ => false)).length

/-- The largest inserted edge length `L` (`0` if there is none). -/
def fdL (σ : List FDOp) : ℕ :=
  maxWord ((fdUpdates σ).map (fun u => match u with | .ins _ _ ℓ => ℓ | _ => 0))

/-- Every operation is valid when it arrives: updates are valid, and queries name present vertices, distinct ones for path queries. -/
def FDValid (n : ℕ) (σ : List FDOp) : Prop :=
  ∀ (t : ℕ) (o : FDOp), σ[t]? = some o →
    match o with
    | .upd u => u.Ok (fdAt n σ t)
    | .dist u v => u ∈ (fdAt n σ t).g.V ∧ v ∈ (fdAt n σ t).g.V
    | .path u v => u ∈ (fdAt n σ t).g.V ∧ v ∈ (fdAt n σ t).g.V ∧ u ≠ v

/-- The sequence has no vertex updates. -/
def NoVertexUpd (σ : List FDOp) : Prop :=
  ∀ u ∈ fdUpdates σ, match u with
    | .insV _ => False
    | .delV _ => False
    | _ => True

/-- The query clauses with approximation factor `β`, for a run whose window `k` (window `0` is the initialization, window `t + 1` belongs
to operation `t`) has output `out k` and takes `time k` steps: a distance query is answered with `d̂` such that
`distG(u, v) ≤ d̂ ≤ β·distG(u, v)`, in at most `Td` steps; a path query is answered with a walk of length at most `β·distG(u, v)` in at most
`Tp·(|E(P)| + 1)` steps, or with "no such path", correctly and in at most `Tn` steps. -/
structure APSPQueries (out : ℕ → List ℕ) (time : ℕ → ℕ) (n : ℕ) (σ : List FDOp) (β Td Tp Tn : ℝ) : Prop where
  dist : ∀ (t u v : ℕ), σ[t]? = some (.dist u v) →
    ∃ x, distAnswer (out (t + 1)) = some x ∧
      (((fdAt n σ t).g.dist u v : ℕ∞) : ℝ≥0∞) ≤ x ∧
      x ≤ ENNReal.ofReal β * (((fdAt n σ t).g.dist u v : ℕ∞) : ℝ≥0∞) ∧
      (time (t + 1) : ℝ) ≤ Td
  path : ∀ (t u v : ℕ), σ[t]? = some (.path u v) →
    (∃ es, pathAnswer (out (t + 1)) = some (some es) ∧
      (fdAt n σ t).g.WalkFromTo u es v ∧
      ((((fdAt n σ t).g.walkLen es : ℕ) : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal β * (((fdAt n σ t).g.dist u v : ℕ∞) : ℝ≥0∞) ∧
      (time (t + 1) : ℝ) ≤ Tp * ((es.length : ℝ) + 1)) ∨
    (pathAnswer (out (t + 1)) = some none ∧ (fdAt n σ t).g.dist u v = ⊤ ∧
      (time (t + 1) : ℝ) ≤ Tn)

/-- The time spent outside query windows, initialization included, for a run whose window `k` takes `time k` steps. -/
def fdUpdateTime (time : ℕ → ℕ) (σ : List FDOp) : ℕ :=
  time 0 + ∑ t ∈ Finset.range σ.length,
    match σ[t]? with
    | some o => if o.isQ then 0 else time (t + 1)
    | none => 0

end DecrNbhdCover.Supplement


