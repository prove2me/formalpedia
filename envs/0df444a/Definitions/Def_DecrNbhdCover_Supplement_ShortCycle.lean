-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_ShortCycle
-- name    : DecrNbhdCover_Supplement_ShortCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:44.222689+00:00
-- url     : https://prove2.me/theorems/c9849a11-3955-44cd-bf90-bb69b277a9f1
-- title:
--   $(\hat m,r)$-short cycle decompositions
-- statement:
--   Let $G$ be an unweighted graph (all lengths $1$; parallel edges are allowed). An **$(\hat m,r)$-short cycle decomposition** of $G$ is a collection $\mathcal C$ of edge-disjoint cycles of $G$, each of length at most $r$, such that at most $\hat m$ edges of $G$ lie on no cycle of $\mathcal C$.
--
--   The item also fixes the two ways a program presents such a collection. A static algorithm outputs the list of the cycles. A fully dynamic algorithm, whose graph starts with $n$ vertices and no edges and undergoes insertions of unit-length edges and deletions of edges, reports each insertion of a cycle into the collection and each removal of a cycle from it.
--
--   **Formalization Note** A cycle is given by its list of edges and is a closed walk with at least one edge, no repeated edge and no repeated vertex other than its endpoints; two parallel edges form a cycle of length $2$. Edge-disjointness is between cycles of different indices. A cycle id is not reused while it is present.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §10.4, pp.89–90 (PDF 93–94)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Short-cycle decompositions (§10.4, Theorems 10.20 and 10.21)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), §10.4, p.89 (PDF 93): "a (m̂, r)-short cycle decomposition of an unweighted graph
G is a collection C of edge-disjoint cycles of length at most r each, such that the total number of edges of G that do not lie on any cycle in
C is at most m̂."

**Formalization Note.** All edge lengths are `1`; the graph may have parallel edges (the default of §2.1), and two parallel edges form a cycle
of length 2. A collection of cycles is indexed by numbers, each cycle given by its list of edges; edge-disjointness is between cycles of
different indices, and a cycle repeats no edge. *Static.* Input words: `n`, then the edge list; the program outputs
`r, k₁, (k₁ edges), …, k_r, (k_r edges)` and has no operations. *Fully dynamic.* Updates are the edge insertions `0, u, v, 1` and edge
deletions `1, e` of a fully dynamic graph on the vertices `0, …, n-1`, which starts with no edges; the program reports `0, id, k, e₁, …, e_k`
(the cycle `id` is inserted) and `1, id` (cycle `id` is removed), and a cycle id is not reused while it is present. -/

/-- The family `cyc` of edge lists is an `(m̂, r)`-short cycle decomposition of `G`. -/
structure IsShortCycleDecomposition (G : Graph ℕ ℕ) (cyc : ℕ → Option (List ℕ)) (mhat r : ℝ) : Prop where
  cycle : ∀ id c, cyc id = some c → ∃ vs, IsCycle G vs c
  short : ∀ id c, cyc id = some c → (c.length : ℝ) ≤ r
  disj : ∀ id₁ id₂ c₁ c₂ e, cyc id₁ = some c₁ → cyc id₂ = some c₂ → e ∈ c₁ → e ∈ c₂ → id₁ = id₂
  rest : (({e | e ∈ G.E ∧ ¬ ∃ id c, cyc id = some c ∧ e ∈ c}.ncard : ℕ) : ℝ) ≤ mhat

/-- The words of a list of cycles. -/
def cycleWords (cs : List (List ℕ)) : List ℕ :=
  cs.length :: cs.flatMap (fun c => c.length :: c)

/-- The input of Theorem 10.21: an `n`-vertex graph with unit lengths. -/
structure SCInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)

namespace SCInput

variable (I : SCInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The conditions of Theorem 10.21: a valid edge list with all lengths `1`. -/
structure Ok : Prop where
  edges_ok : EdgesOk I.n I.edges
  unit : ∀ t ∈ I.edges, t.2.2 = 1

/-- The input words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges

/-- The graph. -/
def G : Graph ℕ ℕ := ofEdges I.n I.edges

end SCInput

/-- A cycle report of the fully dynamic algorithm. -/
inductive CycleReport where
  | add (id : ℕ) (es : List ℕ)
  | rem (id : ℕ)

/-- The words of a report. -/
def CycleReport.words : CycleReport → List ℕ
  | .add id es => 0 :: id :: es.length :: es
  | .rem id => [1, id]

/-- The effect of a report on the collection: a cycle is inserted under an id not in use, and removed only if present. -/
def cycleStep (s : ℕ → Option (List ℕ)) : CycleReport → Option (ℕ → Option (List ℕ))
  | .add id es => match s id with
    | none => some (Function.update s id (some es))
    | some _ => none
  | .rem id => match s id with
    | some _ => some (Function.update s id none)
    | none => none

/-- The protocol of Theorem 10.20. -/
def cycleProtocol : Protocol FDOp CycleReport (ℕ → Option (List ℕ)) where
  opWords := FDOp.words
  isQuery := FDOp.isQ
  enc := CycleReport.words
  step := cycleStep
  st₀ := fun _ => none

/-- The operations of Theorem 10.20 are valid: each is an edge insertion with length `1` or an edge deletion, valid when it arrives. -/
def CycleValid (n : ℕ) (σ : List FDOp) : Prop :=
  FDValid n σ ∧ ∀ o ∈ σ, match o with
    | .upd (.ins _ _ ℓ) => ℓ = 1
    | .upd (.del _) => True
    | _ => False

end DecrNbhdCover.Supplement


