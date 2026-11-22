-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_Common
-- name    : DecrNbhdCover_Supplement_Common
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:00.806236+00:00
-- url     : https://prove2.me/theorems/1417920f-d344-40fe-a15b-aade0318405c
-- title:
--   Shared objects of the supplement: $\log_2(2+x)$, reported dynamic graphs, cycles, forests, answer formats
-- statement:
--   This item collects the objects shared by the added theorems.
--
--   1. $\mathrm{lg}(x)=\log_2(2+x)$ and $\mathrm{mx1}(m)=\max(1,m)$. They replace $\log x$ and $m$ in an upper bound where the printed factor would vanish at a degenerate input.
--   2. A **reported dynamic graph** is a graph with parallel edges, no self-loops and positive integer lengths that a program maintains by reporting each change: insertion of a vertex, deletion of a vertex together with its incident edges, insertion of an edge with a number never used before, two distinct present endpoints and a positive length, and deletion of a present edge. The record keeps the current graph and the set of edge numbers ever used.
--   3. A **cycle** of a graph is a closed walk with at least one edge that repeats no edge and repeats no vertex other than its first and last. In a multigraph two parallel edges form a cycle of length $2$. A **forest** is a graph with no cycle.
--   4. A **distance answer** is the value $\infty$ or a nonnegative rational $p/q$. A **path answer** is either "no path" or a list of edge numbers.
--   5. The **later time** of a session is its total update time minus the time of the initialization window.
--
--   These conventions are used by the emulator, tree-cover, short-cycle and shortest-path statements of the supplement.
--
--   **Formalization Note** Reports are words: `0, v`, `1, v`, `2, e, u, w, ℓ`, `3, e`. An illegal report makes the record undefined, so a run that emits one fails its specification. A distance answer is `0` (for $\infty$) or `1, p, q` with $q\ne0$; a path answer is `0` or `1, k, e₁, …, e_k`.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §2.1, p.13 (PDF 17); p.72 (PDF 76); Definition 10.6, p.82 (PDF 86); §10.4, p.89 (PDF 93)

import Mathlib
import Definitions.Def_DecrNbhdCover_Graph
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Shared objects of the supplement: logarithms, reported dynamic graphs, cycles and forests, answer formats

Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission,
sha256 4278ef58…), §2.1, p.13 (PDF 17): "All logarithms are to the base of 2"; "By default graphs may contain parallel edges but
no self loops"; p.72 (PDF 76): "Recall that paths may be non-simple unless mentioned otherwise"; §10.4, p.89 (PDF 93) for cycles;
Definition 10.6, p.82 (PDF 86) for forests.

**Formalization Note.** `lg x = log₂(2 + x)` replaces `log x` in an upper bound, so that the bound does not vanish at `x ≤ 1`
(where every algorithm still spends a step), and `mx1 m = max(1, m)` replaces `m` in `m^a`. A **reported dynamic graph** is a
graph that the program maintains and reports word by word: `0, v` (insert vertex `v`), `1, v` (delete `v` with its edges),
`2, e, u, w, ℓ` (insert edge `e` joining `u ≠ w` with length `ℓ > 0`), `3, e` (delete edge `e`). An edge number is never reused,
so `ever` is the set of edges that ever lay in the graph. A **cycle** is a closed walk with at least one edge that repeats no edge
and no vertex except that it ends where it starts; in a multigraph two parallel edges form a cycle of length 2. A **forest** is a
graph with no cycle. Distance answers are `0` (the value `∞`) or `1, p, q` (the rational `p/q`); path answers are `0` (no path) or
`1, k, e₁, …, e_k`. -/

/-- `log₂(2 + x)`. -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 (2 + x)

/-- `max(1, m)` as a real number. -/
def mx1 (m : ℕ) : ℝ := ((max 1 m : ℕ) : ℝ)

/-- A report on a dynamic graph maintained by the program. -/
inductive DynReport where
  | addV (v : ℕ)
  | delV (v : ℕ)
  | addE (e u w ℓ : ℕ)
  | delE (e : ℕ)

/-- The words of a report. -/
def DynReport.words : DynReport → List ℕ
  | .addV v => [0, v]
  | .delV v => [1, v]
  | .addE e u w ℓ => [2, e, u, w, ℓ]
  | .delE e => [3, e]

/-- A reported dynamic graph: the current graph, and the set of edge numbers ever used. -/
structure DynState where
  g : Graph ℕ ℕ
  ever : Set ℕ

/-- The empty graph. -/
def DynState.empty : DynState :=
  ⟨⟨∅, ∅, fun _ => (0, 0), fun _ => 0⟩, ∅⟩

open Classical in
/-- The effect of a report: a vertex is inserted only if absent and deleted only if present (with its edges); an edge is inserted
only with a never used number, two distinct present endpoints and a positive length, and deleted only if present. `none` on an
illegal report. -/
noncomputable def DynState.step (s : DynState) : DynReport → Option DynState
  | .addV v => if v ∉ s.g.V then some { s with g := { s.g with V := s.g.V ∪ {v} } } else none
  | .delV v => if v ∈ s.g.V then
      some { s with g := { s.g with V := s.g.V \ {v}, E := s.g.E \ s.g.incident v } } else none
  | .addE e u w ℓ => if e ∉ s.ever ∧ u ∈ s.g.V ∧ w ∈ s.g.V ∧ u ≠ w ∧ 0 < ℓ then
      some { g := { s.g with E := s.g.E ∪ {e}, ends := Function.update s.g.ends e (u, w),
                             len := Function.update s.g.len e ℓ },
             ever := s.ever ∪ {e} } else none
  | .delE e => if e ∈ s.g.E then some { s with g := { s.g with E := s.g.E \ {e} } } else none

/-- `vs, es` form a cycle of `G`: a closed walk with at least one edge, no repeated edge, and no repeated vertex other than its
endpoints. -/
def IsCycle (G : Graph ℕ ℕ) (vs es : List ℕ) : Prop :=
  G.IsWalk vs es ∧ es ≠ [] ∧ es.Nodup ∧ vs.head? = vs.getLast? ∧ vs.tail.Nodup

/-- `G` is a forest: it has no cycle. -/
def IsForest (G : Graph ℕ ℕ) : Prop :=
  ∀ vs es, ¬ IsCycle G vs es

/-- A distance answer: `0` is `∞`, and `1, p, q` is `p/q` (`q ≠ 0`). -/
noncomputable def distAnswer : List ℕ → Option ℝ≥0∞
  | [0] => some ⊤
  | [1, p, q] => if q = 0 then none else some (ENNReal.ofReal ((p : ℝ) / (q : ℝ)))
  | _ => none

/-- A path answer: `0` reports that there is no path, and `1, k, e₁, …, e_k` is a path with these edges. -/
def pathAnswer : List ℕ → Option (Option (List ℕ))
  | [0] => some none
  | 1 :: k :: es => if es.length = k then some (some es) else none
  | _ => none

/-- The time spent in the update windows after initialization (query windows excluded). -/
noncomputable def laterTime {Op Rep St : Type} (π : Protocol Op Rep St) (W : ℕ) (P : Program) (init : List ℕ)
    (σ : List Op) : ℕ :=
  π.updateTime W P init σ - wTime W P (π.blocks init σ) 0

end DecrNbhdCover.Supplement


