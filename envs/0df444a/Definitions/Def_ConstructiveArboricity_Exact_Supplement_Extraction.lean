-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Supplement_Extraction
-- name    : ConstructiveArboricity_Exact_Supplement_Extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:13:18.170122+00:00
-- url     : https://prove2.me/theorems/ec5a8799-943c-4ada-9261-0cad36c90a42
-- title:
--   Finite phases of ExtractOnePseudoforest and the descending first stage
-- statement:
--   Algorithm 2 starts with no selected edges. A saturated vertex still needs to choose while it has outdegree $d$ in the current orientation and no selected outgoing edge. Each phase scans vertices in label order. At an eligible root, the first outgoing edge leaving its selected-edge component is chosen; if none leaves, the first outgoing edge is chosen. A merge marks every vertex in its union for the current phase. The routine stops when no vertex needs a choice.
--
--   The internal input has an outgoing adjacency directory with degrees and offsets. Each adjacency entry contains the original edge identity and its head. The outer first stage prepares this representation, then executes the extraction rounds at bounds $k,k-1,\ldots,1$ with deletion. These definitions specify transitions and termination, without assuming pseudoforest correctness or any complexity bound.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. §§2–5 and Appendix A, definition interface, PDF/printed p.10.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface

/-! Finite phase semantics of Algorithm 2 and lines 1–5 of Algorithm 1,
pp.10–12. Component tests are ordinary finite graph reachability; no selection,
acyclicity, cycle-count or time conclusion is included in these semantics.
The internal adjacency directory is prepared by the outer routine in O(n+m).
The RAM still charges all operations performed by the internal routine. -/
namespace ConstructiveArboricity.Exact.Supplement
noncomputable section
open Classical

variable (G : Graph) (tail : Fin G.m → Fin G.n)

def outgoing (A : Finset (Fin G.m)) (v : Fin G.n) : Finset (Fin G.m) :=
  A.filter fun e => tail e = v

def needsChoice (A S : Finset (Fin G.m)) (d : ℕ) (v : Fin G.n) : Prop :=
  (outgoing G tail A v).card = d ∧ outgoing G tail S v = ∅

def component (S : Finset (Fin G.m)) (v : Fin G.n) : Finset (Fin G.n) :=
  Finset.univ.filter fun u => (G.onEdges (↑S)).Reachable v u

/-- Selected edges and vertices whose component has merged in this phase. -/
abbrev ExtractState (G : Graph) := Finset (Fin G.m) × Finset (Fin G.n)

def extractVisit (A : Finset (Fin G.m)) (d : ℕ)
    (s : ExtractState G) (v : Fin G.n) : ExtractState G :=
  let C := component G s.1 v
  if needsChoice G tail A s.1 d v ∧ v ∉ s.2 then
    let leaving := (outgoing G tail A v).filter fun e => G.head tail e ∉ C
    if h : leaving.Nonempty then
      let e := leaving.min' h
      (insert e s.1, s.2 ∪ C ∪ component G s.1 (G.head tail e))
    else if h : (outgoing G tail A v).Nonempty then
      (insert ((outgoing G tail A v).min' h) s.1, s.2)
    else s
  else s

def extractPhase (A : Finset (Fin G.m)) (d : ℕ)
    (S : Finset (Fin G.m)) : Finset (Fin G.m) :=
  ((List.ofFn (fun v : Fin G.n => v)).foldl (extractVisit G tail A d) (S, ∅)).1

def ExtractResult (A : Finset (Fin G.m)) (d : ℕ)
    (S : Finset (Fin G.m)) : Prop :=
  ∃ p : ℕ, (extractPhase G tail A d)^[p] ∅ = S ∧
    ∀ v, ¬ needsChoice G tail A S d v

/-- Compact selected-edge list; no m-word bitmap is output by Algorithm 2. -/
def selectedOutput (S : Finset (Fin G.m)) : List ℤ :=
  (S.card : ℤ) :: (S.sort (· ≤ ·)).map (fun e => (e.val : ℤ))

/-- Header, (degree,offset) directory, then (edge identity,head) adjacency entries.
The input represents exactly the given orientation and keeps isolated vertices.
Offsets are relative to the start of the adjacency payload. -/
def adjacencyInput (d : ℕ) : List ℤ :=
  let entries := fun v => (outgoing G tail Finset.univ v).sort (· ≤ ·)
  [(G.n : ℤ), (G.m : ℤ), (d : ℤ)] ++
    (List.ofFn (fun v : Fin G.n =>
      [((entries v).length : ℤ),
       (2 * ∑ u ∈ Finset.univ.filter (fun u : Fin G.n => u < v), (entries u).length : ℤ)])).flatten ++
    (List.ofFn (fun v : Fin G.n => (entries v).flatMap fun e =>
      [(e.val : ℤ), ((G.head tail e).val : ℤ)])).flatten

/-- Descending rounds with deletion, so an edge cannot be selected twice. -/
def FirstStage (k : ℕ) (c : Fin G.m → Fin k) : Prop :=
  ∀ j : Fin k, ExtractResult G tail
    (Finset.univ.filter fun e => j.val ≤ (c e).val) (k - j.val)
    (Finset.univ.filter fun e => c e = j)

end
end ConstructiveArboricity.Exact.Supplement


