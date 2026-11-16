-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Supplement_Model
-- name    : NearLinearRSP_TwoResources_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:18:28.310659+00:00
-- url     : https://prove2.me/theorems/312d8e59-5672-4e8c-ab4f-840e5c2bcf85
-- title:
--   Multi-resource instances, feasible paths and objective aspect ratio
-- statement:
--   Fix a resource count $k$. A multi-resource instance consists of the published finite directed graph $G=(V,E)$, source $s\in V$, one nonnegative real objective length $\ell$, and nonnegative real edge costs $c_j$ and budgets $C_j$ for $j=0,\ldots,k-2$. Paths are nonempty vertex lists with an edge between each consecutive pair; repeated edge occurrences are counted. Exact feasibility and the extended optimum are
--   $$
--   \operatorname{Feasible}(t,P)\iff P:s\leadsto t\ \land\ \forall j,\ c_j(P)\le C_j,\qquad
--   \operatorname{OPT}(t)=\inf_{P:\operatorname{Feasible}(t,P)}\ell(P).
--   $$
--   The optimum takes values in $[0,\infty]$, and an empty feasible family has optimum $\infty$. Relaxed paths obey every $c_j(P)\le(1+\varepsilon)C_j$. The graph object, path predicate, multiplicity-aware path sum and positive-length aspect ratio are reused unchanged. A dummy zero-cost projection is used only to call the published length helpers, never to replace the separate constraints.
--
--   Coordinate zero is the objective, and coordinate $j+1$ is $c_j$. Edges spending a zero-budget resource are filtered out, as are self-loops. Positive-budget clocks are retained and zero-budget clocks omitted. Incident vertices and the source have records; isolated targets have implicit defaults. The objective aspect ratio $W$ ignores zero lengths and is one if no positive length exists. These objects supply the common domain and comparator contract for Theorem 2.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.1–4, Definition 1.1, graph/path conventions and Theorem 2; Appendix B p.14

import Definitions.Def_NearLinearRSP_TwoResources_Instance

set_option autoImplicit false
open scoped NNReal ENNReal

namespace NearLinearRSP.TwoResources.Supplement

/-- One objective and k-1 separately budgeted nonnegative real resources. -/
structure MultiInstance (k : ℕ) where
  graph : Digraph
  source : ℕ
  source_valid : source < graph.n
  length : ℕ → ℕ → ℝ≥0
  cost : Fin (k - 1) → ℕ → ℕ → ℝ≥0
  budget : Fin (k - 1) → ℝ≥0

/-- Projection used ONLY for the published graph/length helpers. -/
def lengthInstance {k : ℕ} (I : MultiInstance k) : Instance :=
  ⟨I.graph, I.source, I.source_valid, I.length, fun _ _ => 0, 0⟩

def ExactFeasible {k : ℕ} (I : MultiInstance k) (t : ℕ) (P : List ℕ) : Prop :=
  IsPath I.graph I.source t P ∧ ∀ r, pathWeight (I.cost r) P ≤ I.budget r

noncomputable def multiOptimum {k : ℕ} (I : MultiInstance k) (t : ℕ) : ℝ≥0∞ :=
  ⨅ (P : List ℕ) (_ : ExactFeasible I t P), ENNReal.ofReal (pathWeight I.length P)

def RelaxedPath {k : ℕ} (I : MultiInstance k) (ε : ℝ) (t : ℕ) (P : List ℕ) : Prop :=
  IsPath I.graph I.source t P ∧
    ∀ r, pathWeight (I.cost r) P ≤ (1 + ε) * I.budget r

/-- Zero budgets filter edges; deleting self loops preserves feasible optima. -/
noncomputable def usableEdges {k : ℕ} (I : MultiInstance k) : List (ℕ × ℕ) := by
  classical
  exact I.graph.edges.filter (fun e => e.1 ≠ e.2 ∧
    ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0)

def incidentVertices {k : ℕ} (I : MultiInstance k) : List ℕ :=
  (I.source :: I.graph.edges.flatMap (fun e => [e.1, e.2])).eraseDups

noncomputable def hasPositiveBudget {k : ℕ} (I : MultiInstance k) : Bool := by
  classical
  exact decide (∃ r, 0 < I.budget r)

/-- Coordinate 0 is the objective; coordinate r+1 is constrained cost r. -/
def coordinateWeight {k : ℕ} (I : MultiInstance k) (r : Fin k) : ℕ → ℕ → ℝ≥0 :=
  if h : r.val = 0 then I.length else I.cost ⟨r.val - 1, by omega⟩

def coordinateBudget {k : ℕ} (I : MultiInstance k) (L : ℝ) (r : Fin k) : ℝ :=
  if h : r.val = 0 then L else I.budget ⟨r.val - 1, by omega⟩

/-- Dormant zero-budget coordinates are omitted, not divided by zero. -/
noncomputable def clockCoordinates {k : ℕ} (I : MultiInstance k) : List (Fin k) :=
  (List.finRange k).filter (fun r => r.val = 0 ∨ 0 < coordinateBudget I 1 r)

noncomputable def multiScale {k : ℕ} (I : MultiInstance k) (ε : ℝ) : ℝ :=
  (max 1 I.graph.edges.length : ℕ) *
    (1 + Real.log (max 2 I.graph.n : ℕ)) *
    (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I))) /
    ε ^ (4 * k + 1)

/-- Stable first minimizer; no optimality or running-time certificate is assumed. -/
noncomputable def selectMin {α : Type} (f : α → ℝ) (xs : List α) (fallback : α) : α :=
  xs.foldl (fun x y => if f y < f x then y else x) (xs.headD fallback)

end NearLinearRSP.TwoResources.Supplement


