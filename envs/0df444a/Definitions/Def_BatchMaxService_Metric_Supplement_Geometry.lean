-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_Geometry
-- name    : BatchMaxService_Metric_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:00:52.810743+00:00
-- url     : https://prove2.me/theorems/71aca1d3-9968-49db-b9f0-c9b32912c96a
-- title:
--   Ordered finite lines, represented tree paths and exact Steiner oracles
-- statement:
--   A finite line is enumerated in increasing real coordinate order and carries absolute distance. Every turning-point segment is expanded to all sites between its endpoints. The minimum spacing is the finite minimum over distinct sites, with zero used only when there are fewer than two sites.
--
--   $$d(u,v)=|x(u)-x(v)|,\qquad T[A]=\bigcup_{v\in A}\operatorname{path}_T(s,v).$$
--
--   The published metric-tree representation is reused. Parent scans construct paths and the anchored minimal subtree; a weighted-tree instance requires the given metric to equal its path lengths. Its edges have strictly positive lengths. A one-vertex tree is included. A farthest endpoint is selected from actual request identities in the returned tree, with fixed ties. An exact Steiner oracle is a deterministic function returning an actual minimum-weight tree spanning any nonempty terminal set, allowing other sites as Steiner vertices; efficiency is not required. These utilities support Algorithms 1–3 and 5–6.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Sections 3.3, 5.1–5.3 and 6, printed pp. 6, 13–17, 20 / PDF pp. 7, 14–18, 21

import Mathlib
import Definitions.Def_BatchMaxService_Metric_RequestInput
import Definitions.Def_BatchMaxService_Metric_PrimTraversal

namespace BatchMaxService.Metric.Supplement

variable {n : ℕ}

/-- Enumeration of a known finite ordered subset of R, with its actual metric. -/
def IsLine [MetricSpace (Fin n)] (x : Fin n → ℝ) : Prop :=
  StrictMono x ∧ ∀ u v, dist u v = |x u - x v|

noncomputable def lineSegment (x : Fin n → ℝ) (u v : Fin n) : List (Fin n) := by
  classical
  let xs := (List.finRange n).filter fun z => min (x u) (x v) ≤ x z ∧ x z ≤ max (x u) (x v)
  exact if x u ≤ x v then xs else xs.reverse

/-- Turning points expanded to every site traversed, preserving forced hits. -/
noncomputable def lineWalk (x : Fin n → ℝ) : List (Fin n) → List (Fin n)
  | [] => []
  | [u] => [u]
  | u :: v :: rest => lineSegment x u v ++ (lineWalk x (v :: rest)).tail

noncomputable def extremes (x : Fin n → ℝ) (s : Fin n) (A : Finset (Fin n)) : Fin n × Fin n := by
  classical
  exact match (A.sort (· ≤ ·)).head? with
  | none => (s, s)
  | some u => (A.toList.foldl (fun a b => if x b < x a then b else a) u,
              A.toList.foldl (fun a b => if x a < x b then b else a) u)

/-- Right endpoint wins a tie, as in Algorithms 5 and 6. -/
noncomputable def farLine (x : Fin n → ℝ) (s : Fin n) (A : Finset (Fin n)) : Fin n :=
  let lr := extremes x s A
  if |x s - x lr.1| ≤ |x s - x lr.2| then lr.2 else lr.1

noncomputable def cleanupWalk (x : Fin n → ℝ) (s : Fin n) (A : Finset (Fin n)) : List (Fin n) :=
  let lr := extremes x s A
  if |x s - x lr.1| ≤ |x s - x lr.2| then lineWalk x [s, lr.1, lr.2]
  else lineWalk x [s, lr.2, lr.1]

/-- Finite minimum spacing, with value zero only for fewer than two sites.
    No logarithm, natural division or rounding of real distances is used. -/
noncomputable def spacing (x : Fin n → ℝ) : ℝ := by
  classical
  let ds := ((sitePairs n).filter fun uv => uv.1 ≠ uv.2).map fun uv => |x uv.1 - x uv.2|
  exact match ds with
  | [] => 0
  | d :: rest => rest.foldl min d

noncomputable def sweepWalk (x : Fin n → ℝ) (s : Fin n) (r : ℝ) : List (Fin n) := by
  classical
  let A := Finset.univ.filter fun v => |x v - x s| ≤ r
  let lr := extremes x s A
  exact lineWalk x [s, lr.1, lr.2, s]

/-- Parent pointers of an actual represented tree, not a supplied distance oracle. -/
def backPath (p : Parents n) : ℕ → Fin n → List (Fin n)
  | 0, v => [v]
  | k + 1, v => v :: (match p v with | none => [] | some u => backPath p k u)

noncomputable def treePath (F : MetricTree n) (u v : Fin n) : List (Fin n) :=
  (backPath (rootLoop F n {u} (fun _ => none)).1 n v).reverse

/-- A positive-weight vertex tree represented in its path metric. Since every edge
    has distinct endpoints, strict positivity follows from the metric axioms. -/
noncomputable def IsWeightedTree [MetricSpace (Fin n)] (T : MetricTree n) : Prop :=
  IsTree T ∧ T.vertices = Finset.univ ∧
    ∀ u v, dist u v = walkLength (treePath T u v)

noncomputable def pathEdges (w : List (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact (w.zip w.tail).toFinset.image fun uv => s(uv.1, uv.2)

/-- The union of paths from the anchor to all terminals. Construction uses the
    represented tree; the counter charges rooting, parent scans and finite unions. -/
noncomputable def minimalSubtree (T : MetricTree n) (s : Fin n)
    (A : Finset (Fin n)) : Charged (MetricTree n) := by
  classical
  let rooted := rootLoop T n {s} (fun _ => none)
  let paths := A.toList.map fun v => (backPath rooted.1 n v).reverse
  let vertices := insert s (paths.foldl (fun V w => V ∪ w.toFinset) ∅)
  let edges := paths.foldl (fun E w => E ∪ pathEdges w) ∅
  exact (⟨vertices, edges⟩, rooted.2 + 100 * (n + 1)^5 * (T.edges.card + 1))

noncomputable def pathDistance [MetricSpace (Fin n)] (F : MetricTree n) (u v : Fin n) : ℝ :=
  walkLength (treePath F u v)

/-- Select an actual request farthest in the returned tree. Least label wins ties. -/
noncomputable def farthestRequest [MetricSpace (Fin n)] (F : MetricTree n) (s : Fin n)
    (known : ℕ → Fin n) (P : Finset ℕ) : Option ℕ := by
  classical
  exact (P.sort (· ≤ ·)).foldl (fun best q => match best with
    | none => some q
    | some b => if pathDistance F s (known b) < pathDistance F s (known q)
        then some q else some b) none

/-- Exactness alone, not efficiency or a terminal-only constraint. -/
noncomputable def ExactSteinerOracle [MetricSpace (Fin n)]
    (oracle : Finset (Fin n) → MetricTree n) : Prop :=
  ∀ A, A.Nonempty → IsTree (oracle A) ∧ A ⊆ (oracle A).vertices ∧
    ENNReal.ofReal (treeWeight (oracle A)) = SteinerCost A

end BatchMaxService.Metric.Supplement


