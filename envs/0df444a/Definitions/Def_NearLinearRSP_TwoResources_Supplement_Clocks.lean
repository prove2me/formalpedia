-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Supplement_Clocks
-- name    : NearLinearRSP_TwoResources_Supplement_Clocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:13.2742+00:00
-- url     : https://prove2.me/theorems/5bd7544d-d060-44d7-9102-ef987a508316
-- title:
--   Product-Poisson clocks and the computed multidimensional queue tables
-- statement:
--   A clock call has an instance $I$, internal accuracy $\delta$, objective threshold $L$, and a flag selecting the zero-length subgraph. For calls used by Theorem 2, $\delta=\varepsilon/4$ and $L>0$. Let $d\le k$ be the number of retained coordinates (the objective and the positive-budget costs). Put
--   $$
--   q=\left\lceil\frac{512k}{\delta^2}\right\rceil,\qquad
--   \lambda_r=\frac{q}{(1+\delta/2)B_r},\qquad
--   p_{uv}(a)=\prod_{r=0}^{d-1}e^{-\lambda_rw_r(uv)}\frac{(\lambda_rw_r(uv))^{a_r}}{a_r!}.
--   $$
--   Here $B_0=L$ and the other thresholds are the retained budgets; $w_r$ is the corresponding edge resource. The product is the joint mass of independent Poisson increments, newly exposed on each traversal, including repeated traversals. A zero mean has unit mass at zero and zero mass elsewhere.
--
--   The table is indexed by a vertex and a genuine $d$-coordinate tick vector. Any coordinate at least $q$ has value one, including at the source; an unsaturated source has value zero. Layers are processed in decreasing lexicographic order. Each nonsource initial key is the minimum of its next-coordinate tick values. Queue extraction has fixed first-minimum ties and an extraction rank. An edge relaxation uses the sum over the whole finite admissible increment rectangle and its complementary overflow mass, updating only on strict improvement. Each cell stores its value, a tick-coordinate or predecessor label, and rank. A target is accepted when its zero-vector value is at most $1/4$.
--
--   These are computed values, with no correctness or time guarantee assumed. List folds specify the deterministic choices; the companion theorem requires a charged efficient heap and adjacency implementation producing the same snapshot.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.6–9, Section 4, Section 5 and Observation A.1 p.14, extended to k clocks by Appendix B p.14

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_Model
import Definitions.Def_actuarial_poissonCountMass

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement

structure ClockCall (k : ℕ) where
  I : MultiInstance k
  δ : ℝ
  L : ℝ
  zeroOnly : Bool

noncomputable def ticks (k : ℕ) (δ : ℝ) : ℕ := Nat.ceil (512 * (k : ℝ) / δ ^ 2)
noncomputable def ClockCall.q {k : ℕ} (A : ClockCall k) : ℕ := ticks k A.δ
noncomputable def ClockCall.coords {k : ℕ} (A : ClockCall k) := clockCoordinates A.I
noncomputable def ClockCall.d {k : ℕ} (A : ClockCall k) : ℕ := A.coords.length

noncomputable def callEdges {k : ℕ} (A : ClockCall k) : List (ℕ × ℕ) :=
  (usableEdges A.I).filter (fun e => !A.zeroOnly || A.I.length e.1 e.2 = 0)

noncomputable def clockRate {k : ℕ} (A : ClockCall k) (r : Fin A.d) : ℝ :=
  (A.q : ℝ) / ((1 + A.δ / 2) * coordinateBudget A.I A.L (A.coords.get r))

noncomputable def clockMean {k : ℕ} (A : ClockCall k) (r : Fin A.d) (u v : ℕ) : ℝ :=
  clockRate A r * coordinateWeight A.I (A.coords.get r) u v

/-- The product law describes fresh independent increments at EACH traversal. -/
noncomputable def incrementMass {k : ℕ} (A : ClockCall k) (u v : ℕ)
    (a : Fin A.d → ℕ) : ℝ :=
  ∏ r, ActuarialValuation.poissonCountMass (clockMean A r u v) (a r)

/-- Lexicographically increasing enumeration, first coordinate most significant. -/
def vectors : (d q : ℕ) → List (Fin d → ℕ)
  | 0, _ => [fun r => Fin.elim0 r]
  | d + 1, q => (List.range q).flatMap (fun a => (vectors d q).map (Fin.cons a))

noncomputable def rectangle {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) :=
  (vectors A.d A.q).filter (fun a => ∀ r, i r + a r < A.q)

inductive MultiParent where
  | none
  | tick (coordinate : ℕ)
  | edge (vertex : ℕ)
  deriving DecidableEq

structure MultiCell where
  value : ℝ
  parent : MultiParent
  rank : ℕ

abbrev MultiTable (d : ℕ) := ℕ → (Fin d → ℕ) → MultiCell

noncomputable def put {d : ℕ} (T : MultiTable d) (v : ℕ) (i : Fin d → ℕ)
    (c : MultiCell) : MultiTable d := by
  classical
  exact fun w j => if w = v ∧ j = i then c else T w j

/-- Saturation precedes the source boundary, including at the source itself. -/
noncomputable def value {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) : ℝ :=
  if ∃ r, A.q ≤ i r then 1 else (T v i).value

noncomputable def expectation {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ) : ℝ :=
  let xs := rectangle A i
  1 - (xs.map (incrementMass A u v)).sum +
    (xs.map (fun a => incrementMass A u v a * value A T u (fun r => i r + a r))).sum

structure MultiLayer (d : ℕ) where
  table : MultiTable d
  keys : ℕ → ℝ
  parents : ℕ → MultiParent
  queue : List ℕ
  nextRank : ℕ

noncomputable def nextTick {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) : Option (Fin A.d) :=
  let rs := List.finRange A.d
  match rs with
  | [] => none
  | r :: _ => some (selectMin (fun s => value A T v (Function.update i s (i s + 1))) rs r)

noncomputable def initializeLayer {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : MultiLayer A.d where
  table := T
  keys v := if v = A.I.source then 0 else
    match nextTick A T v i with
    | none => 1
    | some r => value A T v (Function.update i r (i r + 1))
  parents v := if v = A.I.source then .none else
    match nextTick A T v i with
    | none => .none
    | some r => .tick r.val
  queue := incidentVertices A.I
  nextRank := 0

noncomputable def relax {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : MultiLayer A.d :=
  if e.1 = u ∧ e.2 ∈ S.queue then
    let b := expectation A S.table u e.2 i
    if b < S.keys e.2 then
      { S with
        keys := Function.update S.keys e.2 b
        parents := Function.update S.parents e.2 (.edge u) }
    else S
  else S

noncomputable def pop {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : MultiLayer A.d :=
  match S.queue with
  | [] => S
  | v :: _ =>
    let u := selectMin S.keys S.queue v
    let S' := { S with
      table := put S.table u i ⟨S.keys u, S.parents u, S.nextRank⟩
      queue := S.queue.erase u
      nextRank := S.nextRank + 1 }
    (callEdges A).foldl (relax A i u) S'

noncomputable def constructLayer {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : MultiTable A.d :=
  ((List.range (incidentVertices A.I).length).foldl
    (fun S _ => pop A i S) (initializeLayer A T i)).table

/-- A definition of the computed table, not a predicate asserting its success.
The RAM theorem requires an efficient heap/adjacency implementation of these values. -/
noncomputable def constructTable {k : ℕ} (A : ClockCall k) : MultiTable A.d :=
  (vectors A.d A.q).reverse.foldl (constructLayer A) (fun _ _ => ⟨1, .none, 0⟩)

noncomputable def accepts {k : ℕ} (A : ClockCall k) (t : ℕ) : Bool :=
  decide (value A (constructTable A) t (fun _ => 0) ≤ 1 / 4)

end NearLinearRSP.TwoResources.Supplement


