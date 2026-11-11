-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_FastEvaluation
-- name    : FiniteGroupTesting_LinearQuery_FastEvaluation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:10.246873+00:00
-- url     : https://prove2.me/theorems/97c2424f-9764-4167-815a-7bb81d5281bd
-- title:
--   Query-free preprocessing and short-word multiplication
-- statement:
--   For fixed positive implementation integers $A,B$, sample $A\lceil\log_2n\rceil$ uniform labels. Compute each syntactic column $T_s(x)=p_x(s)$ by a charged orbit-tree traversal. Scan it for a unique $r$ with $T_s(r)=e$, then compute $T_r$; fail if uniqueness does not hold. Breadth-first search on these stored column edges must reach every label within $B\lceil\log_2n\rceil$ steps.
--
--   $$\operatorname{Eval}(x,y)=T_{s_\ell}(\cdots T_{s_1}(x)\cdots),\qquad \operatorname{Eval}(x,e)=x.$$
--
--   Parents and column indices represent the stored short words; evaluation follows parents recursively and applies columns outward from the root. This avoids copying complete words on every discovery. The same deterministic final orbit tree can be recomputed on each of the three attempts. No original-table query occurs. Regularity is not required to define failure or evaluation on arbitrary executions.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 23, §3.4 and equation (3.4.1)

import Definitions.Def_FiniteGroupTesting_LinearQuery_Reconstruction

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Scan a stored column for its unique inverse label; no original-table query. -/
def inverseLabel {n : ℕ} (e : Fin n) (col : Fin n → Fin n) :
    ℕ → ℕ → Fin n → OracleRun n (ℕ × Fin n)
  | 0, count, candidate => pure (count, candidate)
  | j + 1, count, candidate => do
      charge 7
      let x := labelAt e (n - (j + 1))
      if col x == e then inverseLabel e col j (count + 1) x
      else inverseLabel e col j count candidate

/-- k iid uniform labels; both the syntactic column and its inverse-label column are stored. -/
def sampleColumns {n : ℕ} (a : StoredAction n) (e : Fin n) (tree : OrbitTree n)
    (k : ℕ) : ℕ → (ℕ → Fin n → Fin n) → OracleRun n (Option (ℕ → Fin n → Fin n))
  | 0, cols => pure (some cols)
  | j + 1, cols => do
      charge 8
      let sampled ← draw (n - 1)
      let s := labelAt e sampled.val
      let col ← treeColumn a e s tree
      let (count, r) ← inverseLabel e col n 0 e
      if count != 1 then return none
      let inv ← treeColumn a e r tree
      let i := k - (j + 1)
      sampleColumns a e tree k j (Function.update (Function.update cols (2 * i) col) (2 * i + 1) inv)

structure WordTree (n : ℕ) where
  orbit : OrbitTree n
  depth : Fin n → ℕ

/-- Breadth-first search restricted to the prescribed word length, including on bad actions. -/
def wordEdges {n : ℕ} (graph : StoredAction n) (x : Fin n) :
    ℕ → WordTree n → OracleRun n (WordTree n)
  | 0, w => pure w
  | j + 1, w => do
      charge 15
      let i := graph.degree - (j + 1)
      let z := graph.image i x
      let w := if !w.orbit.points.marked z then
        ⟨{ w.orbit with points := w.orbit.points.insert z, parent := Function.update w.orbit.parent z x, edge := Function.update w.orbit.edge z i }, Function.update w.depth z (w.depth x + 1)⟩
        else w
      wordEdges graph x j w

def wordLoop {n : ℕ} (graph : StoredAction n) (maxDepth : ℕ) :
    ℕ → WordTree n → OracleRun n (WordTree n)
  | 0, w => pure w
  | fuel + 1, w => do
      charge 8
      if w.orbit.head ≥ w.orbit.points.count then return w
      let x := w.orbit.points.labels w.orbit.head
      let w := { w with orbit := { w.orbit with head := w.orbit.head + 1 } }
      let w ← if w.depth x < maxDepth then wordEdges graph x graph.degree w else pure w
      wordLoop graph maxDepth fuel w

structure FastEvaluator (n : ℕ) where
  identity : Fin n
  columns : ℕ → Fin n → Fin n
  words : WordTree n
  maxDepth : ℕ

/-- The fixed A,B are implementation constants, chosen before n and the input table. -/
def preprocessing {n : ℕ} (A B : ℕ) (a : StoredAction n) (e : Fin n) :
    OracleRun n (Option (FastEvaluator n)) := do
  let L ← ceilLogProgram n
  let rows ← symmetricRows a a.degree (fun _ => id)
  let sym := { a with degree := 2 * a.degree, image := rows }
  let tree ← buildOrbitTree sym e
  let cols ← sampleColumns sym e tree (A * L) (A * L) (fun _ => id)
  match cols with
  | none => return none
  | some cols =>
      charge (8 * n + 12)
      let graph := { a with degree := 2 * A * L, image := cols }
      let w ← wordLoop graph (B * L) n
        ⟨⟨(LabelSet.empty e).insert e, fun _ => e, fun _ => 0, 0⟩, fun _ => 0⟩
      if w.orbit.points.count != n then return none
      return some ⟨e, cols, w, B * L⟩

/-- Follow the stored word from its root outward; the stack has at most maxDepth entries. -/
def evaluateWord {n : ℕ} (ev : FastEvaluator n) (x : Fin n) :
    ℕ → Fin n → OracleRun n (Fin n)
  | 0, _ => pure x
  | fuel + 1, y => do
      charge 8
      if y == ev.identity then return x
      let z ← evaluateWord ev x fuel (ev.words.orbit.parent y)
      return ev.columns (ev.words.orbit.edge y) z

def evaluate {n : ℕ} (ev : FastEvaluator n) (x y : Fin n) : OracleRun n (Fin n) :=
  evaluateWord ev x ev.maxDepth y

end FiniteGroupTesting.LinearQuery


