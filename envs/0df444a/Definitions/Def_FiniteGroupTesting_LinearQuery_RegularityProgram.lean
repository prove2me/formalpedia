-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_RegularityProgram
-- name    : FiniteGroupTesting_LinearQuery_RegularityProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:36.051224+00:00
-- url     : https://prove2.me/theorems/510bead2-1f43-49b1-bcde-405197237fc8
-- title:
--   Orbit-tree randomized regularity test
-- statement:
--   Compute inverse generator tables and their symmetric union. Breadth-first exploration from $e$ records one parent and edge generator for every discovered point. Reject unless the orbit is the entire specified set. In a trial choose a uniform $y$, compute all $v_y(x)=p_x(y)$ in tree order, and check
--
--   $$\gamma(v_y(x))=v_y(\gamma(x))\quad\text{for every }x,\gamma.$$
--
--   Independent trials must all pass. A real failure input $\delta$ is converted to $\lceil1/\delta\rceil$; charged integer doubling computes $r=\lceil\log_2\lceil1/\delta\rceil\rceil$. Empty generators are handled directly: accept exactly on a singleton. There are no original-table queries, no enumeration of the generated group, and no regularity assumption in the code. Tree composition is $p_z=\gamma p_x$.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 20–22, §3.2, Theorem 3.8 algorithm

import Definitions.Def_FiniteGroupTesting_LinearQuery_ExploreExtension

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Compute ceil(log_2 target) by charged doubling on finite words. -/
def logLoop {n : ℕ} (target : ℕ) : ℕ → ℕ → ℕ → OracleRun n ℕ
  | 0, _, r => pure r
  | fuel + 1, power, r => do
      charge 5
      if target ≤ power then return r
      logLoop target fuel (2 * power) (r + 1)

def ceilLogProgram {n : ℕ} (target : ℕ) : OracleRun n ℕ :=
  logLoop target (target + 1) 1 0

def inverseRow {n : ℕ} (a : StoredAction n) (i : ℕ) :
    ℕ → (Fin n → Fin n) → OracleRun n (Fin n → Fin n)
  | 0, inv => pure inv
  | j + 1, inv => do
      charge 8
      let x := a.domain.labels (a.domain.count - (j + 1))
      inverseRow a i j (Function.update inv (a.image i x) x)

def symmetricRows {n : ℕ} (a : StoredAction n) :
    ℕ → (ℕ → Fin n → Fin n) → OracleRun n (ℕ → Fin n → Fin n)
  | 0, rows => pure rows
  | j + 1, rows => do
      charge 8
      let i := a.degree - (j + 1)
      let inv ← inverseRow a i a.domain.count id
      symmetricRows a j (Function.update (Function.update rows i (a.image i)) (a.degree + i) inv)

structure OrbitTree (n : ℕ) where
  points : LabelSet n
  parent : Fin n → Fin n
  edge : Fin n → ℕ
  head : ℕ

def orbitEdges {n : ℕ} (a : StoredAction n) (x : Fin n) :
    ℕ → OrbitTree n → OracleRun n (OrbitTree n)
  | 0, t => pure t
  | j + 1, t => do
      charge 12
      let i := a.degree - (j + 1)
      let z := a.image i x
      let t := if a.domain.marked z && !t.points.marked z then
        { t with points := t.points.insert z, parent := Function.update t.parent z x, edge := Function.update t.edge z i } else t
      orbitEdges a x j t

def orbitLoop {n : ℕ} (a : StoredAction n) :
    ℕ → OrbitTree n → OracleRun n (OrbitTree n)
  | 0, t => pure t
  | fuel + 1, t => do
      charge 6
      if t.head ≥ t.points.count then return t
      let x := t.points.labels t.head
      let t ← orbitEdges a x a.degree { t with head := t.head + 1 }
      orbitLoop a fuel t

/-- Generator multiplication is left composition on tree edges: p_z = gamma p_x. -/
def buildOrbitTree {n : ℕ} (a : StoredAction n) (e : Fin n) : OracleRun n (OrbitTree n) := do
  charge (6 * a.domain.count + 6)
  orbitLoop a a.domain.count ⟨(LabelSet.empty e).insert e, fun _ => e, fun _ => 0, 0⟩

/-- All p_x(y) in discovery order, one traversal of the stored orbit tree. -/
def treeColumnLoop {n : ℕ} (a : StoredAction n) (t : OrbitTree n) :
    ℕ → (Fin n → Fin n) → OracleRun n (Fin n → Fin n)
  | 0, col => pure col
  | j + 1, col => do
      charge 8
      let pos := t.points.count - (j + 1)
      let x := t.points.labels pos
      let col := if pos == 0 then col else
        Function.update col x (a.image (t.edge x) (col (t.parent x)))
      treeColumnLoop a t j col

def treeColumn {n : ℕ} (a : StoredAction n) (_e y : Fin n)
    (t : OrbitTree n) : OracleRun n (Fin n → Fin n) :=
  treeColumnLoop a t t.points.count (fun _ => y)

def equivarianceEdges {n : ℕ} (a : StoredAction n) (v : Fin n → Fin n) (x : Fin n) :
    ℕ → OracleRun n Bool
  | 0 => pure true
  | j + 1 => do
      charge 10
      let i := a.degree - (j + 1)
      if a.image i (v x) != v (a.image i x) then return false
      equivarianceEdges a v x j

def equivariancePoints {n : ℕ} (a : StoredAction n) (v : Fin n → Fin n) :
    ℕ → OracleRun n Bool
  | 0 => pure true
  | j + 1 => do
      charge 5
      let good ← equivarianceEdges a v (a.domain.labels (a.domain.count - (j + 1))) a.degree
      if !good then return false
      equivariancePoints a v j

def regularityTrials {n : ℕ} (a : StoredAction n) (e : Fin n) (t : OrbitTree n) :
    ℕ → OracleRun n Bool
  | 0 => pure true
  | r + 1 => do
      charge 5
      if a.domain.count == 0 then return false
      let i ← draw (a.domain.count - 1)
      let v ← treeColumn a e (a.domain.labels i.val) t
      let good ← equivariancePoints a v a.domain.count
      if !good then return false
      regularityTrials a e t r

/-- The actual test: explicit inverse tables, orbit/BFS, then independent equivariance trials.
An empty generator family is handled by the orbit check, including the singleton case. -/
def regularityProgram {n : ℕ} (a : StoredAction n) (e : Fin n) (r : ℕ) : OracleRun n Bool := do
  charge 4
  if a.degree == 0 then return a.domain.count == 1
  let rows ← symmetricRows a a.degree (fun _ => id)
  let sym := { a with degree := 2 * a.degree, image := rows }
  let t ← buildOrbitTree sym e
  charge 5
  if t.points.count != a.domain.count then return false
  regularityTrials sym e t r

/-- The real failure input is converted to ceil(1/delta), then repetitions are computed
by charged integer doubling; a base-2 ceiling guarantees 2^(-r) <= delta. -/
noncomputable def regularityTest {n : ℕ} (a : StoredAction n) (e : Fin n)
    (δ : ℝ) : OracleRun n Bool := .step 1 (do
  let r ← ceilLogProgram ⌈1 / δ⌉₊
  regularityProgram a e r)

end FiniteGroupTesting.LinearQuery


