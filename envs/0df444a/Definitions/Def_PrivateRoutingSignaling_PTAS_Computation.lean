-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Computation
-- name    : PrivateRoutingSignaling_PTAS_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:49.846456+00:00
-- url     : https://prove2.me/theorems/3b39e5f9-a6bc-4e07-a793-3f41acf8c1e5
-- title:
--   Binary execution, full grid LP construction, and sparse rational output
-- statement:
--   Finite latency descriptions are represented by finite binary-tape evaluator programs. Each evaluates rational loads exactly, with rational outputs. A monotone polynomial evaluation envelope $E(m)$ bounds their actual transitions at description-plus-query length $m$; its polynomial degree may depend on the evaluators. The prior is rational. These are the numerical conventions of the source, independent of the general real-flow benchmark.
--
--   The input encodes the graph, terminals, states, rational prior, evaluator transition tables, a rational Lipschitz bound, and positive rational tolerance $\delta$. No path enumeration is supplied. The construction enumerates all simple paths and all ordered $k$-tuples of paths, counts path occurrences, and removes duplicate grid points, with
--
--   $$k=\max\{1,\lceil4d^2L/\delta\rceil\},$$
--
--   where the goal takes $d$ to be the graph's maximum simple-path length, computed from the graph rather than read from the input.
--
--   The full rational LP is the paper's $(P_\epsilon)$: minimize expected flow cost on the grid, impose both directions of each prior equality, nonnegativity, and the weighted $\delta$-relaxed obedience rows. Redundant diagonal obedience rows cause no restriction at positive tolerance. Its carrier is the published general rational LP.
--
--   A pipeline has three finite program tables, with no correctness or speed fields. Its execution constructs the encoded LP, runs the LP stage to a dense rational vector, and formats a sparse scheme listing states, positive-traffic paths as actual arc lists, and positive joint probabilities. Every stage is executed using the published bit-machine transition semantics; intermediate handoffs also charge the strings' lengths. Rational arithmetic, evaluator interpretation, enumeration, optimization and output must all be carried out by those transitions.
--
--   The solution specification requires optimality against all real feasible LP points and basicness as a feasible vertex. Output weights induce a finite joint Borel measure. The time expression retains universal polynomial degrees, explicit evaluation cost, and $\max\{2,n\}^{\lceil C(d+d^3L/\varepsilon)\rceil}$. It is a budget for executed work, not an invented runtime attached to an output function. The LP solver's correctness and bit complexity remain theorem obligations.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #439 (October 2026), §2.3, p. 8 (PDF p. 8), computational conventions; §3.1, pp. 9–12 (PDF pp. 9–12), LP (P_ε) and Theorem 3.2 proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf

import Mathlib
import Definitions.Def_EditGV897_Main_Machine
import Definitions.Def_RobustToDynamics_LPInst
import Definitions.Def_PrivateRoutingSignaling_PTAS_Signaling

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace PrivateRoutingSignaling.PTAS

/-- Binary encodings are framed binary digits; dimensions are never unary numbers. -/
def natCode (n : ℕ) : List Bool := EditGV897.Main.frame (EditGV897.Main.binary n)
def ratCode (q : ℚ) : List Bool :=
  EditGV897.Main.integerCode q.num ++ natCode q.den

def listCode {α : Type} (enc : α → List Bool) (xs : List α) : List Bool :=
  natCode xs.length ++ xs.flatMap enc

def symbolCode : Option Bool → List Bool
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def motionCode : EditGV897.Main.Motion → List Bool
  | .left => [false, false]
  | .stay => [false, true]
  | .right => [true, false]

/-- The ternary digits enumerate all possible heads of a fixed finite number of tapes. -/
def heads (t j : ℕ) (i : Fin t) : Option Bool :=
  match (j / 3 ^ i.val) % 3 with
  | 0 => none
  | 1 => some false
  | _ => some true

/-- Entire finite transition table, not an unbounded mathematical callback. -/
def programCode (P : EditGV897.Main.Program) : List Bool :=
  natCode P.states ++ natCode P.workTapes ++
    (List.ofFn (fun q : Fin (P.states + 1) =>
      (List.ofFn (fun j : Fin (3 ^ (P.workTapes + 2)) =>
        match P.transition q (heads (P.workTapes + 2) j.val) with
        | none => [false]
        | some (q', a) => true :: (natCode q'.val ++
            (List.ofFn (fun i : Fin (P.workTapes + 2) =>
              symbolCode (a i).1 ++ motionCode (a i).2)).flatten))).flatten)).flatten

/-- Source finite descriptions, represented by arbitrary finite binary evaluator programs.
No polynomial degree is common to all input latency descriptions. -/
structure BinaryData (I : Instance) where
  prior : Fin I.states → ℚ
  prior_eq : ∀ θ, (prior θ : ℝ) = I.prior θ
  eval : Fin I.states → Fin I.network.arcs → ℚ → ℚ
  code : Fin I.states → Fin I.network.arcs → EditGV897.Main.Program

/-- A monotone polynomial evaluation envelope supplied by the computational convention.
Its degree may depend on the input evaluators. Output length is charged by Runs. -/
def Evaluates (I : Instance) (D : BinaryData I) (E : ℕ → ℕ) : Prop :=
  Monotone E ∧ (∃ a b : ℕ, ∀ m, E m ≤ a * (m + 1) ^ b) ∧
  ∀ θ i x, x ∈ Set.Icc (0 : ℚ) 1 →
    (D.eval θ i x : ℝ) = I.latency θ i (x : ℝ) ∧
    EditGV897.Main.Runs (D.code θ i) (ratCode x) (ratCode (D.eval θ i x))
      (E ((programCode (D.code θ i)).length + (ratCode x).length))

/-- Complete graph input and latency descriptions; no path list is part of the input.
The path-length bound `d` is not part of the input either: Theorem 1.1 defines `d` from the
graph, and only the Lipschitz bound `L` is "known". -/
def inputCode (I : Instance) (D : BinaryData I) (L ε : ℚ) : List Bool :=
  natCode I.network.vertices ++ natCode I.network.arcs ++
    natCode I.network.source.val ++ natCode I.network.sink.val ++
    (List.ofFn (fun i : Fin I.network.arcs =>
      natCode (I.network.graph.tail i).val ++ natCode (I.network.graph.head i).val)).flatten ++
    natCode I.states ++ (List.ofFn (fun θ : Fin I.states =>
      ratCode (D.prior θ) ++ (List.ofFn (fun i : Fin I.network.arcs =>
        EditGV897.Main.frame (programCode (D.code θ i)))).flatten)).flatten ++ ratCode L ++ ratCode ε

/-- The chosen grid denominator, with no division by L (including L=0 and d=0). -/
def gridSize (d : ℕ) (L ε : ℚ) : ℕ := max 1 ⌈4 * (d : ℚ) ^ 2 * L / ε⌉₊

abbrev GridColumn (I : Instance) (k : ℕ) := Fin I.states × Grid I.network k

/-- Exact rational coefficients, evaluated only at rational loads. -/
def qIncidence (N : RoutingNetwork) (i : Fin N.arcs) (p : Path N) : ℚ :=
  if i ∈ pathArcs N p then 1 else 0

def qGrid (N : RoutingNetwork) (k : ℕ) (a : Grid N k) (p : Path N) : ℚ :=
  ((a.val p).val : ℚ) / k

def qLoad (N : RoutingNetwork) (k : ℕ) (a : Grid N k) (i : Fin N.arcs) : ℚ :=
  ∑ p, qIncidence N i p * qGrid N k a p

def qPathCost (I : Instance) (D : BinaryData I) (k : ℕ) (z : GridColumn I k)
    (p : Path I.network) : ℚ :=
  ∑ i, D.eval z.1 i (qLoad I.network k z.2 i) * qIncidence I.network i p

def objectiveCoeff (I : Instance) (D : BinaryData I) (k : ℕ)
    (z : GridColumn I k) : ℚ :=
  ∑ p, qGrid I.network k z.2 p * qPathCost I D k z p

/-- All rows of P_ε, including both signs of each prior equality and nonnegativity. -/
inductive GridRow (I : Instance) (k : ℕ)
  | priorUpper : Fin I.states → GridRow I k
  | priorLower : Fin I.states → GridRow I k
  | nonnegative : GridColumn I k → GridRow I k
  | obedience : Path I.network → Path I.network → GridRow I k
  deriving Fintype, DecidableEq

def rowCoeff (I : Instance) (D : BinaryData I) (k : ℕ) (ε : ℚ) :
    GridRow I k → GridColumn I k → ℚ
  | .priorUpper θ, z => if z.1 = θ then 1 else 0
  | .priorLower θ, z => if z.1 = θ then -1 else 0
  | .nonnegative a, z => if z = a then -1 else 0
  | .obedience p q, z =>
      -(qGrid I.network k z.2 p * (qPathCost I D k z q + ε - qPathCost I D k z p))

def rowBound (I : Instance) (D : BinaryData I) (k : ℕ) : GridRow I k → ℚ
  | .priorUpper θ => D.prior θ
  | .priorLower θ => -D.prior θ
  | .nonnegative _ => 0
  | .obedience _ _ => 0

/-- Enumerate k ordered path choices, then count occurrences. Erasing duplicates
produces the entire uniform grid, in at most |P|^k iterations before polynomial overhead. -/
def pathSelections (N : RoutingNetwork) : ℕ → List (List (Path N))
  | 0 => [[]]
  | k + 1 => (List.finRange (pathList N).length).flatMap
      (fun p => (pathSelections N k).map (p :: ·))

def gridList (N : RoutingNetwork) (k : ℕ) : List (Grid N k) :=
  ((pathSelections N k).filterMap (fun ps =>
    let a : Path N → Fin (k + 1) := fun p => Fin.ofNat (k + 1) (ps.count p)
    if h : ∑ p, (a p).val = k then some ⟨a, h⟩ else none)).eraseDups

def columnList (I : Instance) (k : ℕ) : List (GridColumn I k) :=
  (List.finRange I.states).flatMap (fun θ => (gridList I.network k).map (θ, ·))

def rowList (I : Instance) (k : ℕ) : List (GridRow I k) :=
  (List.finRange I.states).map GridRow.priorUpper ++
    (List.finRange I.states).map GridRow.priorLower ++
    (columnList I k).map GridRow.nonnegative ++
    (List.finRange (pathList I.network).length).flatMap (fun p =>
      (List.finRange (pathList I.network).length).map (GridRow.obedience p))

/-- Executable construction of P_ε in the published general LP carrier.
Both the graph paths and grid columns are enumerated from input data.
The diagonal obedience rows are redundant for ε≥0. -/
def discretizedLP (I : Instance) (D : BinaryData I) (k : ℕ)
    (ε : ℚ) : RobustToDynamics.LPInst where
  p := (rowList I k).length
  q := (columnList I k).length
  A r c := rowCoeff I D k ε ((rowList I k).get r) ((columnList I k).get c)
  b r := rowBound I D k ((rowList I k).get r)
  c c := objectiveCoeff I D k ((columnList I k).get c)

def lpCode (L : RobustToDynamics.LPInst) : List Bool :=
  natCode L.p ++ natCode L.q ++
    (List.ofFn (fun r : Fin L.p =>
      (List.ofFn (fun c : Fin L.q => ratCode (L.A r c))).flatten)).flatten ++
    (List.ofFn (fun r : Fin L.p => ratCode (L.b r))).flatten ++
    (List.ofFn (fun c : Fin L.q => ratCode (L.c c))).flatten

def denseCode (I : Instance) (k : ℕ) (w : GridColumn I k → ℚ) : List Bool :=
  listCode (fun z => ratCode (w z)) (columnList I k)

/-- Feasibility is posed over all real weights, even though the output is rational. -/
def GridFeasible (I : Instance) (D : BinaryData I) (k : ℕ) (ε : ℚ)
    (w : GridColumn I k → ℝ) : Prop :=
  ∀ r : GridRow I k, ∑ z, (rowCoeff I D k ε r z : ℝ) * w z ≤ rowBound I D k r

noncomputable def gridCost (I : Instance) (D : BinaryData I) (k : ℕ)
    (w : GridColumn I k → ℝ) : ℝ := ∑ z, (objectiveCoeff I D k z : ℝ) * w z

/-- An optimal basic solution: a feasible vertex that minimizes over real feasible points.
The midpoint condition characterizes vertices of this convex polyhedron. -/
def OptimalBasic (I : Instance) (D : BinaryData I) (k : ℕ) (ε : ℚ)
    (w : GridColumn I k → ℚ) : Prop :=
  GridFeasible I D k ε (fun z => (w z : ℝ)) ∧
  (∀ v, GridFeasible I D k ε v →
    gridCost I D k (fun z => (w z : ℝ)) ≤ gridCost I D k v) ∧
  ∀ u v, GridFeasible I D k ε u → GridFeasible I D k ε v →
    (∀ z, (u z + v z) / 2 = (w z : ℝ)) → u = v

noncomputable def outputMeasure (I : Instance) (k : ℕ) (hk : 0 < k)
    (w : GridColumn I k → ℚ) : Scheme I :=
  ∑ z, ENNReal.ofReal (w z : ℝ) • Measure.dirac (z.1, gridFlow I.network k hk z.2)

/-- Sparse list output: state, positive paths (as actual arc lists) and joint probability.
Zero entries are omitted. No exponential path list is smuggled into the input. -/
def outputCode (I : Instance) (k : ℕ) (w : GridColumn I k → ℚ)
    (order : List (GridColumn I k)) : List Bool :=
  listCode (fun z : GridColumn I k =>
    natCode z.1.val ++
      listCode (fun p : Path I.network =>
        listCode (fun i : Fin I.network.arcs => natCode i.val) (pathArcs I.network p) ++
          ratCode (qGrid I.network k z.2 p))
        ((List.finRange (pathList I.network).length).filter (fun p => 0 < (z.2.val p).val)) ++
      ratCode (w z))
    order

/-- Output ordering is free, but every positive joint probability appears exactly once. -/
def OutputOrder (I : Instance) (k : ℕ) (w : GridColumn I k → ℚ)
    (order : List (GridColumn I k)) : Prop :=
  order.Nodup ∧ ∀ z, z ∈ order ↔ 0 < w z

/-- An actual fixed composition of three finite tape programs, with no behavioral fields:
construct P_ε, solve that rational LP, then emit the sparse scheme. -/
structure Pipeline where
  prepare : EditGV897.Main.Program
  solve : EditGV897.Main.Program
  emit : EditGV897.Main.Program

/-- Operational execution of the three programs in order. Intermediate strings are written
by one stage and read by the next. Handoffs additionally charge every intermediate/input bit.
There are no unit-cost arithmetic, enumeration, evaluation or LP oracle instructions. -/
def PipelineRuns (P : Pipeline) (I : Instance) (D : BinaryData I) (L ε : ℚ)
    (k : ℕ) (w : GridColumn I k → ℚ) (order : List (GridColumn I k)) (budget : ℕ) : Prop :=
  let input := inputCode I D L ε
  let lp := lpCode (discretizedLP I D k ε)
  let dense := denseCode I k w
  let lastInput := EditGV897.Main.frame input ++ dense
  ∃ t₁ t₂ t₃ : ℕ,
    EditGV897.Main.Runs P.prepare input lp t₁ ∧
    EditGV897.Main.Runs P.solve lp dense t₂ ∧
    EditGV897.Main.Runs P.emit lastInput (outputCode I k w order) t₃ ∧
    t₁ + t₂ + t₃ + lp.length + dense.length + lastInput.length ≤ budget

/-- Suppressed factors are a fixed polynomial of input length and evaluation cost.
Only the evaluation-envelope polynomial has an instance-dependent degree. -/
noncomputable def timeBudget (A a b C : ℕ) (I : Instance) (E : ℕ → ℕ)
    (inputLength k : ℕ) (L ε : ℝ) : ℕ :=
  A * (1 + inputLength + E (A * (1 + inputLength + Nat.log 2 (k + 1)) ^ b)) ^ b *
    (1 + I.states) ^ a *
    (max 2 I.network.arcs) ^ ⌈(C : ℝ) * ((I.network.d : ℝ) + (I.network.d : ℝ)^3 * L / ε)⌉₊

end PrivateRoutingSignaling.PTAS


