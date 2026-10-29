-- Prove2me | Definitions.Def_CapacitatedAssort_General_Algorithm
-- name    : CapacitatedAssort_General_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:29.370412+00:00
-- url     : https://prove2.me/theorems/8e87ffdb-cbe3-4d87-b15c-e36b7736cf3a
-- title:
--   Algorithm 1: geometric enumeration and a counted rounded DP
-- statement:
--   The program scans each coefficient column for its extrema, then generates successive geometric points from its minimum until reaching $n$ times its maximum. A computed Bernoulli upper bound on the number of steps makes the recursive definition total; on the source domain it does not truncate the grid. The finite bound is computed using arithmetic and ceiling, with no logarithm oracle. All Cartesian-product guesses are enumerated by mixed-radix addresses.
--
--   For each guess, floor/ceiling-rounded coefficients are materialized. A finite array contains every canonical residual vector between zero and the saturated increasing demand or decreasing budget. At prefix zero, a state is reachable exactly when all lower demands are zero; upper budgets in the table are nonnegative. Each subsequent row compares exclusion with inclusion using the preceding materialized row, subtracting the rounded coefficient vector, saturating lower requirements, and rejecting negative upper budgets. Unreachable cells are absent; reachable cells hold a finite weight and a persistent witness spine. Inclusion conses the current item onto the predecessor witness; exclusion wins finite ties. The terminal cell is the maximal demand vector, and the witness spine is traversed explicitly for output.
--
--   Algorithm 1 discards unreachable guesses and witnesses whose computed weight exceeds capacity, evaluates $g$ on the actual witness's column sums, and returns the first maximum-valued candidate. With no candidate it returns failure. It never inserts an extra empty candidate or searches the global optimum. The returned list is viewed as a finite subset without changing its operational representation. The operation counter covers extrema, grids, rounding, all table construction and transitions, traceback, candidate sums, oracle evaluation and comparisons. No claim of correctness is part of this definition. Positive coefficients and $\epsilon>0$ ensure that the total-function defaults in malformed inputs are not used; the source theorems impose those conditions.
-- source:
--   Désir, Goyal and Zhang (2021), Technical Note—Capacitated Assortment Optimization: Hardness and Approximation, https://doi.org/10.1287/opre.2021.2142, held source.pdf, Algorithm 1, equations (7)–(10), PDF/printed pp. 11–14

import Definitions.Def_CapacitatedAssort_General_Model
import Definitions.Def_CapacitatedAssort_General_Work

/- Exact imported Lean source for tool-free blind auditing.

--- Definitions/Def_CapacitatedAssort_General_Functions.lean ---
import Mathlib

namespace CapacitatedAssort.General

/-- Componentwise monotonicity on the entire real domain, with a fixed split. -/
def MixedMonotone {M : ℕ} (k : ℕ) (g : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ (m : Fin M) (x : Fin M → ℝ) (s t : ℝ), s ≤ t →
    if m.val < k then g (Function.update x m s) ≤ g (Function.update x m t)
    else g (Function.update x m t) ≤ g (Function.update x m s)

/-- Nonnegative O(δ) error near zero from the right; zero error is permitted. -/
def SmallError (u : ℝ → ℝ) : Prop :=
  (∀ δ, 0 ≤ u δ) ∧ ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧
    ∀ δ, 0 < δ → δ < η → u δ ≤ C * δ

def scale {M : ℕ} (k : ℕ) (α β : ℝ) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun m => (if m.val < k then α else β) * x m

/-- Uniform reading of Assumption 2: the loss and threshold precede all x. -/
def ScalingStable {M : ℕ} (k : ℕ) (g : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ u v : ℝ → ℝ, SmallError u → SmallError v →
    ∃ e : ℝ → ℝ, SmallError e ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ, 0 < δ → δ < η → ∀ x : Fin M → ℝ,
        (1 - e δ) * g x ≤ g (scale k (1 - u δ) (1 + v δ) x)

end CapacitatedAssort.General

--- Definitions/Def_CapacitatedAssort_General_Model.lean ---
import Definitions.Def_CapacitatedAssort_General_Functions

noncomputable section
namespace CapacitatedAssort.General
open Finset

/-- Section 3.1 data. All numerical data remain real. -/
structure Instance (n M : ℕ) where
  a : Fin n → Fin M → ℝ
  w : Fin n → ℝ
  W : ℝ
  split : ℕ
  g : (Fin M → ℝ) → ℝ

def Standing {n M : ℕ} (D : Instance n M) : Prop :=
  0 < n ∧ 0 < M ∧ D.split ≤ M ∧
  (∀ i m, 0 < D.a i m) ∧ (∀ i, 0 ≤ D.w i) ∧ 0 ≤ D.W

def weight {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, D.w i

def sums {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : Fin M → ℝ :=
  fun m => ∑ i ∈ S, D.a i m

def value {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : ℝ := D.g (sums D S)

def Feasible {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : Prop := weight D S ≤ D.W

/-- Attained finite maximum. The fallback occurs only when even ∅ is infeasible. -/
def optimum {n M : ℕ} (D : Instance n M) : ℝ := by
  classical
  let F := (univ : Finset (Finset (Fin n))).filter (Feasible D)
  exact if h : F.Nonempty then F.sup' h (value D) else 0

/-- Empty-column defaults are outside Standing. -/
def amin {n M : ℕ} (D : Instance n M) (m : Fin M) : ℝ :=
  ((List.finRange n).map (fun i => D.a i m)).foldl min (if h : 0 < n then D.a ⟨0,h⟩ m else 0)

def amax {n M : ℕ} (D : Instance n M) (m : Fin M) : ℝ :=
  ((List.finRange n).map (fun i => D.a i m)).foldl max (if h : 0 < n then D.a ⟨0,h⟩ m else 0)

/-- The theorem's unindexed A_max is the largest column ratio. -/
def ratio {n M : ℕ} (D : Instance n M) : ℝ :=
  ((List.finRange M).map (fun m => amax D m / amin D m)).foldl max 1

/-- Minimal covering exponent, not a restriction on the real coefficients. -/
def gridLength {n M : ℕ} (D : Instance n M) (ε : ℝ) (m : Fin M) : ℕ := by
  classical
  exact if h : ∃ L : ℕ, (n : ℝ) * amax D m ≤ amin D m * (1 + ε)^L then Nat.find h else 0

def GridGuess {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) : Prop :=
  ∀ m, ∃ ℓ : ℕ, ℓ ≤ gridLength D ε m ∧ h m = amin D m * (1 + ε)^ℓ

def GuessFeasible {n M : ℕ} (D : Instance n M) (h : Fin M → ℝ) (S : Finset (Fin n)) : Prop :=
  Feasible D S ∧ ∀ m, if m.val < D.split then h m ≤ sums D S m else sums D S m ≤ h m

def Rounded {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) (i : Fin n) (m : Fin M) : ℤ :=
  if m.val < D.split then ⌊(n : ℝ) * D.a i m / (ε * h m)⌋
  else ⌈(n : ℝ) * D.a i m / (ε * h m)⌉

def lowerDemand (n : ℕ) (ε : ℝ) : ℤ := ⌊(n : ℝ) / ε⌋ - (n : ℤ)
def upperDemand (n : ℕ) (ε : ℝ) : ℤ := ⌈(n : ℝ) / ε⌉ + (n : ℤ)

/-- The printed runtime expression, evaluated only with n*ratio ≥ 2 and 0<ε<1. -/
def runtimeScale {n M : ℕ} (D : Instance n M) (ε : ℝ) : ℝ :=
  (Real.log ((n : ℝ) * ratio D))^M * (n : ℝ)^(M+1) / ε^(4*M)

end CapacitatedAssort.General

--- Definitions/Def_CapacitatedAssort_General_Work.lean ---
import Mathlib

namespace CapacitatedAssort.General

/-- Writer-style instrumented real-RAM computations. The state counts operations.
Arrays have unit read/write and amortized push, persistent list cons is unit,
and scalar arithmetic/comparison/rounding and one value-oracle call are unit.
Charges below group a fixed number of these instructions, never an asymptotic bound. -/
abbrev Work (α : Type) := StateM ℕ α

def charge (k : ℕ) : Work Unit := modify (· + k)

/-- Materialize a finite index loop: test, increment and index construction,
then one loop dispatch per element. Callback operations are charged separately. -/
def tabulate {α : Type} (n : ℕ) (f : Fin n → Work α) : Work (Array α) := do
  charge (3*n+1)
  let mut out := #[]
  for i in List.finRange n do
    charge 1
    let x ← f i
    charge 1
    out := out.push x
  return out

/-- Copy a persistent witness spine into an output list (traceback). -/
def trace {α : Type} : List α → Work (List α)
  | [] => do charge 1; return []
  | x :: xs => do
      charge 2
      let tail ← trace xs
      charge 1
      return x :: tail

/-- Mixed-radix decoding, coordinate zero least significant. -/
def decode (bases : Array ℕ) (j : ℕ) : Work (Array ℤ) := do
  charge (3*bases.size+1)
  let mut q := j
  let mut out := #[]
  for m in List.finRange bases.size do
    charge 6 -- dispatch, read, remainder, integer conversion, quotient, push
    let b := bases[m.val]!
    let r : ℤ := (q % b : ℕ)
    q := q / b
    out := out.push r
  return out

/-- Mixed-radix addressing. Called only on canonical residuals. -/
def encode (bases : Array ℕ) (r : Array ℤ) : Work ℕ := do
  charge (3*bases.size+1)
  let mut stride := 1
  let mut j := 0
  for m in List.finRange bases.size do
    charge 7 -- dispatch, two reads, toNat, two multiplies, addition
    j := j + (r[m.val]!).toNat * stride
    stride := stride * bases[m.val]!
  return j

def boxSize (bases : Array ℕ) : Work ℕ := do
  charge (3*bases.size+1)
  let mut size := 1
  for m in List.finRange bases.size do
    charge 3 -- dispatch, read, multiplication
    size := size * bases[m.val]!
  return size

end CapacitatedAssort.General

-/

noncomputable section
namespace CapacitatedAssort.General
open Classical

/-- Each step tests coverage before extending the geometric grid. Fuel is only a
termination bound; on admissible inputs Bernoulli's inequality ensures coverage
before it expires. No list of length fuel is allocated or traversed in advance. -/
def geometric (ε target : ℝ) : ℕ → ℝ → Work (List ℝ)
  | 0, x => do charge 1; return [x]
  | fuel+1, x => do
      charge 2 -- fuel branch and real comparison
      if target ≤ x then
        charge 1
        return [x]
      else
        charge 2 -- addition and multiplication
        let tail ← geometric ε target fuel (x * (1+ε))
        charge 1 -- cons
        return x :: tail

/-- Scan the actual input for each column's extrema, then generate its grid. -/
def makeGrids {n M : ℕ} (D : Instance n M) (ε : ℝ) : Work (Array (Array ℝ)) :=
  tabulate M fun m => do
    charge 2 -- empty test, initial coefficient read
    let start := if hn : 0 < n then D.a ⟨0,hn⟩ m else 0
    let mut lo := start
    let mut hi := start
    charge (3*n+1)
    for i in List.finRange n do
      charge 4 -- loop, coefficient read, min comparison, max comparison
      let a := D.a i m
      lo := min lo a
      hi := max hi a
    charge 6 -- cast n, multiply, two divisions, ceiling, increment
    let target := (n : ℝ) * hi
    let fuel := ⌈target / lo / ε⌉₊ + 1
    let grid ← geometric ε target fuel lo
    charge (2*grid.length+1) -- list traversal and array writes
    return grid.toArray

/-- Canonical residual bounds: increasing requirements saturated at zero;
decreasing budgets range from zero to I₂. -/
def makeBases (n M k : ℕ) (ε : ℝ) : Work (Array ℕ) := do
  charge 7 -- cast, divide, floor, ceil, integer cast, subtract, add
  let lo := lowerDemand n ε
  let hi := upperDemand n ε
  tabulate M fun m => do
    charge 3 -- split comparison, toNat (= saturation), successor
    return (if m.val < k then lo else hi).toNat + 1

/-- Residual subtraction returns failure for negative upper budgets. -/
def residual (k : ℕ) (r a : Array ℤ) : Work (Option (Array ℤ)) := do
  charge (3*r.size+1)
  let mut out := #[]
  let mut valid := true
  for m in List.finRange r.size do
    charge 5 -- loop, two reads, subtract, split comparison
    let d := r[m.val]! - a[m.val]!
    if m.val < k then
      charge 2 -- max comparison and push
      out := out.push (max 0 d)
    else
      charge 3 -- sign test, boolean update, push
      valid := valid && decide (0 ≤ d)
      out := out.push d
  charge 1
  return if valid then some out else none

/-- A finite weight and persistent witness spine; none is +infinity. -/
abbrev Cell (n : ℕ) := Option (ℝ × List (Fin n))

/-- Exclusion wins finite ties, a fixed reverse-index lexicographic convention. -/
def choose {n : ℕ} (exclude included : Cell n) : Work (Cell n) := do
  charge 1
  match exclude, included with
  | none, y => return y
  | x, none => return x
  | some x, some y =>
      charge 1
      return if x.1 ≤ y.1 then some x else some y

/-- The finite mixed-direction rounded DP; each previous row is materialized once.
Witness spines share tails; inclusion adds one node rather than copying a subset. -/
def runDP {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) : Work (Cell n) := do
  let bases ← makeBases n M D.split ε
  let size ← boxSize bases
  let states ← tabulate size fun j => decode bases j.val
  let rounded ← tabulate n fun i => tabulate M fun m => do
    charge 8 -- reads n,a,h; split compare; two multiplies; divide; round
    return Rounded D ε h i m
  let mut row ← tabulate size fun j => do
    charge 1 -- state read
    let r := states[j.val]!
    let mut ok := true
    charge (3*M+1)
    for m in List.finRange M do
      charge 5 -- loop, split test, read, zero comparison, boolean update
      if m.val < D.split then ok := ok && decide (r[m.val]! = 0)
    charge 1
    return if ok then (some (0, []) : Cell n) else none
  charge (3*n+1)
  for i in List.finRange n do
    charge 2 -- dispatch and rounded row read
    let a := rounded[i.val]!
    let old := row
    row ← tabulate size fun j => do
      charge 2 -- state and exclusion reads
      let r := states[j.val]!
      let ex := old[j.val]!
      let rem ← residual D.split r a
      let inc ← match rem with
        | none => do charge 1; pure none
        | some r' => do
            charge 1
            let index ← encode bases r'
            charge 2 -- table read and option branch
            match old[index]! with
            | none => pure none
            | some (w, S) => do
                charge 3 -- input weight read, addition, persistent cons
                pure (some (w + D.w i, i :: S))
      choose ex inc
  charge 2 -- terminal index subtraction and lookup
  let terminal := row[size-1]!
  charge 1
  match terminal with
  | none => return none
  | some (w, S) =>
      let copied ← trace S
      return some (w, copied)

/-- The source's F(I,n): unreachable states have +∞, not zero. -/
def terminalWeight {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) : WithTop ℝ :=
  match (runDP D ε h).run 0 |>.1 with
  | none => ⊤
  | some (w, _) => w

/-- Evaluate the objective on the actual witness by summing each input column. -/
def evalWitness {n M : ℕ} (D : Instance n M) (S : List (Fin n)) : Work ℝ := do
  let v ← tabulate M fun m => do
    let mut total := 0
    for i in S do
      charge 3 -- list dispatch, input read, addition
      total := total + D.a i m
    charge 1 -- end-of-list test
    return total
  charge 1 -- value oracle, passed the already materialized vector
  return D.g (fun m => v[m.val]!)

/-- Enumerate all geometric guesses, run the table, discard infeasible outputs,
and retain the first maximum-valued actual candidate. None means failure. -/
def algorithm {n M : ℕ} (D : Instance n M) (ε : ℝ) : Work (Option (List (Fin n))) := do
  let grids ← makeGrids D ε
  let bases ← tabulate M fun m => do
    charge 2 -- grid read and length
    return (grids[m.val]!).size
  let count ← boxSize bases
  let mut best : Option (ℝ × List (Fin n)) := none
  charge (3*count+1)
  for j in List.finRange count do
    charge 1
    let indices ← decode bases j.val
    let h ← tabulate M fun m => do
      charge 4 -- index read, toNat, grid read, grid element read
      return (grids[m.val]!)[(indices[m.val]!).toNat]!
    let ans ← runDP D ε (fun m => h[m.val]!)
    charge 1
    match ans with
    | none => pure ()
    | some (w, S) =>
        charge 1
        if w ≤ D.W then
          let v ← evalWitness D S
          charge 1
          match best with
          | none => best := some (v, S)
          | some (v', _) =>
              charge 1
              if v' < v then best := some (v, S)
  charge 1
  return best.map Prod.snd

def output {n M : ℕ} (D : Instance n M) (ε : ℝ) : Option (Finset (Fin n)) :=
  ((algorithm D ε).run 0).1.map List.toFinset

def operations {n M : ℕ} (D : Instance n M) (ε : ℝ) : ℕ :=
  ((algorithm D ε).run 0).2

end CapacitatedAssort.General


