-- Prove2me | Definitions.Def_GEGIAMP_Relative_Machine
-- name    : GEGIAMP_Relative_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:50:29.471287+00:00
-- url     : https://prove2.me/theorems/43fa2aca-ba0f-4252-8623-0921d476507f
-- title:
--   The Parisi-data oracle model (Definition 2.2) as a costed instruction language
-- statement:
--   A structured program language over an unbounded real memory and an integer memory. Unit-cost primitives: exact real $+,-,\times,\div$ and literals; $\sqrt{\cdot}$; $\log$; integer rounding $\lfloor\cdot\rfloor,\lceil\cdot\rceil$ and the integer-to-real cast; integer $+,-,\times$; indirect load/store; one evaluation of $\gamma(t)$, $m(t,x)$ or $a(t,x)$; one standard Gaussian draw from an i.i.d. $N(0,1)$ tape; and comparisons in `if`/`while` tests. No matrix primitive: a dense product is a loop of $N^2$ unit operations. Work is the number of executed units (memory accesses are charged); storage is the number of distinct cells touched, input included; marked blocks count dense products and Euler–Maruyama steps in the execution trace. Fuel-indexed big-step semantics and the final state of a terminating run.
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Definition 2.2, §2.3, p. 7

import Mathlib

/-!
# The Parisi-data oracle model (Definition 2.2) as a costed instruction language

Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1 (SHA-256 ea6508af…5658e),
Definition 2.2, §2.3, p. 7: "The algorithm receives the explicitly supplied matrix A, a target
accuracy, and a failure probability α ∈ (0, 1/2). It can evaluate γ(t), m(t, x), a(t, x)
(0 ≤ t < 1, x ∈ ℝ). Each oracle evaluation, real arithmetic operation, comparison, square root,
logarithm of a positive real number, integer rounding, and independent standard Gaussian draw
costs one unit. In particular, a dense matrix–vector product costs O(N²)."

**The machine.** A structured program (`Cmd`) over two unbounded memories, a real memory
`R : ℕ → ℝ` and an integer memory `Z : ℕ → ℤ`, with
* exact real `+ − × ÷` (`x/0 = 0`, Lean's convention), real literals;
* `√` (`Real.sqrt`), `log` (`Real.log`; the paper only takes logarithms of positive reals);
* integer rounding `⌊·⌋`, `⌈·⌉` (real → integer), the cast integer → real;
* integer `+ − ×` and integer literals (index arithmetic);
* indirect real load/store through an integer pointer (memory and index operations);
* one evaluation of `γ(t)`, `m(t, x)` or `a(t, x)`;
* one standard Gaussian draw: the next cell of an i.i.d. `N(0, 1)` tape;
* comparisons (`<`, `≤` of reals or integers) in `if` and `while` tests.

Every primitive operation and every test **costs one unit** (`work`), memory accesses included.
There is no matrix or vector primitive: a dense product is a loop of `N²` unit operations.
**Storage** is the number of distinct memory cells (real or integer) touched by the run
(read, written or holding input); nothing is ever freed, so this is the peak number of cells
in use. Tape cells are not storage (they are the source of randomness, not memory).

`mark l c` runs `c` and records one execution of a block of kind `l` (used to count the dense
products and the Euler–Maruyama steps of an execution trace); it has no cost of its own and
changes nothing else. Oracle functions are parameters of the semantics.
-/

namespace GEGIAMP.Relative

/-- The three Parisi-data oracles of (2.7): `γ(t)`, `m(t, x)`, `a(t, x)`. -/
structure Oracles where
  gam : ℝ → ℝ
  m : ℝ → ℝ → ℝ
  a : ℝ → ℝ → ℝ

/-- A primitive operation (one unit each). Real cells are `R i`, integer cells `Z i`. -/
inductive Op where
  /-- `R d := c`. -/
  | lit (d : ℕ) (c : ℝ)
  /-- `R d := R i + R j`. -/
  | add (d i j : ℕ)
  /-- `R d := R i − R j`. -/
  | sub (d i j : ℕ)
  /-- `R d := R i * R j`. -/
  | mul (d i j : ℕ)
  /-- `R d := R i / R j`. -/
  | div (d i j : ℕ)
  /-- `R d := √(R i)`. -/
  | sqrt (d i : ℕ)
  /-- `R d := log (R i)`. -/
  | log (d i : ℕ)
  /-- `Z d := ⌊R i⌋`. -/
  | floor (d i : ℕ)
  /-- `Z d := ⌈R i⌉`. -/
  | ceil (d i : ℕ)
  /-- `R d := (Z i : ℝ)`. -/
  | cast (d i : ℕ)
  /-- `Z d := n`. -/
  | zlit (d : ℕ) (n : ℤ)
  /-- `Z d := Z i + Z j`. -/
  | zadd (d i j : ℕ)
  /-- `Z d := Z i − Z j`. -/
  | zsub (d i j : ℕ)
  /-- `Z d := Z i * Z j`. -/
  | zmul (d i j : ℕ)
  /-- `R d := R (Z p)` (indirect load; a negative pointer reads cell `0`). -/
  | load (d p : ℕ)
  /-- `R (Z p) := R i` (indirect store). -/
  | store (p i : ℕ)
  /-- `R d := γ(R i)`. -/
  | gam (d i : ℕ)
  /-- `R d := m(R i, R j)`. -/
  | mo (d i j : ℕ)
  /-- `R d := a(R i, R j)`. -/
  | ao (d i j : ℕ)
  /-- `R d :=` the next standard Gaussian of the tape. -/
  | gauss (d : ℕ)

/-- A test (one unit). -/
inductive Cond where
  /-- `R i < R j`. -/
  | rlt (i j : ℕ)
  /-- `R i ≤ R j`. -/
  | rle (i j : ℕ)
  /-- `Z i < Z j`. -/
  | zlt (i j : ℕ)
  /-- `Z i ≤ Z j`. -/
  | zle (i j : ℕ)

/-- Kinds of marked blocks of an execution trace. -/
inductive Label where
  /-- A dense product `A q_s` with a matrix query. -/
  | queryProduct
  /-- The dense product `A v` that initializes rounding. -/
  | roundProduct
  /-- One Euler–Maruyama step (6.14) of one coordinate. -/
  | step
  deriving DecidableEq

/-- Structured programs. -/
inductive Cmd where
  | skip
  | op (o : Op)
  | seq (c₁ c₂ : Cmd)
  | ite (b : Cond) (c₁ c₂ : Cmd)
  | while (b : Cond) (c : Cmd)
  | mark (l : Label) (c : Cmd)

/-- A memory cell: `(false, i)` is `R i`, `(true, i)` is `Z i`. -/
abbrev Cell := Bool × ℕ

/-- A machine state. -/
structure State where
  R : ℕ → ℝ
  Z : ℕ → ℤ
  /-- The Gaussian tape and its cursor. -/
  tape : ℕ → ℝ
  ptr : ℕ
  /-- Unit operations executed so far. -/
  work : ℕ
  /-- Cells touched so far (input cells included). -/
  cells : Finset Cell
  /-- Executions of marked blocks so far. -/
  marks : Label → ℕ

namespace State

/-- Record an access to the given cells. -/
def touch (s : State) (cs : List Cell) : State := { s with cells := s.cells ∪ cs.toFinset }

/-- Charge one unit. -/
def tick (s : State) : State := { s with work := s.work + 1 }

/-- Write a real cell. -/
def setR (s : State) (d : ℕ) (x : ℝ) : State := { s with R := Function.update s.R d x }

/-- Write an integer cell. -/
def setZ (s : State) (d : ℕ) (n : ℤ) : State := { s with Z := Function.update s.Z d n }

end State

/-- One primitive operation (charged one unit, its cells recorded). -/
noncomputable def stepOp (O : Oracles) (o : Op) (s : State) : State :=
  let s := s.tick
  match o with
  | .lit d c => (s.setR d c).touch [(false, d)]
  | .add d i j => (s.setR d (s.R i + s.R j)).touch [(false, d), (false, i), (false, j)]
  | .sub d i j => (s.setR d (s.R i - s.R j)).touch [(false, d), (false, i), (false, j)]
  | .mul d i j => (s.setR d (s.R i * s.R j)).touch [(false, d), (false, i), (false, j)]
  | .div d i j => (s.setR d (s.R i / s.R j)).touch [(false, d), (false, i), (false, j)]
  | .sqrt d i => (s.setR d (Real.sqrt (s.R i))).touch [(false, d), (false, i)]
  | .log d i => (s.setR d (Real.log (s.R i))).touch [(false, d), (false, i)]
  | .floor d i => (s.setZ d ⌊s.R i⌋).touch [(true, d), (false, i)]
  | .ceil d i => (s.setZ d ⌈s.R i⌉).touch [(true, d), (false, i)]
  | .cast d i => (s.setR d (s.Z i : ℝ)).touch [(false, d), (true, i)]
  | .zlit d n => (s.setZ d n).touch [(true, d)]
  | .zadd d i j => (s.setZ d (s.Z i + s.Z j)).touch [(true, d), (true, i), (true, j)]
  | .zsub d i j => (s.setZ d (s.Z i - s.Z j)).touch [(true, d), (true, i), (true, j)]
  | .zmul d i j => (s.setZ d (s.Z i * s.Z j)).touch [(true, d), (true, i), (true, j)]
  | .load d p => (s.setR d (s.R (s.Z p).toNat)).touch [(false, d), (true, p), (false, (s.Z p).toNat)]
  | .store p i => (s.setR (s.Z p).toNat (s.R i)).touch [(false, (s.Z p).toNat), (true, p), (false, i)]
  | .gam d i => (s.setR d (O.gam (s.R i))).touch [(false, d), (false, i)]
  | .mo d i j => (s.setR d (O.m (s.R i) (s.R j))).touch [(false, d), (false, i), (false, j)]
  | .ao d i j => (s.setR d (O.a (s.R i) (s.R j))).touch [(false, d), (false, i), (false, j)]
  | .gauss d => ({ s.setR d (s.tape s.ptr) with ptr := s.ptr + 1 }).touch [(false, d)]

/-- Evaluate a test (its cells recorded; the unit is charged by the caller). -/
def evalCond (b : Cond) (s : State) : Prop :=
  match b with
  | .rlt i j => s.R i < s.R j
  | .rle i j => s.R i ≤ s.R j
  | .zlt i j => s.Z i < s.Z j
  | .zle i j => s.Z i ≤ s.Z j

/-- The cells a test reads. -/
def condCells (b : Cond) : List Cell :=
  match b with
  | .rlt i j | .rle i j => [(false, i), (false, j)]
  | .zlt i j | .zle i j => [(true, i), (true, j)]

open Classical in
/-- Big-step semantics with fuel: `exec O n c s = some s'` when `c` run from `s` terminates
within nesting/iteration depth `n` in state `s'`. Tests cost one unit. -/
noncomputable def exec (O : Oracles) : ℕ → Cmd → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, s => some s
  | _ + 1, .op o, s => some (stepOp O o s)
  | n + 1, .seq c₁ c₂, s => (exec O n c₁ s).bind (exec O n c₂)
  | n + 1, .ite b c₁ c₂, s =>
    let s' := (s.tick).touch (condCells b)
    if evalCond b s then exec O n c₁ s' else exec O n c₂ s'
  | n + 1, .while b c, s =>
    let s' := (s.tick).touch (condCells b)
    if evalCond b s then (exec O n c s').bind (exec O n (.while b c)) else some s'
  | n + 1, .mark l c, s =>
    (exec O n c s).map fun t => { t with marks := Function.update t.marks l (t.marks l + 1) }

/-- The program terminates from `s`. -/
def Halts (O : Oracles) (c : Cmd) (s : State) : Prop := ∃ n, (exec O n c s).isSome

open Classical in
/-- The final state of a terminating run (`none` if the run does not terminate). -/
noncomputable def finalState (O : Oracles) (c : Cmd) (s : State) : Option State :=
  if h : Halts O c s then exec O (Nat.find h) c s else none

/-- Sequential composition of a list of commands. -/
def seqs : List Cmd → Cmd
  | [] => .skip
  | c :: cs => .seq c (seqs cs)

end GEGIAMP.Relative


