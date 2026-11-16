-- Prove2me | Definitions.Def_DigraphDFSStream_Main_Supplement_ParameterizedStreaming
-- name    : DigraphDFSStream_Main_Supplement_ParameterizedStreaming
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:54:45.140121+00:00
-- url     : https://prove2.me/theorems/a0d5b12c-b69d-4431-b5e3-784c8064c123
-- title:
--   Charged parameters and tasks for the published streaming machine
-- statement:
--   A subroutine receives finite task data as well as an edge stream. A natural number is encoded by a unary length delimiter followed by its binary digits. Vertex lists and families of lists also include their lengths. The task data occupy stack 4 at entry; stack 0 retains the vertex count. Both are included in the published charge for mutable memory. The other initial stacks are empty. Subsequent steps use exactly the published finite instruction set, including its pass counter, edge reader and read-once fair coin tape.
--
--   For program $P$, stream $\sigma$, parameter string $h$, and output predicate $B$, the success event is
--   $$\{\omega:\text{the run of }P(\sigma,h;\omega)\text{ halts with output satisfying }B\}.$$
--   Resource bounds require termination and bounded passes and charged bits on every tape and every execution prefix. Reliability requires this event to be measurable and to have probability at least $1-\delta$. The public high-probability convention is $\delta=n^{-(c+1)}$ for $n\ge2$, with exact success for $n=1$, matching the published DFS target.
--
--   The accounting functions use $L(n)=\lceil\log_2 n\rceil+1$ for positive $n$. The work-space envelope is $C(b(n)+(n+1)L(n+2)^d)$, retaining a primitive's charged budget $b(n)$. Pass envelopes encode the exact logarithmic powers in §4. Integer ceilings round real bounds upwards; a lower bound of one pass covers the initial scan and size zero. The specialized joining envelope is $\lceil 2n/k\rceil+3kp(n)$, retaining the proof's Stage 1 constant two and two primitive calls plus one additional scan per Stage 2 path.
--
--   These definitions provide task input/output and resource accounting without granting graph access outside edge reads. The noncomputable real-valued bound expressions are specifications; they are not executable machine instructions.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), §2, printed p.4 (PDF p.5); §4, printed pp.11–18 (PDF pp.12–19)

import Definitions.Def_DigraphDFSStream_Main_StreamingMachine

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Self-delimiting binary naturals. Lengths and vertex labels are data, not free counters. -/
def natCode (a : ℕ) : List Bool :=
  List.replicate (binary a).length true ++ [false] ++ binary a

def vertexCode {m : ℕ} (xs : List (Fin m)) : List Bool :=
  natCode xs.length ++ xs.flatMap (fun x => natCode x.val)

def familyCode {m : ℕ} (xs : List (List (Fin m))) : List Bool :=
  natCode xs.length ++ xs.flatMap vertexCode

/-- The published machine, with a charged parameter string on stack 4 at entry.
Only vertex sets, paths, sources, and integer task parameters are supplied here, never edges.
The instruction interpreter and fair coin tape are exactly the published ones. -/
def parameterInitial {m : ℕ} (input : List (Fin m × Fin m))
    (header : List Bool) : StreamConfiguration m :=
  let s := initialConfiguration m input
  {s with memory := {s.memory with cells := Function.update s.memory.cells 4 header}}

inductive ParameterReaches {m : ℕ} (P : StreamProgram)
    (input : List (Fin m × Fin m)) (header : List Bool) (ω : ℕ → Bool) :
    StreamConfiguration m → Prop where
  | initial : ParameterReaches P input header ω (parameterInitial input header)
  | next (s t : StreamConfiguration m) : ParameterReaches P input header ω s →
      streamStep P input ω s = some t → ParameterReaches P input header ω t

def ParameterHalts {m : ℕ} (P : StreamProgram) (input : List (Fin m × Fin m))
    (header : List Bool) (ω : ℕ → Bool) (output : List Bool) : Prop :=
  ∃ s, ParameterReaches P input header ω s ∧ P[s.memory.pc]? = some .halt ∧
    output = s.memory.cells 7

def ParameterBounds {m : ℕ} (P : StreamProgram) (input : List (Fin m × Fin m))
    (header : List Bool) (bits passes : ℕ) : Prop :=
  ∀ ω : ℕ → Bool, (∃ out, ParameterHalts P input header ω out) ∧
    ∀ s, ParameterReaches P input header ω s →
      chargedBits s.memory ≤ bits ∧ s.passes ≤ passes

def ParameterSuccess {m : ℕ} (P : StreamProgram) (input : List (Fin m × Fin m))
    (header : List Bool) (accept : List Bool → Prop) : Set (ℕ → Bool) :=
  {ω | ∃ out, ParameterHalts P input header ω out ∧ accept out}

def ParameterReliable {m : ℕ} (P : StreamProgram) (input : List (Fin m × Fin m))
    (header : List Bool) (accept : List Bool → Prop) (δ : ℝ) : Prop :=
  MeasurableSet (ParameterSuccess P input header accept) ∧
    1 - δ ≤ fairCoins.real (ParameterSuccess P input header accept)

/-- Matches DFSHighProbability: exact correctness at size one, arbitrary fixed polynomial
confidence at larger sizes. Size zero is used only by internal tasks with an ambient size. -/
noncomputable def failure (c n : ℕ) : ℝ :=
  if n < 2 then 0 else (n : ℝ) ^ (-(c + 1 : ℝ))

def Solves {m : ℕ} (P : StreamProgram) (input : List (Fin m × Fin m))
    (header : List Bool) (accept : List Bool → Prop) (bits passes c n : ℕ) : Prop :=
  ParameterBounds P input header bits passes ∧
    ParameterReliable P input header accept (failure c n)

/-- Exact ceiling, so the path-count threshold is literally 4(ceil(log₂ n)+2). -/
def L (n : ℕ) : ℕ := Nat.clog 2 n + 1

/-- Space inherited from one sequential primitive, plus charged local records. All displayed
constants and exponents are quantified before p, b, n, k and the input graph in the theorems. -/
def workBits (C d : ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  C * (b n + (n + 1) * (L (n + 2)) ^ d)

noncomputable def tradeoff (C h : ℕ) (extra : Bool) (p : ℕ → ℕ) (n k : ℕ) : ℕ :=
  max 1 ⌈(C : ℝ) * ((n : ℝ) / k + (k : ℝ) * p n +
    (if extra then (p n : ℝ) else 0)) * (L n : ℝ) ^ h⌉₊

def mergePasses (C : ℕ) (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  max 1 (C * p n * L n)

noncomputable def rootPasses (C d : ℕ) (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  max 1 ⌈(C : ℝ) * Real.sqrt ((n : ℝ) * p n) * (L n : ℝ) ^ d⌉₊

noncomputable def quarterK (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊

/-- Stage 1: at most 2n/k scans. Stage 2: fewer than k paths, each with two
primitive calls and one scan, hence at most 3kp additional passes when p≥1. -/
noncomputable def joiningPasses (p : ℕ → ℕ) (n k : ℕ) : ℕ :=
  max 1 (⌈2 * (n : ℝ) / k⌉₊ + 3 * k * p n)

end DigraphDFSStream.Main.Supplement


