-- Prove2me | Definitions.Def_DigraphDFSStream_Main_StreamingMachine
-- name    : DigraphDFSStream_Main_StreamingMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:27.686291+00:00
-- url     : https://prove2.me/theorems/ba18adc9-dbf7-427c-a156-e571dcbca983
-- title:
--   Uniform bit-stack streaming programs and charged execution prefixes
-- statement:
--   A program is a finite list of instructions operating on eight stacks of bits. Instructions push one bit, pop and branch on one bit, read a fresh fair coin, read the next edge, rewind at the end of a stream, or halt. A program has no graph oracle, arbitrary transition callback, position-query instruction, or persistent public random seed.
--
--   The public input is $n$, initially stored in binary. Reading an edge stores its two labels and a nonempty-input flag in working stacks. End-of-stream reads store an empty-input flag. Rewinding is allowed only after consuming the current stream. Passes, the remaining input suffix, and the coin head are interpreter data that code cannot inspect. The same adversarial input order is used on every pass.
--
--   Every mutable stack, including output stack 7, is charged. If stack lengths are $\ell_i$ and the program counter is $j$, the charge is
--   $$\operatorname{bitlength}(j)+1+\sum_{i=0}^7(2\ell_i+1).$$
--   The unary-delimited list encoding charges both stack contents and lengths. The program counter can be placed last in the encoding. Prefixes include temporary storage and failure executions; a resource bound is not conditional on success. The program must halt on every tape in the target resource predicate.
--
--   The random tape is the countable product of independent fair bits. Old coins are unavailable unless retained in charged memory. A pass bound $p(n)$ has exponent $a+o(1)$ when, for the same $p$,
--   $$\forall\varepsilon>0\ \exists C_\varepsilon>0,N_\varepsilon\ \forall n\ge N_\varepsilon,\quad p(n)\le C_\varepsilon n^{a+\varepsilon}.$$
--   Semi-streaming bits use a single fixed logarithmic exponent and a uniform constant; $n+1$ and $\log_2(n+2)+1$ handle small inputs.
--
--   The model is an operational vocabulary for stating the target, not a supplied implementation of Algorithms 2–4. Correctness and resource predicates must still be proved for a program witness.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), §2, Multipass Semi-Streaming Model, printed p.4 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace DigraphDFSStream.Main

/-- A fixed eight-stack bit machine. Its program is a finite list, independent of n and the input.
There are no arbitrary-function instructions, graph oracles, public counters, or persistent seeds. -/
inductive StreamInstruction where
  | push (dst : Fin 8) (bit : Bool) (next : ℕ)
  | pop (src : Fin 8) (ifEmpty ifFalse ifTrue : ℕ)
  | coin (dst : Fin 8) (next : ℕ)
  | readEdge (next : ℕ)
  | rewind (next : ℕ)
  | halt
  deriving Inhabited

abbrev StreamProgram := List StreamInstruction

/-- The complete charged mutable configuration. Stack 7 is the output buffer. -/
structure StreamMemory where
  pc : ℕ
  cells : Fin 8 → List Bool

/-- Ghost execution data: input and coin heads and the pass counter cannot be inspected by code.
Only readEdge, coin and rewind, respectively, can interact with the heads. -/
structure StreamConfiguration (n : ℕ) where
  memory : StreamMemory
  remaining : List (Fin n × Fin n)
  coinHead : ℕ
  passes : ℕ

/-- Little-endian canonical binary, with zero represented by the empty list. -/
def binary (v : ℕ) : List Bool := Nat.bits v

/-- Prefix-free list encoding takes 2*l+1 bits per stack, and a binary program counter.
This charges stack-length information as well as every data/output bit. -/
def chargedBits (m : StreamMemory) : ℕ :=
  (binary m.pc).length + 1 + ∑ i : Fin 8, (2 * (m.cells i).length + 1)

def initialConfiguration (n : ℕ) (input : List (Fin n × Fin n)) : StreamConfiguration n :=
  ⟨⟨0, fun i => if i = 0 then binary n else []⟩, input, 0, 1⟩

/-- One deterministic microstep after fixing a fresh, read-once fair coin tape.
The interpreter exposes no operations other than the finite instruction set. -/
def streamStep {n : ℕ} (P : StreamProgram) (input : List (Fin n × Fin n))
    (ω : ℕ → Bool) (s : StreamConfiguration n) : Option (StreamConfiguration n) :=
  match P[s.memory.pc]? with
  | none => none
  | some .halt => none
  | some (.push dst bit next) =>
      some {s with memory := ⟨next, Function.update s.memory.cells dst (bit :: s.memory.cells dst)⟩}
  | some (.pop src ifEmpty ifFalse ifTrue) =>
      match s.memory.cells src with
      | [] => some {s with memory := {s.memory with pc := ifEmpty}}
      | b :: bs => some {s with memory :=
          ⟨if b then ifTrue else ifFalse, Function.update s.memory.cells src bs⟩}
  | some (.coin dst next) =>
      some {s with coinHead := s.coinHead + 1, memory :=
        ⟨next, Function.update s.memory.cells dst (ω s.coinHead :: s.memory.cells dst)⟩}
  | some (.readEdge next) =>
      match s.remaining with
      | [] => some {s with memory := ⟨next,
          Function.update (Function.update (Function.update s.memory.cells 1 []) 2 []) 3 [false]⟩}
      | e :: es => some {s with remaining := es, memory := ⟨next,
          Function.update (Function.update (Function.update s.memory.cells 1 (binary e.1.val))
            2 (binary e.2.val)) 3 [true]⟩}
  | some (.rewind next) =>
      if s.remaining.isEmpty then
        some {s with remaining := input
                     passes := s.passes + 1
                     memory := {s.memory with pc := next}}
      else none

/-- Prefix reachability does not discard failure paths or temporary scratch configurations. -/
inductive StreamReaches {n : ℕ} (P : StreamProgram) (input : List (Fin n × Fin n))
    (ω : ℕ → Bool) : StreamConfiguration n → Prop where
  | initial : StreamReaches P input ω (initialConfiguration n input)
  | next (s t : StreamConfiguration n) : StreamReaches P input ω s →
      streamStep P input ω s = some t → StreamReaches P input ω t

def StreamHalts {n : ℕ} (P : StreamProgram) (input : List (Fin n × Fin n))
    (ω : ℕ → Bool) (output : List Bool) : Prop :=
  ∃ s, StreamReaches P input ω s ∧ P[s.memory.pc]? = some .halt ∧
    output = s.memory.cells 7

/-- Product of fair Bernoulli measures; coins are not a graph-dependent input distribution. -/
noncomputable def fairCoins : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- Worst-case bit and pass bounds over every prefix, every stream and every tape.
The program cannot inspect the two ghost counters or the remaining input list. -/
def HasStreamingBounds (P : StreamProgram) (bits passes : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (input : List (Fin n × Fin n)) (ω : ℕ → Bool),
    (∃ output, StreamHalts P input ω output) ∧
    ∀ s, StreamReaches P input ω s →
      chargedBits s.memory ≤ bits n ∧ s.passes ≤ passes n

/-- All-epsilon formulation for one and the same bound function. -/
def SubpowerPasses (a : ℝ) (passes : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → (passes n : ℝ) ≤ C * (n : ℝ) ^ (a + ε)

/-- A fixed logarithmic exponent; no n-dependent O-constant or exponent. -/
def SemistreamingBits (bits : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n : ℕ,
    bits n ≤ C * (n + 1) * (Nat.log2 (n + 2) + 1) ^ d

end DigraphDFSStream.Main


