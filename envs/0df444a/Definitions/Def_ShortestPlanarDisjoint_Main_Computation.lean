-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Computation
-- name    : ShortestPlanarDisjoint_Main_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:41.474438+00:00
-- url     : https://prove2.me/theorems/d80772a0-56a7-49f2-80b7-4ce9b9476869
-- title:
--   Finite bit programs and uniform Boolean circuit families
-- statement:
--   A bit program has finitely many states, a read-only input tape, a fixed finite collection of mutable work tapes and a write-only output stream. Each transition reads at most one fresh fair bit, writes one symbol per work tape, moves each head at most one cell and emits at most one output bit. The alphabet consists of blank, zero and one. Run semantics charge these transitions; there is no instruction for arithmetic, graph queries or optimization.
--
--   Self-delimiting binary codes encode vertices, all unordered adjacency entries, natural edge costs, distinct terminals, their prescribed pairing and actual path witnesses. A leading output tag distinguishes infeasibility from a path list. Correctness means that the decoded paths are an attained optimum, or the infeasibility report is correct. Every execution must halt within its bound and output a feasible linkage or an infeasibility flag; an incorrect flag is allowed only on the error event. The uniform finite law counts all bit tapes of the stated length.
--
--   A Boolean circuit is an acyclic list of input, constant, negation, conjunction and disjunction gates, with sources restricted to earlier gates. Its size includes inputs, gates and output wires; its depth is computed from the wiring. Uniform families carry finite generator programs. Logspace uniformity is a separate predicate asserting actual generation from unary size, polynomial generation time and logarithmic work space, with read-only input and write-only output excluded from work space. Random families use a fixed polynomial data width, a uniformly determined random suffix and independent fair input bits. These are computational models and specifications, without correctness or resource certificates as structure fields.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 1.1, 4.2 and 5.5 (computational conventions), p. 13 (PDF p. 15)

import Definitions.Def_ShortestPlanarDisjoint_Main_Linkage

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- Self-delimiting binary integers: unary bit length, a zero, then the bits.
The redundant leading zero is intentional and fixes the code of zero. -/
def numberBits (a : ℕ) : List Bool :=
  let w := a.log2 + 1
  List.replicate w true ++ [false] ++ (List.range w).map a.testBit

def numbersBits (xs : List ℕ) : List Bool :=
  numberBits xs.length ++ xs.flatMap numberBits

noncomputable def RoutingInput.bits {n k : ℕ} (I : RoutingInput n k) : List Bool := by
  classical
  exact numbersBits ([n, k] ++ (List.ofFn I.terminal).map Fin.val ++
    (List.ofFn I.pairing.mate).map Fin.val) ++
    (List.finRange n).flatMap (fun u => (List.finRange n).flatMap fun v =>
      if u < v then if I.graph.Adj u v then true :: numberBits (I.weight s(u,v))
        else [false] else [])

noncomputable def Linkage.bits {n k : ℕ} {I : RoutingInput n k} (L : Linkage I) : List Bool := by
  classical
  letI : LinearOrder I.pairing.starts := inferInstanceAs (LinearOrder {i : Fin (2 * k) // i < I.pairing.mate i})
  let starts := (Finset.univ : Finset I.pairing.starts).sort (· ≤ ·)
  exact true :: (numberBits starts.length ++ starts.flatMap (fun i =>
    numbersBits ((L.path i).support.map Fin.val)))

/-- A returned path list is checked against actual graph paths. Padding is allowed
for fixed-width circuit outputs; the leading tag separates infeasibility. -/
def LegalOutput {n k : ℕ} (I : RoutingInput n k) (out : List Bool) : Prop :=
  out.head? = some false ∨ ∃ L : Linkage I, L.bits.IsPrefix out

def CorrectOutput {n k : ℕ} (I : RoutingInput n k) (out : List Bool) : Prop :=
  (IsEmpty (Linkage I) ∧ out.head? = some false) ∨
    ∃ L : Linkage I, L.IsOptimal ∧ L.bits.IsPrefix out

/-- A three-symbol tape, with a blank distinct from both bit symbols. -/
abbrev BitSymbol := Option Bool

structure BitTape where
  left : List BitSymbol
  right : List BitSymbol

def BitTape.read (t : BitTape) : BitSymbol := t.right.headD none

def BitTape.write (t : BitTape) (x : BitSymbol) : BitTape :=
  { t with right := x :: t.right.drop 1 }

inductive HeadMove | left | stay | right
  deriving DecidableEq

def BitTape.move (t : BitTape) : HeadMove → BitTape
  | .stay => t
  | .left => ⟨t.left.drop 1, t.left.headD none :: t.right⟩
  | .right => ⟨t.read :: t.left, t.right.drop 1⟩

/-- Each transition reads one independent bit. It can ignore it for a deterministic
step. One transition reads the input and work cells, writes one cell per work tape, moves each
head at most one cell, and appends at most one output bit. There is no arithmetic
or polynomial-query instruction. The program fixes a finite number of work tapes;\nthis standard fixed-tape transition has constant bit cost. -/
structure BitAction (q tapes : ℕ) where
  next : Fin q
  write : Fin tapes → BitSymbol
  inputMove : HeadMove
  workMove : Fin tapes → HeadMove
  output : Option Bool

structure BitProgram where
  workTapes : ℕ
  states : ℕ
  start : Fin states
  instruction : Fin states → BitSymbol → (Fin workTapes → BitSymbol) → Bool → Option (BitAction states workTapes)

structure BitConfiguration (P : BitProgram) where
  state : Fin P.states
  input : BitTape
  work : Fin P.workTapes → BitTape
  output : List Bool
  halted : Bool

def BitProgram.initial (P : BitProgram) (input : List Bool) : BitConfiguration P :=
  ⟨P.start, ⟨[], input.map some⟩, (fun _ => ⟨[], []⟩), [], false⟩

def BitProgram.step (P : BitProgram) (c : BitConfiguration P) (randomBit : Bool) :
    BitConfiguration P :=
  if c.halted then c else
  match P.instruction c.state c.input.read (fun j => (c.work j).read) randomBit with
  | none => { c with halted := true }
  | some a => ⟨a.next, c.input.move a.inputMove,
      (fun j => ((c.work j).write (a.write j)).move (a.workMove j)),
      c.output ++ a.output.toList, false⟩

def BitProgram.run (P : BitProgram) (input tape : List Bool) : ℕ → BitConfiguration P
  | 0 => P.initial input
  | t + 1 => P.step (P.run input tape t) (tape[t]?.getD false)

/-- The finite law is exactly independent unbiased bits, counted with multiplicity.
Every tape has length T, so no execution within T reads a default random bit. -/
noncomputable def bitProbability (T : ℕ) (event : (Fin T → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card (Fin T → Bool)

/-- Actual bounded execution: all tapes halt, all outputs validate, and the
specified fraction of tapes return an optimum or correct infeasibility. -/
def ExecutesSearch {n k : ℕ} (P : BitProgram) (I : RoutingInput n k)
    (input : List Bool) (T : ℕ) (success : ℝ) : Prop :=
  (∀ tape : Fin T → Bool,
    let c := P.run input (List.ofFn tape) T
    c.halted = true ∧ LegalOutput I c.output) ∧
  success ≤ bitProbability T (fun tape =>
    CorrectOutput I (P.run input (List.ofFn tape) T).output)

/-- All operations have bounded fan-in; sources are inputs or earlier gates. -/
inductive BooleanGate
  | input (i : ℕ)
  | constant (b : Bool)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  | disj (i j : ℕ)
  deriving DecidableEq

def BooleanGate.valid (inputs previous : ℕ) : BooleanGate → Prop
  | .input i => i < inputs
  | .constant _ => True
  | .neg i => i < previous
  | .conj i j | .disj i j => i < previous ∧ j < previous

def BooleanGate.value (input previous : List Bool) : BooleanGate → Bool
  | .input i => input[i]?.getD false
  | .constant b => b
  | .neg i => !(previous[i]?.getD false)
  | .conj i j => (previous[i]?.getD false) && (previous[j]?.getD false)
  | .disj i j => (previous[i]?.getD false) || (previous[j]?.getD false)

def BooleanGate.level (previous : List ℕ) : BooleanGate → ℕ
  | .input _ | .constant _ => 0
  | .neg i => previous[i]?.getD 0 + 1
  | .conj i j | .disj i j => max (previous[i]?.getD 0) (previous[j]?.getD 0) + 1

structure BooleanCircuit where
  inputs : ℕ
  gates : List BooleanGate
  outputs : List ℕ
  valid : ∀ i (h : i < gates.length), (gates[i]'h).valid inputs i
  outputs_valid : ∀ i ∈ outputs, i < gates.length

def BooleanCircuit.eval (C : BooleanCircuit) (input : List Bool) : List Bool :=
  let values := C.gates.foldl (fun values g => values ++ [g.value input values]) []
  C.outputs.map (fun i => values[i]?.getD false)

def BooleanCircuit.size (C : BooleanCircuit) : ℕ := C.inputs + C.gates.length + C.outputs.length

def BooleanCircuit.depth (C : BooleanCircuit) : ℕ :=
  let levels := C.gates.foldl (fun levels g => levels ++ [g.level levels]) []
  (C.outputs.map (fun i => levels[i]?.getD 0)).foldl max 0

def BooleanGate.code : BooleanGate → List ℕ
  | .input i => [0, i]
  | .constant b => [1, if b then 1 else 0]
  | .neg i => [2, i]
  | .conj i j => [3, i, j]
  | .disj i j => [4, i, j]

def BooleanCircuit.bits (C : BooleanCircuit) : List Bool :=
  numberBits C.inputs ++ numberBits C.gates.length ++
  C.gates.flatMap (fun g => numbersBits g.code) ++ numbersBits C.outputs

def logEnvelope (n : ℕ) : ℕ := Nat.clog 2 (max 2 n)

/-- A real logspace generator outputs the full finite circuit description from
unary length. Read-only input and write-only output are excluded from work space.
Its random tape is fixed to zero. No circuit correctness is a field. -/
structure UniformCircuitFamily where
  circuit : ℕ → BooleanCircuit
  generator : BitProgram

/-- Actual generation and work-space bounds, to be established as conclusions. -/
def LogspaceUniform (F : UniformCircuitFamily) (coefficient exponent : ℕ) : Prop :=
  0 < coefficient ∧ ∀ n,
    let T := coefficient * (max 2 n) ^ exponent
    (F.generator.run (List.replicate n true) [] T).halted = true ∧
    (F.generator.run (List.replicate n true) [] T).output = (F.circuit n).bits ∧
    ∀ t ≤ T,
      let work := (F.generator.run (List.replicate n true) [] t).work
      (∑ j : Fin F.generator.workTapes, ((work j).left.length + (work j).right.length)) ≤ coefficient * logEnvelope n

/-- Circuit inputs consist of a fixed-width data prefix followed by fair bits.
Correctness and the size/depth bounds remain theorem conclusions. -/
structure RandomCircuitFamily where
  uniform : UniformCircuitFamily
  dataCoefficient : ℕ
  dataExponent : ℕ
  enoughInputs : ∀ n,
    dataCoefficient * (max 2 n) ^ dataExponent ≤ (uniform.circuit n).inputs

/-- The deterministic/random input partition is uniformly computable. A free
size-dependent split could otherwise encode nonuniform advice. -/
def RandomCircuitFamily.dataWidth (F : RandomCircuitFamily) (n : ℕ) : ℕ :=
  F.dataCoefficient * (max 2 n) ^ F.dataExponent

def RandomCircuitFamily.randomWidth (F : RandomCircuitFamily) (n : ℕ) : ℕ :=
  (F.uniform.circuit n).inputs - F.dataWidth n

def RandomCircuitFamily.ExecutesSearch {n k : ℕ} (F : RandomCircuitFamily)
    (I : RoutingInput n k) (input : List Bool) (success : ℝ) : Prop :=
  input.length ≤ F.dataWidth n ∧
  (∀ tape : Fin (F.randomWidth n) → Bool,
    LegalOutput I ((F.uniform.circuit n).eval
      (input ++ List.replicate (F.dataWidth n - input.length) false ++ List.ofFn tape))) ∧
  success ≤ bitProbability (F.randomWidth n) (fun tape =>
    CorrectOutput I ((F.uniform.circuit n).eval
      (input ++ List.replicate (F.dataWidth n - input.length) false ++ List.ofFn tape)))

end ShortestPlanarDisjoint.Main


