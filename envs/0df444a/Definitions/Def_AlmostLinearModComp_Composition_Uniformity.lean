-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Uniformity
-- name    : AlmostLinearModComp_Composition_Uniformity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:41.706855+00:00
-- url     : https://prove2.me/theorems/d74ce599-e8a2-454b-abc1-dd27e5a895f9
-- title:
--   Bit-machine generation of integer-constant circuits
-- statement:
--   A finite-state deterministic machine reads and writes one symbol on a single tape per step and moves one cell. The three symbols are blank, binary zero and binary one. Its input is the size parameter in unary. A successful generation run halts and leaves the complete self-delimiting binary circuit description to the right of a blank head, including every gate, wire index and integer constant.
--
--   The predicate $\operatorname{GeneratesCircuit}(M,n,T,c)$ asserts that such a run finishes within $T$ elementary tape transitions and writes exactly circuit $c$. It does not assert anything about circuit correctness or ring-operation cost. Binary lengths and integer signs are encoded explicitly. Polynomial time in unary $n$ is polynomial time in the numerical degree parameter, as in the source's circuit-construction claim; it is distinct from the algebraic gate count.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), proof of Theorem 1.1, last paragraph, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Circuits

namespace AlmostLinearModComp.Composition

/-- Self-delimiting binary natural: unary bit length, separator, then little-endian bits. -/
def natWord (n : ℕ) : List Bool :=
  let digits := (Nat.digits 2 n).map (fun i => i == 1)
  List.replicate digits.length true ++ [false] ++ digits

def intWord (z : ℤ) : List Bool := (z < 0) :: natWord z.natAbs

def Wire.word : Wire → List Bool
  | .input n => [false, false] ++ natWord n
  | .integer z => [false, true] ++ intWord z
  | .gate n => [true, false] ++ natWord n

def RingGate.word : RingGate → List Bool
  | .add a b => [false, false] ++ a.word ++ b.word
  | .sub a b => [false, true] ++ a.word ++ b.word
  | .mul a b => [true, false] ++ a.word ++ b.word

def Circuit.word (c : Circuit) : List Bool :=
  natWord c.gates.length ++ c.gates.flatMap RingGate.word ++
    natWord c.outputs.length ++ c.outputs.flatMap Wire.word

/-- Three tape symbols: blank, binary zero, binary one. -/
abbrev TapeSymbol := Fin 3

/-- An ordinary finite-state, one-tape deterministic machine. No arithmetic or output oracle. -/
structure CircuitMachine where
  states : ℕ
  start : Fin states
  transition : Fin states → TapeSymbol → Option (Fin states × TapeSymbol × Bool)

structure MachineConfiguration (M : CircuitMachine) where
  state : Option (Fin M.states)
  left : List TapeSymbol
  head : TapeSymbol
  right : List TapeSymbol

/-- A transition reads/writes one symbol and moves one cell (true = right). -/
def machineStep (M : CircuitMachine) (c : MachineConfiguration M) : MachineConfiguration M :=
  match c.state with
  | none => c
  | some s => match M.transition s c.head with
    | none => { c with state := none }
    | some (s', write, direction) =>
      if direction then
        { state := some s', left := write :: c.left,
          head := c.right.headD 0, right := c.right.drop 1 }
      else
        { state := some s', left := c.left.drop 1,
          head := c.left.headD 0, right := write :: c.right }

/-- Unary size input: a blank head followed by n ones, with blanks elsewhere. -/
def initialConfiguration (M : CircuitMachine) (n : ℕ) : MachineConfiguration M :=
  { state := some M.start, left := [], head := 0, right := List.replicate n 2 }

def machineRun (M : CircuitMachine) (n : ℕ) : ℕ → MachineConfiguration M
  | 0 => initialConfiguration M n
  | t + 1 => machineStep M (machineRun M n t)

def bitSymbol (b : Bool) : TapeSymbol := if b then 2 else 1

/-- A witnessed run, bounded in elementary tape transitions, writes the entire circuit,
including all bits of its integer constants, immediately to the right of a blank head. -/
def GeneratesCircuit (M : CircuitMachine) (n time : ℕ) (c : Circuit) : Prop :=
  ∃ t ≤ time, (machineRun M n t).state = none ∧
    (machineRun M n t).head = 0 ∧
    (machineRun M n t).right = c.word.map bitSymbol

end AlmostLinearModComp.Composition


