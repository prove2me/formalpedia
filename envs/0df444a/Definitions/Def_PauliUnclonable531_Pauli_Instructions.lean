-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Instructions
-- name    : PauliUnclonable531_Pauli_Instructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:57.013176+00:00
-- url     : https://prove2.me/theorems/1db1f3f4-ef47-4645-bef3-1c8ac19c368e
-- title:
--   Local encryption and measurement instructions with semantics
-- statement:
--   The instruction language implements the actual procedures of Section 3.1. Its quantum primitives have the matrices X,H,S and local Pauli projectors. A scan retains the least active key position j*. Encryption draws a distinct fair bit at each other position, loads the message bit, adds the active sampled bits modulo two, stores the result at j*, prepares each computational basis qubit using conditional X, then applies H and optionally S at the sites specified by the key. A uniformly distributed tape fixes its unused j* coordinate to zero; every other coordinate is independent and fair.
--
--   $$\operatorname{Enc}_{\rm op}(k,m)=\frac1{|\mathcal R_k|}\sum_{r\in\mathcal R_k}\operatorname{executeEnc}(k,m;r).$$
--
--   The interpreter starts at |0ⁿ⟩⟨0ⁿ| and conjugates by each single-wire gate. Decryption emits only nonidentity local measurements, sums their unnormalized projective-instrument branches, and returns the parity of the outcome bits. It applies to arbitrary entangled input states.
--
--   The fair-bit, basis-preparation, and gate counts are computed from the emitted list. Classical cost charges ten times (n+1) address bits per visited scan site or emitted/executed instruction, including generation and parity processing. The scan and list constructors are uniform in n and the key; matrix entries describe semantics, not unit-cost matrix operations. No correctness or cost bound is a field.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), §2.1, p.11; §3.1, pp.16–17

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Scheme

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Operational syntax for §3.1: wires are numbered 0,…,n−1. H and S are
single-qubit Clifford generators; basis preparation is conditional X on a fresh |0⟩. -/
inductive Gate where
  | X | H | S
  deriving DecidableEq

noncomputable def gateMatrix : Gate → Op (Fin 2)
  | .X => QMaxCutSDP.Rounding.pauli 1
  | .H => ((Real.sqrt 2 : ℂ))⁻¹ • !![1,1;1,-1]
  | .S => !![1,0;0,Complex.I]

/-- One local gate acting on an arbitrary, possibly entangled n-qubit state. -/
def onWire {n : ℕ} (j : Fin n) (M : Op (Fin 2)) : Op (Bits n) :=
  fun x y => ∏ i, if i = j then M (x i) (y i) else if x i = y i then 1 else 0

def basisDensity {n : ℕ} (r : Bits n) : Op (Bits n) :=
  fun x y => if x = r ∧ y = r then 1 else 0

/-- Scan the whole key from left to right, retaining its first nonidentity position. -/
def pivot {n : ℕ} (k : Key n) : Option (Fin n) :=
  (List.finRange n).foldl (fun p j =>
    match p with
    | some i => some i
    | none => if active k.val j then some j else none) none

abbrev Tape {n : ℕ} (k : Key n) := {r : Bits n // ∀ j, pivot k = some j → r j = 0}

inductive EncInstruction (n : ℕ) where
  | fair : Fin n → EncInstruction n
  | loadMessage : EncInstruction n
  | xorBit : Fin n → EncInstruction n
  | storePivot : EncInstruction n
  | prepare : Fin n → EncInstruction n
  | gate : Fin n → Gate → EncInstruction n
  deriving DecidableEq

structure EncState (n : ℕ) where
  bits : Bits n
  parity : Fin 2
  quantum : Op (Bits n)

/-- Each fair instruction reads a distinct coordinate of a uniformly distributed tape.
The excluded pivot coordinate does not consume a coin. -/
noncomputable def encStep {n : ℕ} (p : Option (Fin n)) (m : Fin 2) (tape : Bits n)
    (s : EncState n) : EncInstruction n → EncState n
  | .fair j => {s with bits := Function.update s.bits j (tape j)}
  | .loadMessage => {s with parity := m}
  | .xorBit j => {s with parity := s.parity + s.bits j}
  | .storePivot => match p with
      | none => s
      | some j => {s with bits := Function.update s.bits j s.parity}
  | .prepare j =>
      let U := onWire j (if s.bits j = 0 then 1 else gateMatrix .X)
      {s with quantum := U * s.quantum * U.conjTranspose}
  | .gate j g =>
      let U := onWire j (gateMatrix g)
      {s with quantum := U * s.quantum * U.conjTranspose}

/-- Generated code: the key scan computes the pivot once, then samples, computes parity,
prepares the basis vector, and applies H followed by S when appropriate (p.16). -/
def encProgram {n : ℕ} (k : Key n) : List (EncInstruction n) :=
  let js := List.finRange n
  let p := pivot k
  let others := js.filter (fun j => some j ≠ p)
  others.map EncInstruction.fair ++ [.loadMessage] ++
    (others.filter (active k.val)).map EncInstruction.xorBit ++ [.storePivot] ++
    js.map EncInstruction.prepare ++ js.flatMap (fun j =>
      if k.val.1 j = 0 then [] else
        [.gate j .H] ++ if k.val.2 j = 0 then [] else [.gate j .S])

noncomputable def executeEnc {n : ℕ} (k : Key n) (m : Fin 2) (tape : Tape k) : Op (Bits n) :=
  ((encProgram k).foldl (encStep (pivot k) m tape.val) ⟨0,0,basisDensity 0⟩).quantum

noncomputable def operationalEnc {n : ℕ} (k : Key n) (m : Fin 2) : Op (Bits n) :=
  (Fintype.card (Tape k) : ℂ)⁻¹ • ∑ tape : Tape k, executeEnc k m tape

/-- Number of actual emitted random draws, basis preparations, and H/S gates. -/
def fairCount {n : ℕ} (p : List (EncInstruction n)) : ℕ :=
  (p.filter fun i => match i with | .fair _ => true | _ => false).length

def preparationCount {n : ℕ} (p : List (EncInstruction n)) : ℕ :=
  (p.filter fun i => match i with | .prepare _ => true | _ => false).length

def gateCount {n : ℕ} (p : List (EncInstruction n)) : ℕ :=
  (p.filter fun i => match i with | .gate _ _ => true | _ => false).length

/-- Classical bit-cost model: each wire address is stored in n+1 bits. A scan or code
emission handles a constant number of bits/addresses per visited site; each executed
instruction handles a constant number of bits/addresses. Quantum primitives are charged
separately. The conservative factor 10 covers those fixed operations, not a matrix evaluation. -/
def encBitCost {n : ℕ} (k : Key n) : ℕ :=
  10 * (n+1) * ((List.finRange n).length + (encProgram k).length + 1)

/-- Sequential local Pauli-measurement instruction. No global measurement is primitive. -/
structure DecInstruction (n : ℕ) where
  wire : Fin n
  label : Fin 4

def decProgram {n : ℕ} (k : Key n) : List (DecInstruction n) :=
  ((List.finRange n).filter (active k.val)).map
    (fun j => ⟨j, localLabel (k.val.1 j) (k.val.2 j)⟩)

/-- Projective instrument of a local Pauli, with signed outcome (−1)^b. -/
noncomputable def localProjector {n : ℕ} (i : DecInstruction n) (b : Fin 2) : Op (Bits n) :=
  onWire i.wire ((1/2 : ℂ) • (1 + sign b • QMaxCutSDP.Rounding.pauli i.label))

/-- Born semantics: unnormalized post-measurement states retain their branch probability.
The classical parity register adds outcome bits mod 2. This applies to entangled inputs. -/
noncomputable def executeDec {n : ℕ} : List (DecInstruction n) → Op (Bits n) → Fin 2 → Fin 2 → ℝ
  | [], σ, parity, target => if parity = target then σ.trace.re else 0
  | i :: rest, σ, parity, target => ∑ b : Fin 2,
      executeDec rest (localProjector i b * σ * (localProjector i b).conjTranspose)
        (parity + b) target

noncomputable def operationalDec {n : ℕ} (k : Key n) (σ : Op (Bits n)) (b : Fin 2) : ℝ :=
  executeDec (decProgram k) σ 0 b

def decBitCost {n : ℕ} (k : Key n) : ℕ :=
  10 * (n+1) * ((List.finRange n).length + 2 * (decProgram k).length + 1)

end PauliUnclonable531.Pauli


