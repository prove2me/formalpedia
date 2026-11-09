-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Circuits
-- name    : AlmostLinearModComp_Composition_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:59.814782+00:00
-- url     : https://prove2.me/theorems/d75f6abd-e317-440a-a1a2-45025753354c
-- title:
--   Division-free arithmetic circuits and fixed-scalar linear programs
-- statement:
--   A division-free arithmetic circuit is a finite list of additions, subtractions and multiplications, with input wires, integer-constant wires, and references to earlier gates. Its interpreter executes every listed operation in order and returns every selected output wire. Its ring-operation cost is the number of gates. Validity requires the declared input and output dimensions and forbids forward references.
--
--   A linear straight-line program starts from its variable inputs and zero, and permits addition, subtraction and multiplication by entries of a separate fixed scalar list. The scalar list is independent of the variable inputs. Every scalar multiplication costs one operation. These two program types separate algebraic computation from its semantic specification and provide reusable models for the complexity statements. Invalid wire accesses have a total default value of zero, but theorem statements require valid programs.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §1.1 and final proof of Theorem 1.1, printed pp.1,8 / PDF pp.2,9; §A.2, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Mathlib

namespace AlmostLinearModComp.Composition

/-- Division-free wire syntax; integer constants are interpreted by the ring's canonical map. -/
inductive Wire where
  | input : ℕ → Wire
  | integer : ℤ → Wire
  | gate : ℕ → Wire
  deriving DecidableEq, Repr

/-- Each constructor executes exactly one ring operation. -/
inductive RingGate where
  | add : Wire → Wire → RingGate
  | sub : Wire → Wire → RingGate
  | mul : Wire → Wire → RingGate
  deriving DecidableEq, Repr

structure Circuit where
  gates : List RingGate
  outputs : List Wire
  deriving DecidableEq, Repr

def Wire.valid (inputs previous : ℕ) : Wire → Prop
  | .input i => i < inputs
  | .integer _ => True
  | .gate j => j < previous

def RingGate.valid (inputs previous : ℕ) : RingGate → Prop
  | .add a b | .sub a b | .mul a b => a.valid inputs previous ∧ b.valid inputs previous

/-- No forward references, no missing inputs, and no unavailable output wires. -/
def Circuit.valid (c : Circuit) (inputs outputs : ℕ) : Prop :=
  (∀ i : Fin c.gates.length, (c.gates[i]).valid inputs i.val) ∧
  c.outputs.length = outputs ∧
  ∀ w ∈ c.outputs, w.valid inputs c.gates.length

def Wire.eval {R : Type*} [CommRing R] (input previous : List R) : Wire → R
  | .input i => input[i]?.getD 0
  | .integer z => z
  | .gate j => previous[j]?.getD 0

def RingGate.eval {R : Type*} [CommRing R] (input previous : List R) : RingGate → R
  | .add a b => a.eval input previous + b.eval input previous
  | .sub a b => a.eval input previous - b.eval input previous
  | .mul a b => a.eval input previous * b.eval input previous

/-- Sequential execution actually evaluates every gate, in list order. -/
def Circuit.eval {R : Type*} [CommRing R] (c : Circuit) (input : List R) : List R :=
  let inp := input.toArray
  let read := fun (previous : Array R) (w : Wire) => match w with
    | .input i => inp[i]?.getD 0
    | .integer z => (z : R)
    | .gate i => previous[i]?.getD 0
  let values := c.gates.foldl (fun previous g =>
    let value := match g with
      | .add a b => read previous a + read previous b
      | .sub a b => read previous a - read previous b
      | .mul a b => read previous a * read previous b
    previous.push value) #[]
  c.outputs.map (read values)

def Circuit.cost (c : Circuit) : ℕ := c.gates.length

/-- Variable wires for a linear program; the only freely available constant is zero. -/
inductive LinearWire where
  | zero : LinearWire
  | input : ℕ → LinearWire
  | gate : ℕ → LinearWire
  deriving DecidableEq, Repr

/-- Scalar indices refer to a fixed scalar table, shared with the transposed program. -/
inductive LinearGate where
  | add : LinearWire → LinearWire → LinearGate
  | sub : LinearWire → LinearWire → LinearGate
  | scale : ℕ → LinearWire → LinearGate
  deriving DecidableEq, Repr

structure LinearProgram where
  gates : List LinearGate
  outputs : List LinearWire
  deriving DecidableEq, Repr

def LinearWire.valid (inputs previous : ℕ) : LinearWire → Prop
  | .zero => True
  | .input i => i < inputs
  | .gate j => j < previous

def LinearGate.valid (scalars inputs previous : ℕ) : LinearGate → Prop
  | .add a b | .sub a b => a.valid inputs previous ∧ b.valid inputs previous
  | .scale k a => k < scalars ∧ a.valid inputs previous

def LinearProgram.valid (p : LinearProgram) (scalars inputs outputs : ℕ) : Prop :=
  (∀ i : Fin p.gates.length, (p.gates[i]).valid scalars inputs i.val) ∧
  p.outputs.length = outputs ∧
  ∀ w ∈ p.outputs, w.valid inputs p.gates.length

def LinearWire.eval {R : Type*} [CommRing R] (input previous : List R) : LinearWire → R
  | .zero => 0
  | .input i => input[i]?.getD 0
  | .gate j => previous[j]?.getD 0

def LinearGate.eval {R : Type*} [CommRing R] (scalars input previous : List R) : LinearGate → R
  | .add a b => a.eval input previous + b.eval input previous
  | .sub a b => a.eval input previous - b.eval input previous
  | .scale k a => scalars[k]?.getD 0 * a.eval input previous

def LinearProgram.eval {R : Type*} [CommRing R]
    (p : LinearProgram) (scalars input : List R) : List R :=
  let inp := input.toArray
  let fixed := scalars.toArray
  let read := fun (previous : Array R) (w : LinearWire) => match w with
    | .zero => 0
    | .input i => inp[i]?.getD 0
    | .gate i => previous[i]?.getD 0
  let values := p.gates.foldl (fun previous g =>
    let value := match g with
      | .add a b => read previous a + read previous b
      | .sub a b => read previous a - read previous b
      | .scale k a => fixed[k]?.getD 0 * read previous a
    previous.push value) #[]
  p.outputs.map (read values)

def LinearProgram.cost (p : LinearProgram) : ℕ := p.gates.length

/-- Dense multiplication is a semantic specification, not a gate or an uncharged circuit routine. -/
def matrixAction {R : Type*} [CommRing R] {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) R) (x : Fin s → R) : List R :=
  List.ofFn fun i => ∑ j, A i j * x j

end AlmostLinearModComp.Composition


