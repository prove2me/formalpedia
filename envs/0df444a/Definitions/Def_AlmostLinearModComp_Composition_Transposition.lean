-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Transposition
-- name    : AlmostLinearModComp_Composition_Transposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:41.123199+00:00
-- url     : https://prove2.me/theorems/dbb4653d-ab55-44b4-823c-b192b35a33a1
-- title:
--   Reverse accumulation and truncated coefficient-block transposition
-- statement:
--   The reverse-accumulation compiler seeds the selected output wires with new variable inputs, visits the original gates in reverse order, and accumulates their contributions to the original input wires. Addition propagates to both operands, subtraction changes the contribution to the second operand, and a scalar multiplication reuses the original scalar index. Every accumulation and multiplication creates a counted linear gate. The compiler takes the program and its input dimension, and never takes a matrix or scalar values.
--
--   For matrices over $R[t]/(t^q)$, a second wrapper reverses each input block of $q$ coefficients, applies the transposed coefficient program, and reverses each output block. The coefficient-map specification uses truncated convolution with coordinate-major coefficient blocks. These explicit wire permutations add no ring operations. The correctness and cost assertions are the open theorem Lemma A.2, rather than fields of these definitions.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §A.2, Lemma A.2 and following paragraph, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Circuits

namespace AlmostLinearModComp.Composition

/-- Syntactic reverse accumulation state; entries are wires, never ring values. -/
structure AdjointBuilder where
  gates : List LinearGate
  inputAdjoint : ℕ → LinearWire
  gateAdjoint : ℕ → LinearWire

def AdjointBuilder.accumulate (b : AdjointBuilder) (target value : LinearWire)
    (subtract : Bool := false) : AdjointBuilder :=
  let old := match target with
    | .zero => LinearWire.zero
    | .input i => b.inputAdjoint i
    | .gate i => b.gateAdjoint i
  let op := if subtract then LinearGate.sub old value else LinearGate.add old value
  let wire := LinearWire.gate b.gates.length
  match target with
  | .zero => b
  | .input i =>
    { b with gates := b.gates ++ [op], inputAdjoint := Function.update b.inputAdjoint i wire }
  | .gate i =>
    { b with gates := b.gates ++ [op], gateAdjoint := Function.update b.gateAdjoint i wire }

def reverseLinearGate (b : AdjointBuilder) (g : LinearGate) (i : ℕ) : AdjointBuilder :=
  let value := b.gateAdjoint i
  match g with
  | .add a d => (b.accumulate a value).accumulate d value
  | .sub a d => (b.accumulate a value).accumulate d value true
  | .scale k a =>
    let b' := { b with gates := b.gates ++ [LinearGate.scale k value] }
    b'.accumulate a (.gate b.gates.length)

/-- Reverse-mode transposition. It reads the program, not its matrix, and reuses scalar
indices without introducing any new scalar constants. All accumulation is charged. -/
def transposeProgram (p : LinearProgram) (inputs : ℕ) : LinearProgram :=
  let initial : AdjointBuilder :=
    { gates := []
      inputAdjoint := fun _ => .zero
      gateAdjoint := fun _ => .zero }
  let seeded := p.outputs.zipIdx.foldl
    (fun b wi => b.accumulate wi.1 (.input wi.2)) initial
  let final := p.gates.zipIdx.reverse.foldl
    (fun b gi => reverseLinearGate b gi.1 gi.2) seeded
  { gates := final.gates, outputs := List.ofFn fun i : Fin inputs => final.inputAdjoint i }

/-- Flattened coefficient map with coordinate-major q-coefficient blocks. -/
noncomputable def coefficientAction {R : Type*} [CommRing R] {r s : ℕ}
    (q : ℕ) (A : Matrix (Fin r) (Fin s) (Polynomial R))
    (x : Fin s → Fin q → R) : List R :=
  (List.ofFn fun i : Fin r => List.ofFn fun t : Fin q =>
    ∑ j : Fin s, ∑ k : Fin q,
      if k.val ≤ t.val then (A i j).coeff (t.val - k.val) * x j k else 0).flatten

/-- A pure wire permutation; this creates no arithmetic gates. -/
def reverseBlockIndex (q i : ℕ) : ℕ := (i / q) * q + (q - 1 - i % q)

def reverseInputWire (q : ℕ) : LinearWire → LinearWire
  | .input i => .input (reverseBlockIndex q i)
  | w => w

def reverseInputGate (q : ℕ) : LinearGate → LinearGate
  | .add a b => .add (reverseInputWire q a) (reverseInputWire q b)
  | .sub a b => .sub (reverseInputWire q a) (reverseInputWire q b)
  | .scale k a => .scale k (reverseInputWire q a)

/-- Appendix A.2: reverse q-coefficient input blocks, apply the R-linear
transpose, and reverse each output block. No matrix or new scalar is supplied. -/
def transposeTruncated (p : LinearProgram) (s q : ℕ) : LinearProgram :=
  let tp := transposeProgram p (s * q)
  { gates := tp.gates.map (reverseInputGate q)
    outputs := (List.range s).flatMap (fun i => (tp.outputs.drop (i * q)).take q |>.reverse) }

end AlmostLinearModComp.Composition


