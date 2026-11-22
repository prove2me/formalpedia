-- Prove2me | Definitions.Def_ShiShallow_Core
-- name    : ShiShallow_Core
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-10T02:44:50.958737+00:00
-- url     : https://prove2.me/theorems/a00fc34f-6c22-4f3d-a52d-ad5eed3a8d5a
-- title:
--   Shallow layered quantum circuits and their causal cones
-- statement:
--   Foundational definitions for reasoning about **shallow layered quantum circuits** and their causal (light) cones.
--
--   A circuit acts on $n$ wires whose basis states are bit strings $x \in \{0,1\}^n$, represented as `Bits n := Fin n → Bool`; a quantum state is an amplitude vector `QState n := Bits n → ℂ`. The gate set consists of the Hadamard, phase, $T$ and bit-flip matrices together with CNOT, packaged as an inductive type `Instr n`, each instruction carrying a `support` — the set of wires it touches. A **layer** is a list of instructions and a circuit `Layered n` is a list of layers, so that `depth` is the number of layers. A layer is well formed (`LayerOk`) when its gates act on pairwise disjoint wires, which is what makes a layer physically simultaneous.
--
--   Dynamics are given by `runLayer` and `runLayered`, applying instructions in order. On the classical input $x$ padded with ancillas initialised to $0$ (`inputState`), the quantity `acceptProb` is the probability that a designated output wire is measured to be $1$, and `outDist` is the full distribution induced on basis strings.
--
--   The causal cone is defined backwards. For a set $S$ of wires, `coneStep l S` adjoins the support of every gate of the layer $l$ that meets $S$, and `coneOf c S` folds this backwards through the circuit. Note that `coneStep` tests each gate against the *incoming* set $S$ and not against the accumulator: for a well-formed layer no cascading within the layer can occur, and testing against the accumulator would strictly over-approximate the cone.

import Mathlib

namespace ShiShallow


/-! ## Gate layer (validated numerically against a tensor-product reference) -/

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev QState (n : ℕ) := Bits n → ℂ

noncomputable def hMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a && b then -(Real.sqrt 2)⁻¹ else (Real.sqrt 2)⁻¹

noncomputable def sMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then (if a then Complex.I else 1) else 0

noncomputable def tMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a = b then (if a then Complex.exp (Complex.I * Real.pi / 4) else 1) else 0

/-- The bit-flip gate. -/
noncomputable def xMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else 1

/-- One-qubit gate on wire `i`; equals `I ⊗ ⋯ ⊗ U ⊗ ⋯ ⊗ I` with `U`'s row index on the
output wire. -/
noncomputable def apply1 {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    QState n :=
  fun x => ∑ b : Bool, U (x i) b * ψ (Function.update x i b)

/-- CNOT with control `i`, target `j`. Only a permutation when `i ≠ j`; `cnotState i i` is a
rank-deficient reset map, so every lemma about it must carry that hypothesis. -/
def cnotState {n : ℕ} (i j : Fin n) (_hij : i ≠ j) (ψ : QState n) : QState n :=
  fun x => ψ (Function.update x j (xor (x j) (x i)))

inductive Instr (n : ℕ) where
  | h (i : Fin n)
  | s (i : Fin n)
  | t (i : Fin n)
  | x (i : Fin n)
  | cnot (i j : Fin n) (hij : i ≠ j)

noncomputable def Instr.apply {n : ℕ} : Instr n → QState n → QState n
  | .h i => apply1 hMat i
  | .s i => apply1 sMat i
  | .t i => apply1 tMat i
  | .x i => apply1 xMat i
  | .cnot i j hij => cnotState i j hij

/-- The wires an instruction touches. -/
def Instr.support {n : ℕ} : Instr n → Finset (Fin n)
  | .h i => {i}
  | .s i => {i}
  | .t i => {i}
  | .x i => {i}
  | .cnot i j _ => {i, j}

/-! ## Layers, depth, and causal cones -/

/-- A layered circuit: a list of layers, each a list of instructions. -/
abbrev Layered (n : ℕ) := List (List (Instr n))

/-- Depth is the number of layers. -/
def depth {n : ℕ} (c : Layered n) : ℕ := c.length

/-- A layer is well-formed when its gates act on pairwise disjoint wires — without this the
doubling bound below is false. -/
def LayerOk {n : ℕ} (l : List (Instr n)) : Prop :=
  l.Pairwise fun a b => Disjoint a.support b.support

noncomputable def runLayer {n : ℕ} (l : List (Instr n)) (ψ : QState n) : QState n :=
  l.foldl (fun st g => g.apply st) ψ

noncomputable def runLayered {n : ℕ} (c : Layered n) (ψ : QState n) : QState n :=
  c.foldl (fun st l => runLayer l st) ψ

def inputState {n m : ℕ} (x : Bits n) : QState (n + m) :=
  fun y => if (∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧ (∀ k : Fin m, y (Fin.natAdd n k) = false)
           then 1 else 0

noncomputable def acceptProb {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) : ℝ :=
  ∑ y : Bits (n + m), if y out then ‖runLayered c (inputState x) y‖ ^ 2 else 0

/-- One backward step of the causal cone: adjoin the support of every gate in the layer that
touches `S`. -/
def coneStep {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  l.foldr (fun g acc => if (g.support ∩ S).Nonempty then g.support ∪ acc else acc) S

/-- The causal cone of `S`, propagated backwards through the layers (the last layer acts on
`S` first). -/
def coneOf {n : ℕ} (c : Layered n) (S : Finset (Fin n)) : Finset (Fin n) :=
  c.foldr coneStep S

/-- The distribution the circuit induces on basis strings, for a given classical input. -/
noncomputable def outDist {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (y : Bits (n + m)) : ℝ :=
  ‖runLayered c (inputState x) y‖ ^ 2

end ShiShallow


