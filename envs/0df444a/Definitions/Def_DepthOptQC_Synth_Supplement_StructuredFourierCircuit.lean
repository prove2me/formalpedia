-- Prove2me | Definitions.Def_DepthOptQC_Synth_Supplement_StructuredFourierCircuit
-- name    : DepthOptQC_Synth_Supplement_StructuredFourierCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:46:41.601318+00:00
-- url     : https://prove2.me/theorems/44c466b4-bfbd-442d-af8a-bd2c77f60dd6
-- title:
--   Structured Boolean phase functions and structured Fourier circuits
-- statement:
--   A **structured phase function** is an affine Boolean function XORed with permitted nonlinear block functions on pairwise disjoint supports. The phase families $\mathcal A_3,\mathcal A,\mathcal T$ use bounded-AND, arbitrary-AND and Threshold blocks, respectively; $\mathcal A_{3,f},\mathcal A_f,\mathcal T_f$ additionally allow the controlled-Parity blocks induced by Fan-Out.
--
--   A **structured Fourier circuit** alternates partial Hadamard transforms and diagonal signs $(-1)^{h(z)}$ from one fixed phase family. It starts on $|x\rangle|0\cdots0\rangle$, has a designated output qubit, and its width, number of phase layers and finite syntax-description length are recorded.
--
--   These objects are the exact target representation of Theorem 15; in particular, disjointness is imposed between nonlinear blocks, not between the individual controlled-$Z$ factors inside one Fan-Out block.
--
--   **Formalization Note** Empty Hadamard subsets and the identity phase layer are allowed as in Definition 7.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Definition 4 p.11 and Definitions 5–8 pp.69–70 (PDF pp.13, 71–72), Eqs. (334)–(343)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

noncomputable section

namespace DepthOptQC.Synth.Supplement

open QAlgorithms
open scoped BigOperators

/-- The six structured phase families of Eqs. (336) and (339). -/
inductive PhaseFamily where | A3 | A | T | A3f | Af | Tf deriving DecidableEq

def xorFinset {α : Type*} (S : Finset α) (f : α → Bool) : Bool :=
  S.toList.foldl (fun b a => xor b (f a)) false

def andBlock {m : ℕ} (B : Finset (Fin m)) (z : Qubits m) : Bool := decide (∀ i ∈ B, z i)
def parityBlock {m : ℕ} (B : Finset (Fin m)) (z : Qubits m) : Bool := xorFinset B z

/-- The permitted nonlinear block functions in Table 2 and Eqs. (336), (338), (339). -/
def AllowedBlock {m : ℕ} (F : PhaseFamily) (B : Finset (Fin m)) (g : Qubits m → Bool) : Prop :=
  let boundedAnd := 2 ≤ B.card ∧ B.card ≤ 3 ∧ g = andBlock B
  let anyAnd := 2 ≤ B.card ∧ g = andBlock B
  let threshold := ∃ t ∈ B, ∃ u : ℕ, 1 ≤ u ∧ u ≤ (B.erase t).card ∧
    ∀ z, g z = (z t && decide (u ≤ ((B.erase t).filter fun i => z i).card))
  let fanout := ∃ c ∈ B, (B.erase c).Nonempty ∧
    ∀ z, g z = (z c && parityBlock (B.erase c) z)
  match F with
  | .A3 => boundedAnd | .A => anyAnd | .T => threshold
  | .A3f => boundedAnd ∨ fanout | .Af => anyAnd ∨ fanout | .Tf => threshold ∨ fanout

/-- A structured phase function of Eq. (334): an affine Boolean phase plus permitted nonlinear
functions on pairwise disjoint blocks. -/
structure StructuredPhase (m : ℕ) (F : PhaseFamily) where
  constant : Bool
  linear : Fin m → Bool
  blocks : List (Finset (Fin m) × (Qubits m → Bool))
  disjoint : blocks.Pairwise (fun p q => Disjoint p.1 q.1)
  allowed : ∀ p ∈ blocks, AllowedBlock F p.1 p.2

def StructuredPhase.eval {m : ℕ} {F : PhaseFamily} (h : StructuredPhase m F)
    (z : Qubits m) : Bool :=
  xor h.constant (xor (xorFinset (Finset.univ.filter fun i => h.linear i) z)
    (h.blocks.foldl (fun b p => xor b (p.2 z)) false))

/-- A partial Hadamard transform on the wire subset `S`. -/
def partialHadamard (m : ℕ) (S : Finset (Fin m)) : Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.of fun y x =>
    if ∀ i, i ∉ S → y i = x i then
      (((Real.sqrt 2)⁻¹ ^ S.card : ℝ) : ℂ) *
        if xorFinset S (fun i => x i && y i) then -1 else 1
    else 0

def structuredPhaseMatrix {m : ℕ} {F : PhaseFamily} (h : StructuredPhase m F) :
    Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.diagonal fun z => if h.eval z then -1 else 1

def structuredFourierUnitaryAux {m : ℕ} {F : PhaseFamily} :
    List (Finset (Fin m)) → List (StructuredPhase m F) → Matrix (Qubits m) (Qubits m) ℂ
  | [S], [] => partialHadamard m S
  | S :: Ss, h :: hs => structuredFourierUnitaryAux Ss hs * structuredPhaseMatrix h * partialHadamard m S
  | _, _ => 0

/-- A structured Fourier decision circuit (Definitions 7–8, p.70). It is selected independently
of the input, alternates partial Hadamard layers with structured phase layers, starts on
`|x⟩|0...0⟩`, and has one designated output qubit. -/
structure StructuredFourierCircuit (F : PhaseFamily) (n : ℕ) where
  width : ℕ
  input_le_width : n ≤ width
  hadamards : List (Finset (Fin width))
  phases : List (StructuredPhase width F)
  alternating : hadamards.length = phases.length + 1
  output : Fin width

def StructuredFourierCircuit.unitary {F : PhaseFamily} {n : ℕ}
    (U : StructuredFourierCircuit F n) : Matrix (Qubits U.width) (Qubits U.width) ℂ :=
  structuredFourierUnitaryAux U.hadamards U.phases

def StructuredFourierCircuit.input {F : PhaseFamily} {n : ℕ}
    (U : StructuredFourierCircuit F n) (x : Qubits n) : EuclideanSpace ℂ (Qubits U.width) :=
  ket fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

def StructuredFourierCircuit.acceptance {F : PhaseFamily} {n : ℕ}
    (U : StructuredFourierCircuit F n) (x : Qubits n) : ℝ :=
  probEvent (act U.unitary (U.input x)) (fun z => z U.output)

def StructuredPhase.descriptionLength {m : ℕ} {F : PhaseFamily}
    (h : StructuredPhase m F) : ℕ :=
  1 + m + (h.blocks.map fun p => 1 + p.1.card).sum

/-- A concrete finite description-length count for the Hadamard subsets, affine coefficients,
block supports and designated output. -/
def StructuredFourierCircuit.descriptionLength {F : PhaseFamily} {n : ℕ}
    (U : StructuredFourierCircuit F n) : ℕ :=
  1 + (U.hadamards.map Finset.card).sum +
    (U.phases.map StructuredPhase.descriptionLength).sum

def widePhaseFamily : WideModel → PhaseFamily
  | .ac => .A | .acf => .Af | .tc => .T | .tcf => .Tf

/-- The three bounded-arity clauses in the second half of Theorem 15. -/
inductive BoundedFourierSource where | qunc | quncf | qncf deriving DecidableEq

def boundedSourceGateSet : BoundedFourierSource → Set Gate
  | .qunc => quncGateSet | .quncf => quncfGateSet | .qncf => qncfGateSet

def boundedSourcePhaseFamily : BoundedFourierSource → PhaseFamily
  | .qunc => .A3 | .quncf => .A3f | .qncf => .A3f

end DepthOptQC.Synth.Supplement


