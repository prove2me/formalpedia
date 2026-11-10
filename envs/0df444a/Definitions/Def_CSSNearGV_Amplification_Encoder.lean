-- Prove2me | Definitions.Def_CSSNearGV_Amplification_Encoder
-- name    : CSSNearGV_Amplification_Encoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:17:15.121222+00:00
-- url     : https://prove2.me/theorems/24bcddc0-987d-44c7-9891-b05010bf13d7
-- title:
--   Coherent encoder and unrestricted CNOT layer schedule
-- statement:
--   The outer encoder on each block maps a logical label to the normalized sum of the parity-completed label with final bit zero and its complement. Tensoring these encoders gives a linear map on arbitrary complex amplitudes. The initial register has $s-2$ data qubits, one zero ancilla and one plus ancilla per block.
--
--   The subsequent map acts on basis labels by $L$. Its operational circuit has free coordinate relabelings and layers of disjoint CNOT gates, placed using the published CNOT matrix. The recursively defined PREFIX schedule works in place on all blocklengths, including odd lengths; its reverse computes the derivative. The explicit outer schedule and alternating prefix schedules define the entire encoder.
--
--   Correctness requires equality on every complex input, preservation of every inner product, and equality of the encoder range with the whole CSS subspace. Its resource predicate requires
--   $$\operatorname{depth}\le2s-3+4m\lceil\log_2n\rceil,\qquad\#\mathrm{CNOT}\le\left(4m+\frac{2s-3}{s}\right)n.$$
--
--   No work qubits beyond the specified ancillas are added, and gates may join any distinct wires.
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Section 2.1, printed pp.5–6 / PDF 7–8

import Definitions.Def_CSSNearGV_Amplification_Ensemble
import Definitions.Def_DepthOneQExp_cnotGate

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification
attribute [local instance] Classical.propDecidable

abbrev State (n : ℕ) := Word n → ℂ

def bitAt {n : ℕ} (x : Word n) (i : ℕ) : Bit := if h : i < n then x ⟨i, h⟩ else 0

def outerWord (s b : ℕ) (x : Word ((s - 2) * b)) (z : Word b) : Word (s * b) :=
  fun i =>
    let j := i.val / s
    let r := i.val % s
    (if r < s - 2 then bitAt x (j * (s - 2) + r)
     else if r = s - 2 then ∑ t ∈ Finset.range (s - 2), bitAt x (j * (s - 2) + t)
     else 0) + bitAt z j

/-- Data, zero, plus register order inside each block, before any CNOT. -/
def inputWord (s b : ℕ) (x : Word ((s - 2) * b)) (z : Word b) : Word (s * b) :=
  fun i =>
    if i.val % s < s - 2 then bitAt x (i.val / s * (s - 2) + i.val % s)
    else if i.val % s = s - 1 then bitAt z (i.val / s) else 0

def prepare (s b : ℕ) (ψ : State ((s - 2) * b)) : State (s * b) :=
  fun y => (Real.sqrt ((2 : ℝ) ^ b) : ℂ)⁻¹ *
    ∑ x : Word ((s - 2) * b), ∑ z : Word b, if inputWord s b x z = y then ψ x else 0

/-- Linear extension of the displayed coset encoder followed by U_L. -/
def encode (s b m : ℕ) (π : Perms (s * b) m) (ψ : State ((s - 2) * b)) : State (s * b) :=
  fun y => (Real.sqrt ((2 : ℝ) ^ b) : ℂ)⁻¹ *
    ∑ x : Word ((s - 2) * b), ∑ z : Word b,
      if (amplifier true π).mulVec (outerWord s b x z) = y then ψ x else 0

def publishedState {n : ℕ} (ψ : State n) : EuclideanSpace ℂ (QAlgorithms.Qubits n) :=
  ∑ x : Word n, ψ x • QAlgorithms.ket (QAlgorithms.bitsOfZMod x)

/-- Wire relabelings are free; a layer contains pairwise disjoint two-wire gates. -/
inductive CircuitStep (n : ℕ)
  | relabel : Equiv.Perm (Fin n) → CircuitStep n
  | layer : List (ℕ × ℕ) → CircuitStep n

abbrev Circuit (n : ℕ) := List (CircuitStep n)

def ValidLayer (n : ℕ) (G : List (ℕ × ℕ)) : Prop :=
  (∀ g ∈ G, g.1 < n ∧ g.2 < n) ∧ (G.flatMap fun g => [g.1, g.2]).Nodup

def ValidCircuit {n : ℕ} (c : Circuit n) : Prop :=
  ∀ step ∈ c, match step with
  | .relabel _ => True
  | .layer G => ValidLayer n G

/-- Qubit labels at the two selected wires, for the published gate's 4×4 matrix. -/
def localBits {n : ℕ} (x : Word n) (a b : ℕ) : MITMSynthesis.Q 2 :=
  fun j => if j = 0 then ⟨(bitAt x a).val, ZMod.val_lt _⟩ else ⟨(bitAt x b).val, ZMod.val_lt _⟩

def placedCNOT (n a b : ℕ) : Matrix (Word n) (Word n) ℂ :=
  fun y x => if ∀ i : Fin n, i.val ≠ a → i.val ≠ b → y i = x i then
    (show Matrix (MITMSynthesis.Q 2) (MITMSynthesis.Q 2) ℂ from DepthOneQExp.cnotGate.mat.val) (localBits y a b) (localBits x a b) else 0

def stepMatrix {n : ℕ} : CircuitStep n → Matrix (Word n) (Word n) ℂ
  | .relabel p => fun y x => if y = (permMatrix p).mulVec x then 1 else 0
  | .layer G => (G.map fun g => placedCNOT n g.1 g.2).foldl (fun M T => T * M) 1

def circuitMatrix {n : ℕ} (c : Circuit n) : Matrix (Word n) (Word n) ℂ :=
  (c.map stepMatrix).foldl (fun M T => T * M) 1

def cnotCount {n : ℕ} (c : Circuit n) : ℕ :=
  (c.map fun step => match step with | .relabel _ => 0 | .layer G => G.length).sum

def circuitDepth {n : ℕ} (c : Circuit n) : ℕ :=
  (c.map fun step => match step with | .relabel _ => 0 | .layer _ => 1).sum

/-- The source's recursive in-place prefix schedule, valid also for odd n. -/
def prefixSchedule (n : ℕ) : List (List (ℕ × ℕ)) :=
  if h : n ≤ 1 then [] else
    [(List.range (n / 2)).map fun i => (2 * i, 2 * i + 1)] ++
    ((prefixSchedule (n / 2)).map fun G => G.map fun g => (2 * g.1 + 1, 2 * g.2 + 1)) ++
    [(List.range ((n - 1) / 2)).map fun i => (2 * i + 1, 2 * i + 2)]
termination_by n
decreasing_by omega

def outerSchedule (s b : ℕ) : List (List (ℕ × ℕ)) :=
  (List.range (2 * s - 3)).map fun t =>
    (List.range b).map fun j => if t < s - 2 then (j * s + t, j * s + (s - 2))
      else (j * s + (s - 1), j * s + (t - (s - 2)))

def encodingCircuit (s b m : ℕ) (π : Perms (s * b) m) : Circuit (s * b) :=
  (outerSchedule s b).map CircuitStep.layer ++
  (List.finRange m).flatMap fun i =>
    [CircuitStep.relabel (π ⟨2 * i.val, by omega⟩)] ++
    (prefixSchedule (s * b)).map CircuitStep.layer ++
    [CircuitStep.relabel (π ⟨2 * i.val + 1, by omega⟩)] ++
    (prefixSchedule (s * b)).reverse.map CircuitStep.layer

def ceilLog (n : ℕ) : ℕ := Nat.clog 2 n

/-- Correct on every complex input, preserving all inner products and covering the entire code. -/
def EncoderCorrect (s b m : ℕ) (π : Perms (s * b) m) : Prop :=
  ValidCircuit (encodingCircuit s b m π) ∧
  (∀ ψ : State ((s - 2) * b),
    (circuitMatrix (encodingCircuit s b m π)).mulVec (prepare s b ψ) = encode s b m π ψ) ∧
  (∀ ψ χ : State ((s - 2) * b),
    (∑ y, star (encode s b m π ψ y) * encode s b m π χ y) = ∑ x, star (ψ x) * χ x) ∧
  Set.range (fun ψ : State ((s - 2) * b) => publishedState (encode s b m π ψ)) =
    (quantumCode s b m π : Set (EuclideanSpace ℂ (QAlgorithms.Qubits (s * b))))

def ResourceBounds (s b m : ℕ) (π : Perms (s * b) m) : Prop :=
  circuitDepth (encodingCircuit s b m π) ≤ 2 * s - 3 + 4 * m * ceilLog (s * b) ∧
  (cnotCount (encodingCircuit s b m π) : ℝ) ≤
    (4 * m + (2 * s - 3 : ℝ) / s) * (s * b)

end CSSNearGV.Amplification


