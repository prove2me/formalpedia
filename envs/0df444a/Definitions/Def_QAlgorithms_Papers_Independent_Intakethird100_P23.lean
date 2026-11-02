-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P23
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P23
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:05:38.60128+00:00
-- url     : https://prove2.me/theorems/896c0da0-f61b-42bd-b765-36fe4ee8e51c
-- title:
--   Definitions for Quantum polar codes for arbitrary channels
-- statement:
--   The objects the formalized statements of *Quantum polar codes for arbitrary channels* (arXiv:1201.2906) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `polarMatrixEntry`: Entry of G_N = B_N F^{⊗n}, F = [[1,0],[1,1]], with row vectors and bit reversal B_N. The bit condition is j ⊆ reverse(i) (p.2).
--   - `polarEncode`: The actual Arikan binary transform u ↦ u G_N (pp.2–3).
--   - `binaryCharacter`: Character (-1)^{x·z} of the binary group (Eq.(8), p.3).
--   - `amplitudeVector`: Purified output on B^N E^N of the coherent encoder followed by U^{⊗N} on amplitude input u; U has computational-basis columns (pp.1,3).
--   - `amplitudeBlock`: Bob's actual amplitude output; the environment is traced out (Eqs.(1),(5), pp.1–2).
--   - `environmentBlock`: Eve's amplitude output, from the SAME purification and encoder (pp.2,8).
--   - `phaseVector`: Eq.(8), p.3, in register order (B^N,C^N),E^N. The C coordinate is z, while the input to U^{⊗N} is z G_N. This retains the coherent C-register transformation that appears when using G_N^T on phase labels.
--   - `phaseBlock`: Physical phase output on B^N C^N, with E^N inaccessible (Eq.(8), p.3).
--   - `splitChannel`: Combining and splitting of an ACTUAL block ensemble W. Conditional on u_i, all N-1 other bits are uniform, with the known history retained classically. Off-diagonal history entries vanish. The inline mask retains j<i in amplitude and i<j in phase, padding all other wires by false. Eqs.(5)–(6), p.2; reverse version p.3.
--   - `symmetricInformation`: Symmetric Holevo information in bits of a binary uniform ensemble (p.2).
--   - `channelRootFidelity`: Root channel fidelity; the paper's F is its square. On the physical normalized states this equals sqrt(F) (p.2).
--   - `threshold`: The fixed-exponent polarization threshold 2^{-N^beta} (Eq.(7), p.2).
--   - `amplitudeSplit`: Bob's synthesized amplitude channels, forward histories (pp.2–3).
--   - `phaseSplit`: Bob's synthesized phase channels, reverse histories and all C^N QSI (p.3).
--   - `environmentSplit`: Eve's synthesized amplitude channels, forward histories (pp.8–9).
--   - `goodSet`: Strict good-set rule; the bad set is exactly its complement (Eq.(7), p.2).
--   - `goodAmplitude`: Amplitude-good indices, Eq.(7) and I.C, pp.2–3.
--   - `goodPhase`: Phase-good indices, Eq.(7) and I.C, pp.2–3.
--   - `goodEnvironment`: Eve-amplitude-good indices, Appendix C, p.9.
--   - `informationSet`: Information-ebit positions A (p.3).
--   - `consumedSet`: Consumed-ebit positions B, doubly bad (p.3).
--   - `indexRate`: Index-set rate; N=2^n is always positive, including n=0 (p.6).
--   - `amplitudeInformation`: Single-use symmetric amplitude information (pp.2–3).
--   - `phaseInformation`: Single-use symmetric phase information, including C (pp.2–3).
--   - `symmetricCoherentInformation`: H(B)-H(E) on the maximally mixed qubit input, equal to H(B)-H(AB) on its purification. This is symmetric coherent information, with no maximization (p.3).
-- source:
--   Quantum polar codes for arbitrary channels, arXiv:1201.2906v2, https://arxiv.org/abs/1201.2906v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Statements from Wilde–Renes, arXiv:1201.2906v2. All page numbers are PDF pages.
The local definitions below construct the physical channels, rather than accepting
unrelated synthesized channels or their asymptotic properties as data.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P23

open scoped BigOperators ComplexConjugate Matrix
open Filter
open QAlgorithms (Qubits)
open QAlgorithms.Papers.Independent.Information100.P67 (IsDegradable)

attribute [local instance] Classical.propDecidable

/-- Entry of G_N = B_N F^{⊗n}, F = [[1,0],[1,1]], with row vectors
and bit reversal B_N. The bit condition is j ⊆ reverse(i) (p.2). -/
def polarMatrixEntry (n : ℕ) (i j : Fin (2 ^ n)) : Bool :=
  decide (∀ k : Fin n,
    (j.val / 2 ^ k.val) % 2 ≤ (i.val / 2 ^ (n - 1 - k.val)) % 2)

/-- The actual Arikan binary transform u ↦ u G_N (pp.2–3). -/
def polarEncode (n : ℕ) (u : Qubits (2 ^ n)) : Qubits (2 ^ n) :=
  fun j => decide ((∑ i : Fin (2 ^ n),
    if polarMatrixEntry n i j then (if u i then 1 else 0 : ℕ) else 0) % 2 = 1)

/-- The N=1 generator is the identity (p.2); no history bits exist. -/
example : polarMatrixEntry 0 0 0 = true := by
  simp [polarMatrixEntry]

/-- Character (-1)^{x·z} of the binary group (Eq.(8), p.3). -/
def binaryCharacter {N : ℕ} (x z : Qubits N) : ℂ :=
  (-1 : ℂ) ^ (∑ i, if x i ∧ z i then 1 else 0 : ℕ)

example {N : ℕ} (z : Qubits N) : binaryCharacter (fun _ => false) z = 1 := by
  simp [binaryCharacter]

/-- Purified output on B^N E^N of the coherent encoder followed by U^{⊗N}
on amplitude input u; U has computational-basis columns (pp.1,3). -/
noncomputable def amplitudeVector {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (u : Qubits (2 ^ n)) :
    EuclideanSpace ℂ ((Fin (2 ^ n) → Fin b) × (Fin (2 ^ n) → Fin e)) :=
  WithLp.toLp 2 fun p => ∏ k, U (p.1 k, p.2 k) (polarEncode n u k)

/-- Bob's actual amplitude output; the environment is traced out (Eqs.(1),(5), pp.1–2). -/
noncomputable def amplitudeBlock {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (u : Qubits (2 ^ n)) :=
  QAlgorithms.traceRight (QAlgorithms.pureDensity (amplitudeVector U n u))

/-- Eve's amplitude output, from the SAME purification and encoder (pp.2,8). -/
noncomputable def environmentBlock {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (u : Qubits (2 ^ n)) :=
  QAlgorithms.traceLeft (QAlgorithms.pureDensity (amplitudeVector U n u))

/-- Eq.(8), p.3, in register order (B^N,C^N),E^N. The C coordinate
is z, while the input to U^{⊗N} is z G_N. This retains the coherent
C-register transformation that appears when using G_N^T on phase labels. -/
noncomputable def phaseVector {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (x : Qubits (2 ^ n)) :
    EuclideanSpace ℂ (((Fin (2 ^ n) → Fin b) × Qubits (2 ^ n)) ×
      (Fin (2 ^ n) → Fin e)) :=
  WithLp.toLp 2 fun p =>
    ((Real.sqrt ((2 : ℝ) ^ (2 ^ n)))⁻¹ : ℂ) * binaryCharacter x p.1.2 *
      ∏ k, U (p.1.1 k, p.2 k) (polarEncode n p.1.2 k)

/-- Physical phase output on B^N C^N, with E^N inaccessible (Eq.(8), p.3). -/
noncomputable def phaseBlock {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (x : Qubits (2 ^ n)) :=
  QAlgorithms.traceRight (QAlgorithms.pureDensity (phaseVector U n x))

/-- Combining and splitting of an ACTUAL block ensemble W. Conditional on u_i,
all N-1 other bits are uniform, with the known history retained classically.
Off-diagonal history entries vanish. The inline mask retains j<i in amplitude
and i<j in phase, padding all other wires by false. Eqs.(5)–(6), p.2;
reverse version p.3. -/
noncomputable def splitChannel {N : ℕ} {O : Type*} [Fintype O]
    (W : Qubits N → Matrix O O ℂ) (reverse : Bool) (i : Fin N) (a : Bool) :
    Matrix (Qubits N × O) (Qubits N × O) ℂ :=
  fun p q => if p.1 = q.1 then
    (((2 : ℝ) ^ (N - 1))⁻¹ : ℂ) * ∑ u : Qubits N,
      if u i = a ∧
        (fun j : Fin N =>
          if (if reverse then i.val < j.val else j.val < i.val) then u j else false) = p.1
      then W u p.2 q.2 else 0
  else 0

/-- Symmetric Holevo information in bits of a binary uniform ensemble (p.2). -/
noncomputable def symmetricInformation {O : Type*} [Fintype O] [DecidableEq O]
    (W : Bool → Matrix O O ℂ) : ℝ :=
  QAlgorithms.vnEntropy (((1 / 2 : ℝ) : ℂ) • (W false + W true)) -
    (QAlgorithms.vnEntropy (W false) + QAlgorithms.vnEntropy (W true)) / 2

/-- Root channel fidelity; the paper's F is its square. On the physical
normalized states this equals sqrt(F) (p.2). -/
noncomputable def channelRootFidelity {O : Type*} [Fintype O] [DecidableEq O]
    (W : Bool → Matrix O O ℂ) : ℝ :=
  QAlgorithms.rootFidelity (W false) (W true)

/-- The fixed-exponent polarization threshold 2^{-N^beta} (Eq.(7), p.2). -/
noncomputable def threshold (n : ℕ) (beta : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(((2 ^ n : ℕ) : ℝ) ^ beta))

/-- Bob's synthesized amplitude channels, forward histories (pp.2–3). -/
noncomputable def amplitudeSplit {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (i : Fin (2 ^ n)) :=
  splitChannel (amplitudeBlock U n) false i

/-- Bob's synthesized phase channels, reverse histories and all C^N QSI (p.3). -/
noncomputable def phaseSplit {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (i : Fin (2 ^ n)) :=
  splitChannel (phaseBlock U n) true i

/-- Eve's synthesized amplitude channels, forward histories (pp.8–9). -/
noncomputable def environmentSplit {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (i : Fin (2 ^ n)) :=
  splitChannel (environmentBlock U n) false i

/-- Strict good-set rule; the bad set is exactly its complement (Eq.(7), p.2). -/
noncomputable def goodSet {N : ℕ} {O : Type*} [Fintype O] [DecidableEq O]
    (W : Fin N → Bool → Matrix O O ℂ) (t : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => channelRootFidelity (W i) < t

/-- Amplitude-good indices, Eq.(7) and I.C, pp.2–3. -/
noncomputable def goodAmplitude {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (beta : ℝ) := goodSet (amplitudeSplit U n) (threshold n beta)

/-- Phase-good indices, Eq.(7) and I.C, pp.2–3. -/
noncomputable def goodPhase {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (beta : ℝ) := goodSet (phaseSplit U n) (threshold n beta)

/-- Eve-amplitude-good indices, Appendix C, p.9. -/
noncomputable def goodEnvironment {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (beta : ℝ) := goodSet (environmentSplit U n) (threshold n beta)

/-- Information-ebit positions A (p.3). -/
noncomputable def informationSet {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (beta : ℝ) := goodAmplitude U n beta ∩ goodPhase U n beta

/-- Consumed-ebit positions B, doubly bad (p.3). -/
noncomputable def consumedSet {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ)
    (n : ℕ) (beta : ℝ) := (goodAmplitude U n beta ∪ goodPhase U n beta)ᶜ

/-- Index-set rate; N=2^n is always positive, including n=0 (p.6). -/
noncomputable def indexRate {n : ℕ} (S : Finset (Fin (2 ^ n))) : ℝ :=
  (S.card : ℝ) / (2 ^ n : ℕ)

/-- Single-use symmetric amplitude information (pp.2–3). -/
noncomputable def amplitudeInformation {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ) :=
  symmetricInformation (fun a => amplitudeBlock U 0 (fun _ => a))

/-- Single-use symmetric phase information, including C (pp.2–3). -/
noncomputable def phaseInformation {b e : ℕ} (U : Matrix (Fin b × Fin e) Bool ℂ) :=
  symmetricInformation (fun a => phaseBlock U 0 (fun _ => a))

/-- H(B)-H(E) on the maximally mixed qubit input, equal to H(B)-H(AB)
on its purification. This is symmetric coherent information, with no maximization (p.3). -/
noncomputable def symmetricCoherentInformation {b e : ℕ}
    (U : Matrix (Fin b × Fin e) Bool ℂ) : ℝ :=
  QAlgorithms.vnEntropy (((1 / 2 : ℝ) : ℂ) •
    (amplitudeBlock U 0 (fun _ => false) + amplitudeBlock U 0 (fun _ => true))) -
  QAlgorithms.vnEntropy (((1 / 2 : ℝ) : ℂ) •
    (environmentBlock U 0 (fun _ => false) + environmentBlock U 0 (fun _ => true)))

end QAlgorithms.Papers.Independent.Intakethird100.P23


