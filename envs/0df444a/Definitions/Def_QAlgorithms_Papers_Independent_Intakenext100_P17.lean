-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P17
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:16:17.526886+00:00
-- url     : https://prove2.me/theorems/ef5b33fe-f25d-4dfb-9f1b-6879842dbb1b
-- title:
--   Definitions for Simple Proof of Security of the BB84 Quantum Key Distribution Protocol
-- statement:
--   The objects the formalized statements of *Simple Proof of Security of the BB84 Quantum Key Distribution Protocol* (arXiv:quant-ph/0003004) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `xPair`: PDF pp.1,3: product of two Hadamard-basis states; a true label means minus. The coordinate factor 1/2 is the product of the two normalizations 1/sqrt(2).
--   - `phaseCharacter`: PDF p.2, Eq.(2): the sign (-1)^(z dot w), with dot product in F_2.
--   - `cssPhaseWord`: PDF p.2, Eq.(2): the normalized codeword of Q_{x,z} for a FIXED vector v. In this paper C2 itself is summed over, whereas the frozen Gottesman cssCosetState sums over a dual code and omits normalization; it is not substituted here.
--   - `basisMatches`: PDF p.4, Protocol 3 steps 2,4,6: number of equal preparation/measurement bases. The arguments are the independently uniform basis strings, not channel errors.
--   - `siftingSuccess`: PDF p.4, Protocol 3 step 6: probability of retaining at least 2n signals when all N sent qubits are received. This explicitly averages over all 2^(2N) independently uniform ordered pairs of basis strings. Shortage is an abort and is included in the complementary probability.
--   - `signalCount`: PDF p.4, Protocol 3 step 1: integer implementation of (4+gamma)n signals. The ceiling agrees with the source whenever its signal count is integral. Gamma is the overhead parameter, distinct from the paper's error rate delta.
-- source:
--   Simple Proof of Security of the BB84 Quantum Key Distribution Protocol, arXiv:quant-ph/0003004v2, https://arxiv.org/abs/quant-ph/0003004v2

import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_FreshCopyTomographyPrograms
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

/-!
Shor and Preskill, Simple Proof of Security of the BB84 Quantum Key Distribution
Protocol, arXiv:quant-ph/0003004v2. Three standalone statements from PDF pp.3–4.
Operational security and protocol-reduction nodes are explicitly deferred in HARD.md.
Registers, computational kets, and pure density operators use the frozen conventions.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P17

noncomputable section

open scoped ComplexConjugate

open Classical

open QAlgorithms.DopedTomography (bellVector)

open QAlgorithms.Papers.Independent.Support50.P04 (BinaryWord)

/-- PDF pp.1,3: product of two Hadamard-basis states; a true label means minus.
The coordinate factor 1/2 is the product of the two normalizations 1/sqrt(2). -/
def xPair (a b : Bool) : EuclideanSpace ℂ (Qubits 1 × Qubits 1) :=
  WithLp.toLp 2 fun q =>
    (1 / 2 : ℂ) * (if a && q.1 0 then -1 else 1) * (if b && q.2 0 then -1 else 1)

example : xPair false true ((fun _ => false), (fun _ => true)) = -(1 / 2 : ℂ) := by
  simp [xPair]

/-- PDF p.2, Eq.(2): the sign (-1)^(z dot w), with dot product in F_2. -/
def phaseCharacter {n : ℕ} (z w : BinaryWord n) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin n, z i * w i).val

/-- PDF p.2, Eq.(2): the normalized codeword of Q_{x,z} for a FIXED vector v.
In this paper C2 itself is summed over, whereas the frozen Gottesman cssCosetState
sums over a dual code and omits normalization; it is not substituted here. -/
def cssPhaseWord {n : ℕ} (C2 : Submodule (ZMod 2) (BinaryWord n))
    (v x z : BinaryWord n) : EuclideanSpace ℂ (Qubits n) :=
  ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) •
    ∑ w : C2, phaseCharacter z (w : BinaryWord n) •
      ket (bitsOfZMod (x + v + (w : BinaryWord n)))

example {n : ℕ} (w : BinaryWord n) : phaseCharacter 0 w = 1 := by
  simp [phaseCharacter]

example {n : ℕ} (C2 : Submodule (ZMod 2) (BinaryWord n)) (v x : BinaryWord n) :
    cssPhaseWord C2 v x 0 =
      ((Real.sqrt (Fintype.card C2 : ℝ))⁻¹ : ℂ) •
        ∑ w : C2, ket (bitsOfZMod (x + v + (w : BinaryWord n))) := by
  simp [cssPhaseWord, phaseCharacter]

/-- PDF p.4, Protocol 3 steps 2,4,6: number of equal preparation/measurement bases.
The arguments are the independently uniform basis strings, not channel errors. -/
def basisMatches {N : ℕ} (a b : Qubits N) : ℕ :=
  (Finset.univ.filter fun i : Fin N => a i = b i).card

/-- PDF p.4, Protocol 3 step 6: probability of retaining at least 2n signals
when all N sent qubits are received. This explicitly averages over all 2^(2N)
independently uniform ordered pairs of basis strings. Shortage is an abort and
is included in the complementary probability. -/
def siftingSuccess (n N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * N))⁻¹ *
    ∑ a : Qubits N, ∑ b : Qubits N, if 2 * n ≤ basisMatches a b then 1 else 0

/-- PDF p.4, Protocol 3 step 1: integer implementation of (4+gamma)n signals.
The ceiling agrees with the source whenever its signal count is integral.
Gamma is the overhead parameter, distinct from the paper's error rate delta. -/
def signalCount (gamma : ℝ) (n : ℕ) : ℕ :=
  ⌈(4 + gamma) * (n : ℝ)⌉₊

example (a b : Qubits 0) : basisMatches a b = 0 := by
  simp [basisMatches]

example : siftingSuccess 0 0 = 1 := by
  simp [siftingSuccess, basisMatches]

example : signalCount 1 1 = 5 := by
  norm_num [signalCount]

end

end QAlgorithms.Papers.Independent.Intakenext100.P17


