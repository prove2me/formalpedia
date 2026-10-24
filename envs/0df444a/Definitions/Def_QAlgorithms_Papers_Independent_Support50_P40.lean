-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40
-- name    : QAlgorithms_Papers_Independent_Support50_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T22:02:00.953984+00:00
-- url     : https://prove2.me/theorems/48434583-90a5-4898-aae2-6e80758a69f0
-- title:
--   Definitions for Quantum Channel Capacity of Very Noisy Channels
-- statement:
--   The objects the formalized statements of *Quantum Channel Capacity of Very Noisy Channels* (arXiv:quant-ph/9706061) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ErrorLabel`: PDF pp.5--7: phase-free physical Pauli labels.
--   - `labelMul`: PDF p.6: multiplication with its scalar phase discarded.
--   - `noiseG`: PDF p.3: each nonidentity Pauli has probability `(1-f)/3`.
--   - `weightPolynomial`: PDF p.7, Eq.(2): probability polynomial of a set of error labels.
--   - `slWeight`: PDF p.7, Eq.(3), with the Rains normalization used on that page.
--   - `slEnumerator`: PDF p.7, Eq.(4): the Shor--Laflamme generating polynomial.
--   - `stabilizerLabels`: PDF pp.6--8: the label set of a phase-inclusive stabilizer subgroup.
--   - `centralizerLabels`: PDF p.6: the phase-free commutation centralizer of the stabilizer.
--   - `labelCoset`: PDF pp.6--7: a phase-free left coset; the label group is Abelian.
--   - `InnerCode`: PDF pp.6,12: an additive inner code encoding exactly one logical qubit. The valid phase-inclusive stabilizer has no `-I`. Its `2^m` distinct labels mean `m` independent generators; the normalized basis spans its full +1 space.
--   - `innerEncoderMatrix`: PDF pp.8--9: the isometric encoder in the selected code basis. This matrix is distinct from the frozen folded classical Vandermonde encoder.
--   - `CosetChoices`: PDF pp.6--8,13: complete transversals, with logical I,X,Y,Z fixed in the same code basis. `logicalAction` is equality on every logical operator, so it does not mistake a logical Z fixing one vector for the identity channel.
--   - `syndromeMass`: PDF pp.7--8,13, Eq.(18): the coset mass for a syndrome.
--   - `jointMass`: PDF p.13, Eq.(19): joint logical-Pauli/syndrome mass, before conditioning.
--   - `finiteEntropyBits`: PDF p.12, Eq.(16): finite Shannon entropy in bits, with `0 log 0 = 0`. This takes a finite real mass vector, unlike the frozen quantum/relative entropies.
--   - `signedYield`: PDF p.13, Eq.(20): signed concatenation yield per physical channel use. A negative value is not interpreted as negative operational capacity.
--   - `conditionalBellEntropy`: PDF p.12, Eq.(14): syndrome-conditioned Bell entropy. A zero-mass branch contributes zero without evaluating a conditional distribution.
--   - `independentPauliChannel`: PDF pp.3,7: independent depolarization on a whole physical block. The parameter f is the identity-Pauli fidelity; this is the tensor product of single-qubit channels, not global replacement of the whole block.
--   - `codeBellInput`: PDF pp.9,15, Eqs.(7)--(9),(29): normalized encoded Bell input. The printed `1/2` coefficients in Eq.(29) are corrected to `1/sqrt(2)`; Eq.(7), the density normalization and Eq.(35) determine the correction. This input uses the selected stabilizer-code basis, rather than a dense-coding label.
--   - `outputRQ`: PDF pp.13--15: the actual output on RQ, with noiseless reference R.
--   - `outputQ`: PDF pp.14--15: the actual output on Q, obtained by tracing out R.
--   - `errorBasis`: PDF p.14, Eq.(24): the error-space code basis.
--   - `bellBasis`: PDF p.15, Eq.(30): the generalized normalized Bell basis, with the same syndrome and logical representatives used in the probabilities.
--   - `syndromeProjector`: PDF pp.8--9: the syndrome-space projector.
--   - `recoveredBranch`: PDF pp.9,13: unnormalized logical output for syndrome i after its specified correction; no division by a possibly zero syndrome probability.
--   - `errorEventMass`: PDF pp.7--8: mass of an event in the actual independent Pauli error law.
--   - `blockEncoder`: PDF pp.10--12: tensor product of the fixed inner encoder on n blocks.
--   - `IsAdditiveEncoder`: PDF pp.10--12: an outer additive encoder. The full image, not merely its basis vectors, is the stabilizer code; the isometry preserves all inputs.
--   - `FixedInnerAchievable`: PDF pp.3,10--12,28: attainability by the fixed-inner/additive-outer scheme. The inner block is fixed before n tends to infinity. One encoder and decoder works for every normalized unknown input, and its Bell-pair fidelity also tends to one. Only the physical noise and local CPTP decoding occur: no preshared entanglement or communication side channel is provided. Outer encoders can be selected by the source's random-code existence argument.
--   - `catEncoder`: PDF p.16, Eqs.(32)--(33): the ordinary cat encoder, including p=1.
--   - `catSpace`: PDF p.16: the full cat code space, not a single cat vector.
--   - `amplitudeBit`: PDF pp.2--3,17: the amplitude-error bit of a Pauli.
--   - `phaseBit`: PDF pp.2--3,17: the phase-error bit of a Pauli.
--   - `catSyndrome`: PDF pp.16--17, Fig.7: the measured CNOT-decoder syndrome.
--   - `catLogical`: PDF p.17: residual Pauli after the CNOT cat decoder. Bool addition is xor. The phase bit is the parity of all physical phase-error bits.
--   - `catJoint`: PDF pp.17--18, Eqs.(36)--(39): joint mass of one specified syndrome and logical outcome, computed from the error law rather than from the claimed formula.
--   - `catSyndromeMass`: PDF p.12, Eq.(15): the marginal mass of one specified cat syndrome.
--   - `catYield`: PDF pp.12--13,17--18: signed cat yield, with each syndrome counted separately.
--   - `catClosedMass`: PDF pp.17--18, Eqs.(36)--(39): closed formula for one syndrome of weight r. Its use in the theorem is restricted to r at most m.
--   - `positivityThreshold`: PDF pp.18--19,25,31: high-fidelity positivity threshold of a signed yield. For the codes in the theorems the set contains 1 and lies in [3/4,1], so this real infimum is neither empty nor unbounded.
--   - `catThreshold`: PDF pp.18--19,25: threshold for block size `m+1`.
--   - `rotatedFive`: PDF p.19, Eq.(43): the rotated cat module reverses both physical and logical amplitude/phase axes, `H^(tensor 5) V_cat H`. The logical H is needed when concatenating with the next ordinary cat encoder.
--   - `fiveInFive`: PDF p.19: ordinary five-cat first at encoding, then a rotated five-cat on each of its five outputs. Flattening has physical wire `5*block+within`. This fixes the inner 25-qubit code, rather than allowing an unrelated code witness.
--   - `singleZ`: PDF p.20: a single physical phase error on the specified wire.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, https://arxiv.org/abs/quant-ph/9706061v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Statements from DiVincenzo--Shor--Smolin, arXiv:quant-ph/9706061v3.
PDF page numbers refer to the supplied 31-page original. All new definitions
are local to this paper. In `InnerCode m` the physical block size is `m + 1`;
this includes the identity code (`m = 0`) and excludes an empty physical block.
-/

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer
open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.5--7: phase-free physical Pauli labels. -/
abbrev ErrorLabel (p : ℕ) := Fin p → Pauli

/-- PDF p.6: multiplication with its scalar phase discarded. -/
def labelMul {p : ℕ} (a b : ErrorLabel p) : ErrorLabel p :=
  fun q => (Pauli.mul (a q) (b q)).2

/-- PDF p.3: each nonidentity Pauli has probability `(1-f)/3`. -/
def noiseG (f : ℝ) : ℝ := (1 - f) / 3

/-- PDF p.7, Eq.(2): probability polynomial of a set of error labels. -/
def weightPolynomial {p : ℕ} (f : ℝ) (C : Finset (ErrorLabel p)) : ℝ :=
  ∑ e ∈ C, f ^ (p - opsWeight e) * noiseG f ^ opsWeight e

/-- PDF p.7, Eq.(3), with the Rains normalization used on that page. -/
def slWeight {p : ℕ} (d : ℕ) (O1 O2 : Matrix (Qubits p) (Qubits p) ℂ) : ℂ :=
  ∑ e ∈ Finset.univ.filter (fun e : ErrorLabel p => opsWeight e = d),
    (pauliOps e * O1).trace * (pauliOps e * O2).trace

/-- PDF p.7, Eq.(4): the Shor--Laflamme generating polynomial. -/
def slEnumerator {p : ℕ} (z : ℂ) (O1 O2 : Matrix (Qubits p) (Qubits p) ℂ) : ℂ :=
  ∑ d ∈ Finset.range (p + 1), slWeight d O1 O2 * z ^ d

/-- PDF pp.6--8: the label set of a phase-inclusive stabilizer subgroup. -/
def stabilizerLabels {p : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits p) ℂ)) :
    Finset (ErrorLabel p) := by
  classical
  exact Finset.univ.filter fun e => ∃ U ∈ S, ∃ c : ZMod 4,
    pauliOps e = Complex.I ^ c.val • (U : Matrix (Qubits p) (Qubits p) ℂ)

/-- PDF p.6: the phase-free commutation centralizer of the stabilizer. -/
def centralizerLabels {p : ℕ} (S : Subgroup (Matrix.unitaryGroup (Qubits p) ℂ)) :
    Finset (ErrorLabel p) := by
  classical
  exact Finset.univ.filter fun e => ∀ U ∈ S,
    pauliOps e * (U : Matrix (Qubits p) (Qubits p) ℂ) =
      (U : Matrix (Qubits p) (Qubits p) ℂ) * pauliOps e

/-- PDF pp.6--7: a phase-free left coset; the label group is Abelian. -/
def labelCoset {p : ℕ} (e : ErrorLabel p) (A : Finset (ErrorLabel p)) :
    Finset (ErrorLabel p) := by
  classical
  exact A.image (labelMul e)

/-- PDF pp.6,12: an additive inner code encoding exactly one logical qubit.
The valid phase-inclusive stabilizer has no `-I`. Its `2^m` distinct labels
mean `m` independent generators; the normalized basis spans its full +1 space. -/
structure InnerCode (m : ℕ) where
  stabilizer : Subgroup (Matrix.unitaryGroup (Qubits (m + 1)) ℂ)
  valid : IsStabilizerGroup stabilizer
  labelCount : (stabilizerLabels stabilizer).card = 2 ^ m
  basis : Bool → EuclideanSpace ℂ (Qubits (m + 1))
  orthonormal : Orthonormal ℂ basis
  basisSpan : Submodule.span ℂ (Set.range basis) = stabilizedSpace stabilizer

/-- PDF pp.8--9: the isometric encoder in the selected code basis.
This matrix is distinct from the frozen folded classical Vandermonde encoder. -/
def innerEncoderMatrix {m : ℕ} (C : InnerCode m) : Matrix (Qubits (m + 1)) Bool ℂ :=
  fun x b => C.basis b x

/-- PDF pp.6--8,13: complete transversals, with logical I,X,Y,Z fixed in
the same code basis. `logicalAction` is equality on every logical operator,
so it does not mistake a logical Z fixing one vector for the identity channel. -/
structure CosetChoices {m : ℕ} (C : InnerCode m) where
  syndromeRep : Qubits m → ErrorLabel (m + 1)
  logicalRep : Pauli → ErrorLabel (m + 1)
  syndromeZero : syndromeRep (fun _ => false) = fun _ => Pauli.I
  logicalIdentity : logicalRep .I = fun _ => Pauli.I
  syndromeTransversal : ∀ e : ErrorLabel (m + 1), ∃! i : Qubits m,
    e ∈ labelCoset (syndromeRep i) (centralizerLabels C.stabilizer)
  logicalCentralizes : ∀ j, logicalRep j ∈ centralizerLabels C.stabilizer
  logicalTransversal : ∀ e ∈ centralizerLabels C.stabilizer, ∃! j : Pauli,
    e ∈ labelCoset (logicalRep j) (stabilizerLabels C.stabilizer)
  logicalAction : ∀ j, ∀ rho : Matrix Bool Bool ℂ,
    conjSuperop (pauliOps (logicalRep j)) (conjSuperop (innerEncoderMatrix C) rho) =
      conjSuperop (innerEncoderMatrix C) (conjSuperop j.mat rho)

/-- PDF pp.7--8,13, Eq.(18): the coset mass for a syndrome. -/
def syndromeMass {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (f : ℝ)
    (i : Qubits m) : ℝ :=
  weightPolynomial f (labelCoset (T.syndromeRep i) (centralizerLabels C.stabilizer))

/-- PDF p.13, Eq.(19): joint logical-Pauli/syndrome mass, before conditioning. -/
def jointMass {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (f : ℝ)
    (i : Qubits m) (j : Pauli) : ℝ :=
  weightPolynomial f (labelCoset (labelMul (T.syndromeRep i) (T.logicalRep j))
    (stabilizerLabels C.stabilizer))

/-- PDF p.12, Eq.(16): finite Shannon entropy in bits, with `0 log 0 = 0`.
This takes a finite real mass vector, unlike the frozen quantum/relative entropies. -/
def finiteEntropyBits {A : Type*} [Fintype A] (a : A → ℝ) : ℝ :=
  -∑ x, a x * Real.logb 2 (a x)

/-- PDF p.13, Eq.(20): signed concatenation yield per physical channel use.
A negative value is not interpreted as negative operational capacity. -/
def signedYield {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (f : ℝ) : ℝ :=
  (1 + finiteEntropyBits (syndromeMass C T f) -
    finiteEntropyBits (fun ij : Qubits m × Pauli => jointMass C T f ij.1 ij.2)) / (m + 1)

/-- PDF p.12, Eq.(14): syndrome-conditioned Bell entropy. A zero-mass
branch contributes zero without evaluating a conditional distribution. -/
def conditionalBellEntropy {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (f : ℝ) : ℝ :=
  ∑ i : Qubits m, if syndromeMass C T f i = 0 then 0 else
    syndromeMass C T f i * finiteEntropyBits (fun j : Pauli => jointMass C T f i j / syndromeMass C T f i)

/-- PDF pp.3,7: independent depolarization on a whole physical block.
The parameter f is the identity-Pauli fidelity; this is the tensor product of
single-qubit channels, not global replacement of the whole block. -/
def independentPauliChannel (p : ℕ) (f : ℝ) : Superop (Qubits p) (Qubits p) :=
  fun rho => ∑ e : ErrorLabel p,
    ((f ^ (p - opsWeight e) * noiseG f ^ opsWeight e : ℝ) : ℂ) •
      conjSuperop (pauliOps e) rho

/-- PDF pp.9,15, Eqs.(7)--(9),(29): normalized encoded Bell input.
The printed `1/2` coefficients in Eq.(29) are corrected to `1/sqrt(2)`;
Eq.(7), the density normalization and Eq.(35) determine the correction.
This input uses the selected stabilizer-code basis, rather than a dense-coding label. -/
def codeBellInput {m : ℕ} (C : InnerCode m) : EuclideanSpace ℂ (Bool × Qubits (m + 1)) :=
  ((Real.sqrt 2)⁻¹ : ℂ) •
    (tensorVec (ket false) (C.basis false) + tensorVec (ket true) (C.basis true))

/-- PDF pp.13--15: the actual output on RQ, with noiseless reference R. -/
def outputRQ {m : ℕ} (C : InnerCode m) (f : ℝ) :
    Matrix (Bool × Qubits (m + 1)) (Bool × Qubits (m + 1)) ℂ :=
  idTensorSuperop (R := Bool) (independentPauliChannel (m + 1) f) (pureDensity (codeBellInput C))

/-- PDF pp.14--15: the actual output on Q, obtained by tracing out R. -/
def outputQ {m : ℕ} (C : InnerCode m) (f : ℝ) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  traceLeft (outputRQ C f)

/-- PDF p.14, Eq.(24): the error-space code basis. -/
def errorBasis {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (i : Qubits m) (b : Bool) :
    EuclideanSpace ℂ (Qubits (m + 1)) :=
  act (pauliOps (T.syndromeRep i)) (C.basis b)

/-- PDF p.15, Eq.(30): the generalized normalized Bell basis, with the
same syndrome and logical representatives used in the probabilities. -/
def bellBasis {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (i : Qubits m) (j : Pauli) :
    EuclideanSpace ℂ (Bool × Qubits (m + 1)) :=
  act (Matrix.kronecker (1 : Matrix Bool Bool ℂ)
    (pauliOps (labelMul (T.syndromeRep i) (T.logicalRep j)))) (codeBellInput C)

/-- PDF pp.8--9: the syndrome-space projector. -/
def syndromeProjector {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (i : Qubits m) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  ∑ b : Bool, pureDensity (errorBasis C T i b)

/-- PDF pp.9,13: unnormalized logical output for syndrome i after its
specified correction; no division by a possibly zero syndrome probability. -/
def recoveredBranch {m : ℕ} (C : InnerCode m) (T : CosetChoices C) (f : ℝ) (i : Qubits m) :
    Superop Bool Bool :=
  conjSuperop ((innerEncoderMatrix C)ᴴ * (pauliOps (T.syndromeRep i))ᴴ) ∘
    independentPauliChannel (m + 1) f ∘ conjSuperop (innerEncoderMatrix C)

/-- PDF pp.7--8: mass of an event in the actual independent Pauli error law. -/
def errorEventMass {p : ℕ} (f : ℝ) (P : ErrorLabel p → Prop) : ℝ := by
  classical
  exact weightPolynomial f (Finset.univ.filter P)

/-- PDF pp.10--12: tensor product of the fixed inner encoder on n blocks. -/
def blockEncoder {m : ℕ} (C : InnerCode m) (n : ℕ) :
    Matrix (Fin n → Qubits (m + 1)) (Qubits n) ℂ :=
  fun y x => ∏ i, innerEncoderMatrix C (y i) (x i)

/-- PDF pp.10--12: an outer additive encoder. The full image, not merely
its basis vectors, is the stabilizer code; the isometry preserves all inputs. -/
def IsAdditiveEncoder {n k : ℕ} (E : Matrix (Qubits n) (Qubits k) ℂ) : Prop :=
  k ≤ n ∧ Eᴴ * E = 1 ∧
    ∃ S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ),
      IsStabilizerGroup S ∧ LinearMap.range (Matrix.toEuclideanLin E) = stabilizedSpace S

/-- PDF pp.3,10--12,28: attainability by the fixed-inner/additive-outer
scheme. The inner block is fixed before n tends to infinity. One encoder
and decoder works for every normalized unknown input, and its Bell-pair
fidelity also tends to one. Only the physical noise and local CPTP decoding
occur: no preshared entanglement or communication side channel is provided.
Outer encoders can be selected by the source's random-code existence argument. -/
def FixedInnerAchievable {m : ℕ} (C : InnerCode m) (f R : ℝ) : Prop :=
  ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ k : ℕ, (R - delta) * ((m + 1) * n : ℕ) ≤ (k : ℝ) ∧
    ∃ E : Matrix (Qubits n) (Qubits k) ℂ, IsAdditiveEncoder E ∧
    ∃ D : Superop (Fin n → Qubits (m + 1)) (Qubits k), IsChannel D ∧
      let transmission := D ∘ piSuperop (fun _ : Fin n => independentPauliChannel (m + 1) f) ∘
        conjSuperop (blockEncoder C n) ∘ conjSuperop E
      1 - epsilon ≤ entanglementFidelity transmission ∧
      ∀ psi : EuclideanSpace ℂ (Qubits k), IsState psi →
        1 - epsilon ≤ effectProb (pureDensity psi) (transmission (pureDensity psi))

/-- PDF p.16, Eqs.(32)--(33): the ordinary cat encoder, including p=1. -/
def catEncoder (m : ℕ) : Matrix (Qubits (m + 1)) Bool ℂ :=
  fun x b => if x = (fun _ => b) then 1 else 0

/-- PDF p.16: the full cat code space, not a single cat vector. -/
def catSpace (m : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Qubits (m + 1))) :=
  Submodule.span ℂ (Set.range fun b : Bool => ket (fun _ : Fin (m + 1) => b))

/-- PDF pp.2--3,17: the amplitude-error bit of a Pauli. -/
def amplitudeBit : Pauli → Bool
  | .I => false
  | .X => true
  | .Y => true
  | .Z => false

/-- PDF pp.2--3,17: the phase-error bit of a Pauli. -/
def phaseBit : Pauli → Bool
  | .I => false
  | .X => false
  | .Y => true
  | .Z => true

/-- PDF pp.16--17, Fig.7: the measured CNOT-decoder syndrome. -/
def catSyndrome {m : ℕ} (e : ErrorLabel (m + 1)) : Qubits m :=
  fun q => amplitudeBit (e q.succ) + amplitudeBit (e 0)

/-- PDF p.17: residual Pauli after the CNOT cat decoder. Bool addition
is xor. The phase bit is the parity of all physical phase-error bits. -/
def catLogical {m : ℕ} (e : ErrorLabel (m + 1)) : Pauli :=
  pauliOfBits (amplitudeBit (e 0)) (∑ q, phaseBit (e q))

/-- PDF pp.17--18, Eqs.(36)--(39): joint mass of one specified syndrome
and logical outcome, computed from the error law rather than from the claimed formula. -/
def catJoint (m : ℕ) (f : ℝ) (i : Qubits m) (j : Pauli) : ℝ :=
  errorEventMass f (fun e : ErrorLabel (m + 1) => catSyndrome e = i ∧ catLogical e = j)

/-- PDF p.12, Eq.(15): the marginal mass of one specified cat syndrome. -/
def catSyndromeMass (m : ℕ) (f : ℝ) (i : Qubits m) : ℝ :=
  ∑ j : Pauli, catJoint m f i j

/-- PDF pp.12--13,17--18: signed cat yield, with each syndrome counted separately. -/
def catYield (m : ℕ) (f : ℝ) : ℝ :=
  (1 + finiteEntropyBits (catSyndromeMass m f) -
    finiteEntropyBits (fun ij : Qubits m × Pauli => catJoint m f ij.1 ij.2)) / (m + 1)

/-- PDF pp.17--18, Eqs.(36)--(39): closed formula for one syndrome of
weight r. Its use in the theorem is restricted to r at most m. -/
def catClosedMass (m : ℕ) (f : ℝ) (r : ℕ) : Pauli → ℝ
  | .X | .Y => (2 : ℝ) ^ (m + 1 - r - 1) * noiseG f ^ (m + 1 - r) * (f + noiseG f) ^ r
  | .I => if r = 0 then ((f + noiseG f) ^ (m + 1) + (f - noiseG f) ^ (m + 1)) / 2
      else (2 : ℝ) ^ (r - 1) * noiseG f ^ r * (f + noiseG f) ^ (m + 1 - r)
  | .Z => if r = 0 then ((f + noiseG f) ^ (m + 1) - (f - noiseG f) ^ (m + 1)) / 2
      else (2 : ℝ) ^ (r - 1) * noiseG f ^ r * (f + noiseG f) ^ (m + 1 - r)

/-- PDF pp.18--19,25,31: high-fidelity positivity threshold of a signed yield.
For the codes in the theorems the set contains 1 and lies in [3/4,1],
so this real infimum is neither empty nor unbounded. -/
def positivityThreshold (q : ℝ → ℝ) : ℝ :=
  sInf {f : ℝ | (3 / 4 : ℝ) ≤ f ∧ f ≤ 1 ∧ 0 < q f}

/-- PDF pp.18--19,25: threshold for block size `m+1`. -/
def catThreshold (m : ℕ) : ℝ := positivityThreshold (catYield m)

/-- PDF p.19, Eq.(43): the rotated cat module reverses both physical
and logical amplitude/phase axes, `H^(tensor 5) V_cat H`. The logical H is
needed when concatenating with the next ordinary cat encoder. -/
def rotatedFive : Matrix (Qubits 5) Bool ℂ :=
  fun x b => ∑ a : Bool, (∏ q : Fin 5, hadamard (x q) a) * hadamard a b

/-- PDF p.19: ordinary five-cat first at encoding, then a rotated five-cat
on each of its five outputs. Flattening has physical wire `5*block+within`.
This fixes the inner 25-qubit code, rather than allowing an unrelated code witness. -/
def fiveInFive : Matrix (Qubits 25) Bool ℂ :=
  fun x b => ∏ a : Fin 5,
    rotatedFive (fun q : Fin 5 => x ⟨5 * a.val + q.val, by omega⟩) b

/-- PDF p.20: a single physical phase error on the specified wire. -/
def singleZ {p : ℕ} (a : Fin p) : Matrix (Qubits p) (Qubits p) ℂ :=
  pauliOps (fun q => if q = a then Pauli.Z else Pauli.I)

/-! Small, proved normalization and convention checks for the local definitions. -/

example : noiseG 1 = 0 := by norm_num [noiseG]

example (f : ℝ) : weightPolynomial f (∅ : Finset (ErrorLabel 1)) = 0 := by
  simp [weightPolynomial]

example (f : ℝ) : weightPolynomial f ({fun _ : Fin 1 => Pauli.I} : Finset (ErrorLabel 1)) = f := by
  simp [weightPolynomial, opsWeight]

example (a b : Pauli) (q : Fin 1) :
    labelMul (fun _ => a) (fun _ => b) q = (Pauli.mul a b).2 := rfl

example : amplitudeBit .Y = true ∧ phaseBit .Y = true := ⟨rfl, rfl⟩

example (x : Qubits 1) (b : Bool) : catEncoder 0 x b =
    if x = (fun _ => b) then 1 else 0 := rfl

example (e : ErrorLabel 1) : catSyndrome (m := 0) e = (fun q => Fin.elim0 q) := by
  funext q
  exact Fin.elim0 q

example (a : Unit → ℝ) : finiteEntropyBits a = -(a () * Real.logb 2 (a ())) := by
  simp [finiteEntropyBits]

example {m : ℕ} (C : InnerCode m) (x : Fin 0 → Qubits (m + 1)) (b : Qubits 0) :
    blockEncoder C 0 x b = 1 := by simp [blockEncoder]

end

end QAlgorithms.Papers.Independent.Support50.P40


