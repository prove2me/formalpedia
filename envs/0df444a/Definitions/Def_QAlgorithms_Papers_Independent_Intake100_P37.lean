-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37
-- name    : QAlgorithms_Papers_Independent_Intake100_P37
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:59:40.816061+00:00
-- url     : https://prove2.me/theorems/b707a5a9-1ce4-46d5-804a-2cf81192abb2
-- title:
--   Definitions for Lambda's, V's and optimal cloning with stimulated emission
-- statement:
--   The objects the formalized statements of *Lambda's, V's and optimal cloning with stimulated emission* (arXiv:quant-ph/0003025) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhotonCounts`: PDF pp.2,4: r photon occupations, each bounded by the conserved energy.
--   - `AtomWord`: PDF pp.2,9: atomic words, with excited level r and ground levels 0,...,r-1.
--   - `excitedCount`: PDF p.2 Eq.(1): number of atoms at the excited level.
--   - `LambdaEnergyBasis`: PDF p.2 Eqs.(1),(2): full conserved sector, including nonsymmetric atoms and all polarizations. No emission-chain restriction appears in this type.
--   - `OscBasis`: PDF p.4 Eqs.(12)-(17): r photon modes and r+1 atomic modes. Both conservation equations are enforced, including all allowed polarizations.
--   - `applyMatrix`: Rectangular matrix action, with the same Euclidean convention as `act`.
--   - `emits`: PDF p.2: emission of one mode-a photon by a single specified atom. The equalities, rather than truncated updates, guard every boundary.
--   - `physicalH`: PDF p.2 Eq.(1), p.4 Eq.(16): real equal gamma, dipole/RWA interaction in one spatial field mode. Literal sqrt(n_a+1) factors and Hermitian conjugate.
--   - `physicalEmbedding`: PDF p.4, Appendix A: the actual occupation-to-individual-atoms matrix. It is the accepted positive normalized multinomial embedding, with fixed alphabet.
--   - `oscEmits`: PDF p.4 Eq.(12), Appendix A: oscillator emission with a shared pump c. The ground index b may differ from the photon index a after relabeling.
--   - `oscH`: PDF p.4 Eqs.(12),(17): matrix of gamma sum a_a^dagger b_a^dagger c+h.c.
--   - `groundRelabel`: PDF p.4: fixed unitary ground relabeling g1 -> b2, g2 -> -b1. Row p is in the singlet convention; column q is in the original convention.
--   - `fiveH`: PDF p.4 Eq.(14): the five-mode Hamiltonian, defined by literal square-root matrix elements on the whole oscillator sector, with the a2-b1 minus sign.
--   - `singletEmbedding`: PDF p.4: embedding of singlet-convention oscillator coordinates into the original distinguishable atomic Hilbert space. The inverse relabeling is essential.
--   - `physicalInput`: PDF p.2 Eq.(2): normalized bosonic m-copy input, all A atoms excited. No unknown-polarization-dependent dynamics occur in this definition.
--   - `emissionSectorKet`: PDF p.5 Eq.(19): signed, normalized sector vector in the five-mode basis. Out-of-range l is defined as zero and never used as a normalized state.
--   - `emissionTransfer`: PDF p.5 Eq.(21): derived tridiagonal transfer matrix (not the definition of physical evolution). Both zero endpoints, including A=0, are explicit.
--   - `emissionAmplitude`: PDF p.5 Eq.(18): exact chain coefficient, obtained from the physical transfer.
--   - `physicalOutput`: PDF p.5: actual physical state, using the full conserved-sector exponential.
--   - `atomicRotation`: PDF p.2: atomic conjugate action for ACTIVE photon creation-state action U. The excited level is fixed; this differs from the passive basis wording.
--   - `wordCounts`: Occupation counts of a finite word.
--   - `bosonAction`: PDF pp.2,4: actual normalized bosonic tensor representation. The finite word sum is the matrix element between normalized occupation kets.
--   - `physicalRotation`: PDF p.2: polarization action on the entire physical energy sector.
--   - `fiveRotation`: PDF p.4: simultaneous fundamental SU(2) action on a and b, pump fixed.
--   - `polarizationLift`: PDF pp.2,4: a specified SU(2) lift taking polarization (1,0) to psi. It is unitary with determinant one when psi has unit norm.
--   - `polarizedSector`: PDF p.5 Eq.(19) in an arbitrary polarization, in oscillator coordinates.
--   - `physicalSector`: PDF pp.2,5: sector ket in the ORIGINAL individual-atom convention.
--   - `selectExcited`: PDF p.5: projective measurement outcome with A-l excited atoms.
--   - `excitedOutcomeProbability`: PDF p.5: Born probability of the measured excited-atom outcome.
--   - `conditionalPhysical`: PDF p.5: conditional physical DENSITY, defined only operationally when success is positive. No vector phase equality is imposed by conditioning.
--   - `sectorReadout`: PDF pp.5,7: actual embedding of the l-sector into M=m+l clone qubits and l ground-state anti-clone qubits; the pump is fixed at A-l.
--   - `physicalReadout`: PDF pp.5-7: readout from the full physical space, including the explicit atomic relabeling, projection onto the measured sector and Bose identification.
--   - `sampledPhysical`: PDF p.7 Eqs.(27)-(30): sampled clone density, after the actual atomic measurement and after discarding the ground-state and pump ancillas.
--   - `sectorFidelity`: PDF p.5 Eq.(20): relative frequency evaluated on the normalized sector ket itself; it is not a free scalar constrained to equal a binomial sum.
--   - `benchmark`: PDF p.5 Eq.(20): optimal m-to-M single-copy benchmark, M>0 in uses.
--   - `photonDensity`: PDF p.7: clone density from photon occupation coordinates.
--   - `photonSample`: PDF pp.7-8: the sampled-photon density for a fixed output count.
--   - `PolarizationCovariant`: PDF p.8: polarization covariance of a fixed input-independent photon map. This is a condition on a single operation, never an input-dependent algorithm.
--   - `excitedInputEmbedding`: PDF pp.5,8: fixed input injection of the m-photon Bose space into the full physical sector, with all atoms excited.
--   - `branchKraus`: PDF pp.5,8: Kraus matrix for measuring output photon number m+l and tracing out one particular individual-atom word.
--   - `physicalBranch`: PDF pp.5,8: physical CP branch for fixed output number. The operation is constructed BEFORE the unknown polarization is supplied.
--   - `emissionBranchWeight`: PDF pp.5,8: fixed scalar branch weight evaluated on a reference input. Theorems derive its independence of the input; that is not a definition premise.
--   - `normalizedBranch`: PDF p.8: scalar normalization on ALL operators. It is a channel only when the proved scalar success effect is positive.
--   - `collectiveLower`: PDF p.9 Eq.(A2): sum_k |g_a><e| on individual atoms alone.
--   - `occupationLower`: PDF p.9 Eq.(A2): b_a^dagger c in the actual atomic occupation coordinates. Its factor excludes photon stimulation, which is left unapplied in (A2).
--   - `pairKet`: PDF p.6 Eq.(25): all three signed normalized pair columns.
--   - `VWord`: PDF pp.6-7: A fixed ordered pairs, containing 2A individual V atoms.
--   - `vExcited`: PDF p.6: true physical excitation count of the V atoms, including the one residual physical excitation of each effective ground-state pair.
--   - `VBasis`: PDF p.6 Eq.(22): entire conserved V sector, not just antisymmetric pairs.
--   - `vEmits`: PDF p.6 Eq.(22): physical single-atom emission, with no pair restriction.
--   - `vH`: PDF p.6 Eq.(22): common equal coupling to all 2A individual V atoms.
--   - `pairEmbedding`: PDF pp.6-7 Eqs.(25),(26): tensor product of the explicit pair columns, with photons unchanged. Domain is the full original Lambda sector.
--   - `vInput`: PDF p.6 Eq.(23), p.7 Eq.(26): normalized photon input times A pair singlets.
--   - `vOutput`: PDF pp.6-7: V evolution on its full energy sector.
--   - `vBranchKraus`: PDF p.6: V branch Kraus matrices, tracing out all individual V atoms.
--   - `vBranch`: PDF pp.6-7: the actual V photonic instrument branch.
--   - `oneAtomKet`: PDF p.3 Eqs.(5),(7): original atomic g1,g2 coefficients, both positive.
--   - `bhReadout`: PDF p.3 Eq.(8): original atomic g1 is down=0, g2 is up=1. Our false qubit denotes the source's photon state |1>.
--   - `bhKet`: PDF p.3 Eq.(8): BH three-qubit state in the explicit computational basis.
--   - `meanCloneFidelity`: PDF p.7 Eq.(30): mean single-site fidelity on an arbitrary M-qubit density.
--   - `ExchangeInvariant`: PDF pp.7-8: invariance under every exchange, without assuming Bose support.
--   - `photonFrequency`: PDF p.7 Eq.(30): photon relative frequency, pulled back through the actual Bose occupation embedding, for any desired polarization.
--   - `FiniteKrausBranch`: PDF p.8: physical finite-dimensional selected operation in Kraus form, with its trace-nonincreasing effect explicitly positive.
--   - `toQubitMap`: PDF p.8: equivalence map on physical totally symmetric qubit operators, zero-extended on the orthogonal complement of the input Bose space.
--   - `toPhotonMap`: PDF p.8: inverse map, compression into the real occupation coordinates.
--   - `BoseChannel`: PDF p.8: physical channel on the Bose corner in Bool tensor coordinates. A finite Kraus extension is CP; only the Bose corner has trace preservation.
--   - `mapWeight`: PDF p.8: scalar success probability of a covariant selected photon map, computed on a fixed reference input.
--   - `normalizeMap`: PDF p.8: fixed scalar normalization, not nonlinear division by rho's trace.
--   - `leadingTransfer`: PDF pp.9-10 Eq.(B1): leading large-m generator, with exact zero boundaries.
--   - `leadingAmplitude`: PDF p.10 Eq.(B2): coefficients obtained by exponentiating B1.
--   - `leadingProbability`: PDF p.10 Eq.(B3): the actual measurement probabilities in the B1 model.
--   - `atomPermutation`: PDF pp.3-4: atom permutations act on the full energy sector.
--   - `BoseUniversal`: PDF p.8: universal operation on the physical Bose input/output corners.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, https://arxiv.org/abs/quant-ph/0003025v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

/-!
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1. PDF page locators throughout.
The physical Hamiltonian acts on the ENTIRE finite conserved energy sector.
The symmetric occupation embedding and the emission chain are derived targets,
never assumptions restricting the Hamiltonian. Atomic alphabet: g1=0,g2=1,e=2.
A counts Lambda atoms or ordered V pairs; m counts incident photons; l counts
additional photons. The oscillator coordinates after ground relabeling are
(a1,a2,b1,b2,c), with g1 -> b2 and g2 -> -b1.
The classical-pump limiting assertion is deferred in HARD.md. Compilation pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,4: r photon occupations, each bounded by the conserved energy. -/
abbrev PhotonCounts (r E : ℕ) := Fin r → Fin (E + 1)

/-- PDF pp.2,9: atomic words, with excited level r and ground levels 0,...,r-1. -/
abbrev AtomWord (r A : ℕ) := Fin A → Fin (r + 1)

/-- PDF p.2 Eq.(1): number of atoms at the excited level. -/
def excitedCount {r A : ℕ} (w : AtomWord r A) : ℕ :=
  (Finset.univ.filter fun k => (w k).val = r).card

/-- PDF p.2 Eqs.(1),(2): full conserved sector, including nonsymmetric atoms
and all polarizations. No emission-chain restriction appears in this type. -/
abbrev LambdaEnergyBasis (r A m : ℕ) :=
  {x : PhotonCounts r (m + A) × AtomWord r A //
    (∑ a, (x.1 a).val) + excitedCount x.2 = m + A}

/-- PDF p.4 Eqs.(12)-(17): r photon modes and r+1 atomic modes.
Both conservation equations are enforced, including all allowed polarizations. -/
abbrev OscBasis (r A m : ℕ) :=
  {x : PhotonCounts r (m + A) × QAlgorithms.Papers.Independent.Support21.P16.BoseOccupation (r + 1) A //
    (∑ a, (x.1 a).val) + (x.2.val (Fin.last r)).val = m + A}

/-- Rectangular matrix action, with the same Euclidean convention as `act`. -/
def applyMatrix {I J : Type*} [Fintype I]
    (B : Matrix J I ℂ) (v : EuclideanSpace ℂ I) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (B.mulVec (WithLp.ofLp v))

/-- PDF p.2: emission of one mode-a photon by a single specified atom.
The equalities, rather than truncated updates, guard every boundary. -/
def emits {r A m : ℕ} (a : Fin r) (k : Fin A)
    (p q : LambdaEnergyBasis r A m) : Prop :=
  (q.val.2 k).val = r ∧
  p.val.2 = Function.update q.val.2 k a.castSucc ∧
  (p.val.1 a).val = (q.val.1 a).val + 1 ∧
  ∀ b, b ≠ a → p.val.1 b = q.val.1 b

/-- PDF p.2 Eq.(1), p.4 Eq.(16): real equal gamma, dipole/RWA interaction
in one spatial field mode. Literal sqrt(n_a+1) factors and Hermitian conjugate. -/
def physicalH (r A m : ℕ) (gamma : ℝ) :
    Matrix (LambdaEnergyBasis r A m) (LambdaEnergyBasis r A m) ℂ :=
  fun p q => (gamma : ℂ) * ∑ k : Fin A, ∑ a : Fin r,
    ((if emits a k p q then (Real.sqrt ((q.val.1 a).val + 1 : ℝ) : ℂ) else 0) +
    (if emits a k q p then (Real.sqrt ((p.val.1 a).val + 1 : ℝ) : ℂ) else 0))

/-- PDF p.4, Appendix A: the actual occupation-to-individual-atoms matrix.
It is the accepted positive normalized multinomial embedding, with fixed alphabet. -/
def physicalEmbedding (r A m : ℕ) :
    Matrix (LambdaEnergyBasis r A m) (OscBasis r A m) ℂ :=
  fun p q => if p.val.1 = q.val.1 then
    QAlgorithms.Papers.Independent.Support21.P16.occupationEmbedding (r + 1) A p.val.2 q.val.2 else 0

/-- PDF p.4 Eq.(12), Appendix A: oscillator emission with a shared pump c.
The ground index b may differ from the photon index a after relabeling. -/
def oscEmits {r A m : ℕ} (a b : Fin r) (p q : OscBasis r A m) : Prop :=
  (p.val.1 a).val = (q.val.1 a).val + 1 ∧
  (∀ d, d ≠ a → p.val.1 d = q.val.1 d) ∧
  (p.val.2.val b.castSucc).val = (q.val.2.val b.castSucc).val + 1 ∧
  (q.val.2.val (Fin.last r)).val = (p.val.2.val (Fin.last r)).val + 1 ∧
  ∀ d : Fin r, d ≠ b → p.val.2.val d.castSucc = q.val.2.val d.castSucc

/-- PDF p.4 Eqs.(12),(17): matrix of gamma sum a_a^dagger b_a^dagger c+h.c. -/
def oscH (r A m : ℕ) (gamma : ℝ) :
    Matrix (OscBasis r A m) (OscBasis r A m) ℂ :=
  fun p q => (gamma : ℂ) * ∑ a : Fin r,
    ((if oscEmits a a p q then
      (Real.sqrt (((q.val.1 a).val + 1 : ℝ) *
        ((q.val.2.val a.castSucc).val + 1) *
        (q.val.2.val (Fin.last r)).val) : ℂ) else 0) +
    (if oscEmits a a q p then
      (Real.sqrt (((p.val.1 a).val + 1 : ℝ) *
        ((p.val.2.val a.castSucc).val + 1) *
        (p.val.2.val (Fin.last r)).val) : ℂ) else 0))

/-- PDF p.4: fixed unitary ground relabeling g1 -> b2, g2 -> -b1.
Row p is in the singlet convention; column q is in the original convention. -/
def groundRelabel (A m : ℕ) : Matrix (OscBasis 2 A m) (OscBasis 2 A m) ℂ :=
  fun p q => if p.val.1 = q.val.1 ∧
      p.val.2.val 0 = q.val.2.val 1 ∧ p.val.2.val 1 = q.val.2.val 0 ∧
      p.val.2.val 2 = q.val.2.val 2 then
    (-1 : ℂ) ^ (q.val.2.val 1).val else 0

/-- PDF p.4 Eq.(14): the five-mode Hamiltonian, defined by literal square-root
matrix elements on the whole oscillator sector, with the a2-b1 minus sign. -/
def fiveH (A m : ℕ) (gamma : ℝ) : Matrix (OscBasis 2 A m) (OscBasis 2 A m) ℂ :=
  fun p q => (gamma : ℂ) * ∑ a : Fin 2,
    (-1 : ℂ) ^ a.val *
    ((if oscEmits a (Fin.rev a) p q then
      (Real.sqrt (((q.val.1 a).val + 1 : ℝ) *
        ((q.val.2.val (Fin.rev a).castSucc).val + 1) *
        (q.val.2.val 2).val) : ℂ) else 0) +
     (if oscEmits a (Fin.rev a) q p then
      (Real.sqrt (((p.val.1 a).val + 1 : ℝ) *
        ((p.val.2.val (Fin.rev a).castSucc).val + 1) *
        (p.val.2.val 2).val) : ℂ) else 0))

/-- PDF p.4: embedding of singlet-convention oscillator coordinates into the
original distinguishable atomic Hilbert space. The inverse relabeling is essential. -/
def singletEmbedding (A m : ℕ) : Matrix (LambdaEnergyBasis 2 A m) (OscBasis 2 A m) ℂ :=
  physicalEmbedding 2 A m * (groundRelabel A m)ᴴ

/-- PDF p.2 Eq.(2): normalized bosonic m-copy input, all A atoms excited.
No unknown-polarization-dependent dynamics occur in this definition. -/
def physicalInput (A m : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (LambdaEnergyBasis 2 A m) :=
  WithLp.toLp 2 fun p =>
    if (∀ k, (p.val.2 k).val = 2) ∧
        (p.val.1 0).val + (p.val.1 1).val = m then
      (Real.sqrt (Nat.choose m (p.val.1 1).val : ℝ) : ℂ) *
        psi 0 ^ (p.val.1 0).val * psi 1 ^ (p.val.1 1).val else 0

/-- PDF p.5 Eq.(19): signed, normalized sector vector in the five-mode basis.
Out-of-range l is defined as zero and never used as a normalized state. -/
def emissionSectorKet (A m l : ℕ) : EuclideanSpace ℂ (OscBasis 2 A m) :=
  WithLp.toLp 2 fun p =>
    if l ≤ A ∧ (p.val.1 0).val + (p.val.1 1).val = m + l ∧
        (p.val.2.val 2).val = A - l ∧
        (p.val.2.val 0).val = (p.val.1 1).val ∧
        (p.val.2.val 1).val + (p.val.1 1).val = l then
      (-1 : ℂ) ^ (p.val.1 1).val *
        (Real.sqrt (Nat.choose (m + l - (p.val.1 1).val) m : ℝ) : ℂ) /
        (Real.sqrt (Nat.choose (m + l + 1) l : ℝ) : ℂ) else 0

/-- PDF p.5 Eq.(21): derived tridiagonal transfer matrix (not the definition
of physical evolution). Both zero endpoints, including A=0, are explicit. -/
def emissionTransfer (A m : ℕ) (gamma : ℝ) : Matrix (Fin (A + 1)) (Fin (A + 1)) ℂ :=
  fun k l => if k.val = l.val + 1 then
    (gamma * Real.sqrt ((l.val + 1 : ℝ) * (A - l.val) * (m + l.val + 2)) : ℂ)
  else if l.val = k.val + 1 then
    (gamma * Real.sqrt ((k.val + 1 : ℝ) * (A - k.val) * (m + k.val + 2)) : ℂ)
  else 0

/-- PDF p.5 Eq.(18): exact chain coefficient, obtained from the physical transfer. -/
def emissionAmplitude (A m : ℕ) (gamma t : ℝ) (l : Fin (A + 1)) : ℂ :=
  QAlgorithms.Papers.Independent.Claimed50.P15.propagator (emissionTransfer A m gamma) t l 0

/-- PDF p.5: actual physical state, using the full conserved-sector exponential. -/
def physicalOutput (A m : ℕ) (gamma t : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (LambdaEnergyBasis 2 A m) :=
  act (QAlgorithms.Papers.Independent.Claimed50.P15.propagator (physicalH 2 A m gamma) t) (physicalInput A m psi)

/-- PDF p.2: atomic conjugate action for ACTIVE photon creation-state action U.
The excited level is fixed; this differs from the passive basis wording. -/
def atomicRotation (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => if ha : a.val < 2 then
    if hb : b.val < 2 then conj (U ⟨a.val, ha⟩ ⟨b.val, hb⟩) else 0
  else if b.val = 2 then 1 else 0

/-- Occupation counts of a finite word. -/
def wordCounts {r n : ℕ} (x : Fin n → Fin r) (a : Fin r) : ℕ :=
  (Finset.univ.filter fun k => x k = a).card

/-- PDF pp.2,4: actual normalized bosonic tensor representation. The finite
word sum is the matrix element between normalized occupation kets. -/
def bosonAction (r n : ℕ) (U : Matrix (Fin r) (Fin r) ℂ)
    (out inp : Fin r → ℕ) : ℂ :=
  (Real.sqrt ((∏ a, (Nat.factorial (out a) : ℝ)) / Nat.factorial n) : ℂ) *
  (Real.sqrt ((∏ a, (Nat.factorial (inp a) : ℝ)) / Nat.factorial n) : ℂ) *
    ∑ x : Fin n → Fin r, ∑ y : Fin n → Fin r,
      if wordCounts x = out ∧ wordCounts y = inp then ∏ k, U (x k) (y k) else 0

/-- PDF p.2: polarization action on the entire physical energy sector. -/
def physicalRotation (A m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (LambdaEnergyBasis 2 A m) (LambdaEnergyBasis 2 A m) ℂ :=
  fun p q => if (∑ a, (p.val.1 a).val) = (∑ a, (q.val.1 a).val) then
    bosonAction 2 (∑ a, (q.val.1 a).val) U
      (fun a => (p.val.1 a).val) (fun a => (q.val.1 a).val) *
    ∏ k, atomicRotation U (p.val.2 k) (q.val.2 k) else 0

/-- PDF p.4: simultaneous fundamental SU(2) action on a and b, pump fixed. -/
def fiveRotation (A m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (OscBasis 2 A m) (OscBasis 2 A m) ℂ :=
  fun p q => if p.val.2.val 2 = q.val.2.val 2 then
    bosonAction 2 (∑ a, (q.val.1 a).val) U
      (fun a => (p.val.1 a).val) (fun a => (q.val.1 a).val) *
    bosonAction 2 (A - (q.val.2.val 2).val) U
      (fun a => (p.val.2.val a.castSucc).val)
      (fun a => (q.val.2.val a.castSucc).val) else 0

/-- PDF pp.2,4: a specified SU(2) lift taking polarization (1,0) to psi.
It is unitary with determinant one when psi has unit norm. -/
def polarizationLift (psi : EuclideanSpace ℂ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![psi 0, -conj (psi 1); psi 1, conj (psi 0)]

/-- PDF p.5 Eq.(19) in an arbitrary polarization, in oscillator coordinates. -/
def polarizedSector (A m l : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (OscBasis 2 A m) :=
  act (fiveRotation A m (polarizationLift psi)) (emissionSectorKet A m l)

/-- PDF pp.2,5: sector ket in the ORIGINAL individual-atom convention. -/
def physicalSector (A m l : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (LambdaEnergyBasis 2 A m) :=
  applyMatrix (singletEmbedding A m) (polarizedSector A m l psi)

/-- PDF p.5: projective measurement outcome with A-l excited atoms. -/
def selectExcited (A m l : ℕ) : Matrix (LambdaEnergyBasis 2 A m) (LambdaEnergyBasis 2 A m) ℂ :=
  Matrix.diagonal fun p => if l ≤ A ∧ excitedCount p.val.2 = A - l then 1 else 0

/-- PDF p.5: Born probability of the measured excited-atom outcome. -/
def excitedOutcomeProbability (A m l : ℕ) (gamma t : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  ‖act (selectExcited A m l) (physicalOutput A m gamma t psi)‖ ^ 2

/-- PDF p.5: conditional physical DENSITY, defined only operationally when
success is positive. No vector phase equality is imposed by conditioning. -/
def conditionalPhysical (A m l : ℕ) (gamma t : ℝ)
    (psi : EuclideanSpace ℂ (Fin 2)) : Matrix (LambdaEnergyBasis 2 A m) (LambdaEnergyBasis 2 A m) ℂ :=
  ((excitedOutcomeProbability A m l gamma t psi : ℂ)⁻¹) •
    pureDensity (act (selectExcited A m l) (physicalOutput A m gamma t psi))

/-- PDF pp.5,7: actual embedding of the l-sector into M=m+l clone qubits
and l ground-state anti-clone qubits; the pump is fixed at A-l. -/
def sectorReadout (A m l : ℕ) :
    Matrix (Qubits (m + l) × Qubits l) (OscBasis 2 A m) ℂ :=
  fun x p => if hp : (p.val.1 1).val < m + l + 1 then
    if hb : (p.val.2.val 1).val < l + 1 then
      if l ≤ A ∧ (p.val.1 0).val + (p.val.1 1).val = m + l ∧
          (p.val.2.val 0).val + (p.val.2.val 1).val = l ∧
          (p.val.2.val 2).val = A - l then
        QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding (m + l) x.1 ⟨(p.val.1 1).val, hp⟩ *
        QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding l x.2 ⟨(p.val.2.val 1).val, hb⟩ else 0
    else 0 else 0

/-- PDF pp.5-7: readout from the full physical space, including the explicit
atomic relabeling, projection onto the measured sector and Bose identification. -/
def physicalReadout (A m l : ℕ) :
    Matrix (Qubits (m + l) × Qubits l) (LambdaEnergyBasis 2 A m) ℂ :=
  sectorReadout A m l * groundRelabel A m * (physicalEmbedding 2 A m)ᴴ

/-- PDF p.7 Eqs.(27)-(30): sampled clone density, after the actual atomic
measurement and after discarding the ground-state and pump ancillas. -/
def sampledPhysical (A m l : ℕ) (gamma t : ℝ)
    (psi : EuclideanSpace ℂ (Fin 2)) (k : Fin (m + l)) : Matrix (Fin 2) (Fin 2) ℂ :=
  QAlgorithms.Papers.Independent.Support21.P18.siteReduction (traceRight (physicalReadout A m l *
    conditionalPhysical A m l gamma t psi * (physicalReadout A m l)ᴴ)) k

/-- PDF p.5 Eq.(20): relative frequency evaluated on the normalized sector
ket itself; it is not a free scalar constrained to equal a binomial sum. -/
def sectorFidelity (A m l : ℕ) : ℝ :=
  ∑ p : OscBasis 2 A m, Complex.normSq (emissionSectorKet A m l p) *
    ((p.val.1 0).val : ℝ) / (m + l)

/-- PDF p.5 Eq.(20): optimal m-to-M single-copy benchmark, M>0 in uses. -/
def benchmark (m M : ℕ) : ℝ :=
  ((M * m + M + m : ℕ) : ℝ) / ((M : ℝ) * (m + 2))

/-- PDF p.7: clone density from photon occupation coordinates. -/
def photonDensity (M : ℕ) (rho : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) :
    Matrix (Qubits M) (Qubits M) ℂ :=
  QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M * rho * (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M)ᴴ

/-- PDF pp.7-8: the sampled-photon density for a fixed output count. -/
def photonSample (M : ℕ) (rho : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    (k : Fin M) : Matrix (Fin 2) (Fin 2) ℂ :=
  QAlgorithms.Papers.Independent.Support21.P18.siteReduction (photonDensity M rho) k

/-- PDF p.8: polarization covariance of a fixed input-independent photon map.
This is a condition on a single operation, never an input-dependent algorithm. -/
def PolarizationCovariant (m M : ℕ) (T : Superop (Fin (m + 1)) (Fin (M + 1))) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, ∀ rho,
    T (QAlgorithms.Papers.Independent.Support21.P18.symmetricAction m U.val * rho * (QAlgorithms.Papers.Independent.Support21.P18.symmetricAction m U.val)ᴴ) =
      QAlgorithms.Papers.Independent.Support21.P18.symmetricAction M U.val * T rho * (QAlgorithms.Papers.Independent.Support21.P18.symmetricAction M U.val)ᴴ

/-- PDF pp.5,8: fixed input injection of the m-photon Bose space into the
full physical sector, with all atoms excited. -/
def excitedInputEmbedding (A m : ℕ) : Matrix (LambdaEnergyBasis 2 A m) (Fin (m + 1)) ℂ :=
  fun p j => if (∀ k, (p.val.2 k).val = 2) ∧
      (p.val.1 0).val + (p.val.1 1).val = m ∧ (p.val.1 1).val = j.val then 1 else 0

/-- PDF pp.5,8: Kraus matrix for measuring output photon number m+l and
tracing out one particular individual-atom word. -/
def branchKraus (A m l : ℕ) (gamma t : ℝ) (w : AtomWord 2 A) :
    Matrix (Fin (m + l + 1)) (Fin (m + 1)) ℂ :=
  fun o j => ∑ p : LambdaEnergyBasis 2 A m,
    if p.val.2 = w ∧ (p.val.1 0).val = m + l - o.val ∧
        (p.val.1 1).val = o.val then
      (QAlgorithms.Papers.Independent.Claimed50.P15.propagator (physicalH 2 A m gamma) t * excitedInputEmbedding A m) p j else 0

/-- PDF pp.5,8: physical CP branch for fixed output number. The operation is
constructed BEFORE the unknown polarization is supplied. -/
def physicalBranch (A m l : ℕ) (gamma t : ℝ) :
    Superop (Fin (m + 1)) (Fin (m + l + 1)) :=
  krausApply (branchKraus A m l gamma t)

/-- PDF pp.5,8: fixed scalar branch weight evaluated on a reference input.
Theorems derive its independence of the input; that is not a definition premise. -/
def emissionBranchWeight (A m l : ℕ) (gamma t : ℝ) : ℝ :=
  (physicalBranch A m l gamma t (pureDensity (ket (0 : Fin (m + 1))))).trace.re

/-- PDF p.8: scalar normalization on ALL operators. It is a channel only
when the proved scalar success effect is positive. -/
def normalizedBranch (A m l : ℕ) (gamma t : ℝ) :
    Superop (Fin (m + 1)) (Fin (m + l + 1)) :=
  fun rho => ((emissionBranchWeight A m l gamma t : ℂ)⁻¹) • physicalBranch A m l gamma t rho

/-! Atomic collective lowering operators for Appendix A and its r-ground extension. -/

/-- PDF p.9 Eq.(A2): sum_k |g_a><e| on individual atoms alone. -/
def collectiveLower (r A : ℕ) (a : Fin r) : Matrix (AtomWord r A) (AtomWord r A) ℂ :=
  fun x y => ∑ k : Fin A,
    if (y k).val = r ∧ x = Function.update y k a.castSucc then 1 else 0

/-- PDF p.9 Eq.(A2): b_a^dagger c in the actual atomic occupation coordinates.
Its factor excludes photon stimulation, which is left unapplied in (A2). -/
def occupationLower (r A : ℕ) (a : Fin r) :
    Matrix (QAlgorithms.Papers.Independent.Support21.P16.BoseOccupation (r + 1) A) (QAlgorithms.Papers.Independent.Support21.P16.BoseOccupation (r + 1) A) ℂ :=
  fun p q => if (p.val a.castSucc).val = (q.val a.castSucc).val + 1 ∧
      (q.val (Fin.last r)).val = (p.val (Fin.last r)).val + 1 ∧
      (∀ b : Fin r, b ≠ a → p.val b.castSucc = q.val b.castSucc) then
    (Real.sqrt (((q.val a.castSucc).val + 1 : ℝ) * (q.val (Fin.last r)).val) : ℂ) else 0

/-! Small sanity checks of definitions, with no source-result proofs. -/

example (r : ℕ) (w : AtomWord r 0) : excitedCount w = 0 := by
  simp [excitedCount]

example {I J : Type*} [Fintype I] (v : EuclideanSpace ℂ I) :
    applyMatrix (0 : Matrix J I ℂ) v = 0 := by
  simp [applyMatrix]

example (r m : ℕ) (gamma : ℝ) : physicalH r 0 m gamma = 0 := by
  ext p q
  simp [physicalH]

example (A m : ℕ) (p q : LambdaEnergyBasis 2 A m) : physicalH 2 A m 0 p q = 0 := by
  simp [physicalH]

example (psi : EuclideanSpace ℂ (Fin 2)) :
    polarizationLift psi 0 0 = psi 0 ∧ polarizationLift psi 1 0 = psi 1 := by
  simp [polarizationLift]

example (m : ℕ) (gamma : ℝ) : emissionTransfer 0 m gamma = 0 := by
  ext k l
  have hk : k.val = 0 := by omega
  have hl : l.val = 0 := by omega
  simp [emissionTransfer, hk, hl]

example : benchmark 1 2 = 5 / 6 := by norm_num [benchmark]

example (r : ℕ) (a : Fin r) : collectiveLower r 0 a = 0 := by
  ext x y
  simp [collectiveLower]

/-! V atoms: ordered pairs are explicit; individual level labels e1=0,e2=1,g=2. -/

/-- PDF p.6 Eq.(25): all three signed normalized pair columns. -/
def pairKet : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p q => (Real.sqrt 2 : ℂ)⁻¹ *
    (if q = 2 then
      (if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0)
    else if q = 0 then
      (if p = (2, 1) then 1 else if p = (1, 2) then -1 else 0)
    else (if p = (0, 2) then 1 else if p = (2, 0) then -1 else 0))

/-- PDF pp.6-7: A fixed ordered pairs, containing 2A individual V atoms. -/
abbrev VWord (A : ℕ) := Fin A → Fin 2 → Fin 3

/-- PDF p.6: true physical excitation count of the V atoms, including the
one residual physical excitation of each effective ground-state pair. -/
def vExcited {A : ℕ} (w : VWord A) : ℕ :=
  ∑ k, (Finset.univ.filter fun s : Fin 2 => (w k s).val < 2).card

/-- PDF p.6 Eq.(22): entire conserved V sector, not just antisymmetric pairs. -/
abbrev VBasis (A m : ℕ) :=
  {x : PhotonCounts 2 (m + 2 * A) × VWord A //
    (∑ a, (x.1 a).val) + vExcited x.2 = m + 2 * A}

/-- PDF p.6 Eq.(22): physical single-atom emission, with no pair restriction. -/
def vEmits {A m : ℕ} (a : Fin 2) (k : Fin A) (s : Fin 2)
    (p q : VBasis A m) : Prop :=
  q.val.2 k s = a.castSucc ∧
  p.val.2 = Function.update q.val.2 k (Function.update (q.val.2 k) s 2) ∧
  (p.val.1 a).val = (q.val.1 a).val + 1 ∧
  ∀ b, b ≠ a → p.val.1 b = q.val.1 b

/-- PDF p.6 Eq.(22): common equal coupling to all 2A individual V atoms. -/
def vH (A m : ℕ) (gamma : ℝ) : Matrix (VBasis A m) (VBasis A m) ℂ :=
  fun p q => (gamma : ℂ) * ∑ k : Fin A, ∑ s : Fin 2, ∑ a : Fin 2,
    ((if vEmits a k s p q then (Real.sqrt ((q.val.1 a).val + 1 : ℝ) : ℂ) else 0) +
    (if vEmits a k s q p then (Real.sqrt ((p.val.1 a).val + 1 : ℝ) : ℂ) else 0))

/-- PDF pp.6-7 Eqs.(25),(26): tensor product of the explicit pair columns,
with photons unchanged. Domain is the full original Lambda sector. -/
def pairEmbedding (A m : ℕ) : Matrix (VBasis A m) (LambdaEnergyBasis 2 A m) ℂ :=
  fun p q => if (∀ a, (p.val.1 a).val = (q.val.1 a).val) then
    ∏ k, pairKet (p.val.2 k 0, p.val.2 k 1) (q.val.2 k) else 0

/-- PDF p.6 Eq.(23), p.7 Eq.(26): normalized photon input times A pair singlets. -/
def vInput (A m : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (VBasis A m) :=
  applyMatrix (pairEmbedding A m) (physicalInput A m psi)

/-- PDF pp.6-7: V evolution on its full energy sector. -/
def vOutput (A m : ℕ) (gamma t : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (VBasis A m) :=
  act (QAlgorithms.Papers.Independent.Claimed50.P15.propagator (vH A m gamma) t) (vInput A m psi)

/-- PDF p.6: V branch Kraus matrices, tracing out all individual V atoms. -/
def vBranchKraus (A m l : ℕ) (gamma t : ℝ) (w : VWord A) :
    Matrix (Fin (m + l + 1)) (Fin (m + 1)) ℂ :=
  fun o j => ∑ p : VBasis A m,
    if p.val.2 = w ∧ (p.val.1 0).val = m + l - o.val ∧
        (p.val.1 1).val = o.val then
      (QAlgorithms.Papers.Independent.Claimed50.P15.propagator (vH A m gamma) t * pairEmbedding A m * excitedInputEmbedding A m) p j else 0

/-- PDF pp.6-7: the actual V photonic instrument branch. -/
def vBranch (A m l : ℕ) (gamma t : ℝ) :
    Superop (Fin (m + 1)) (Fin (m + l + 1)) := krausApply (vBranchKraus A m l gamma t)

/-! One atom, in the ORIGINAL atomic convention, and the explicit BH readout. -/

/-- PDF p.3 Eqs.(5),(7): original atomic g1,g2 coefficients, both positive. -/
def oneAtomKet : EuclideanSpace ℂ (LambdaEnergyBasis 2 1 1) :=
  WithLp.toLp 2 fun p =>
    if p.val.2 0 = 0 ∧ (p.val.1 0).val = 2 ∧ (p.val.1 1).val = 0 then
      (Real.sqrt (2 / 3 : ℝ) : ℂ)
    else if p.val.2 0 = 1 ∧ (p.val.1 0).val = 1 ∧ (p.val.1 1).val = 1 then
      (Real.sqrt (1 / 3 : ℝ) : ℂ) else 0

/-- PDF p.3 Eq.(8): original atomic g1 is down=0, g2 is up=1.
Our false qubit denotes the source's photon state |1>. -/
def bhReadout : Matrix (Qubits 2 × Fin 2) (LambdaEnergyBasis 2 1 1) ℂ :=
  fun x p => if h : (p.val.1 1).val < 3 then
    if (p.val.1 0).val + (p.val.1 1).val = 2 ∧ (p.val.2 0).val = x.2.val then
      QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding 2 x.1 ⟨(p.val.1 1).val, h⟩ else 0 else 0

/-- PDF p.3 Eq.(8): BH three-qubit state in the explicit computational basis. -/
def bhKet : EuclideanSpace ℂ (Qubits 2 × Fin 2) :=
  (Real.sqrt (2 / 3 : ℝ) : ℂ) • tensorVec (ket ![false, false]) (ket (0 : Fin 2)) +
  (Real.sqrt (1 / 6 : ℝ) : ℂ) •
    tensorVec (ket ![false, true] + ket ![true, false]) (ket (1 : Fin 2))

/-! Section IV: sampled fidelities and physical operations, including instruments. -/

/-- PDF p.7 Eq.(30): mean single-site fidelity on an arbitrary M-qubit density. -/
def meanCloneFidelity (M : ℕ) (rho : Matrix (Qubits M) (Qubits M) ℂ)
    (psi : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  (∑ k : Fin M, effectProb (pureDensity psi) (QAlgorithms.Papers.Independent.Support21.P18.siteReduction rho k)) / M

/-- PDF pp.7-8: invariance under every exchange, without assuming Bose support. -/
def ExchangeInvariant (M : ℕ) (rho : Matrix (Qubits M) (Qubits M) ℂ) : Prop :=
  ∀ i j : Fin M, ∀ x y : Qubits M,
    rho (x ∘ Equiv.swap i j) (y ∘ Equiv.swap i j) = rho x y

/-- PDF p.7 Eq.(30): photon relative frequency, pulled back through the actual
Bose occupation embedding, for any desired polarization. -/
def photonFrequency (M : ℕ) (rho : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    (psi : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  meanCloneFidelity M (photonDensity M rho) psi

/-- PDF p.8: physical finite-dimensional selected operation in Kraus form,
with its trace-nonincreasing effect explicitly positive. -/
def FiniteKrausBranch {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (T : Superop I J) : Prop :=
  ∃ n : ℕ, ∃ E : Fin n → Matrix J I ℂ,
    (1 - ∑ k, (E k)ᴴ * E k).PosSemidef ∧ ∀ rho, T rho = krausApply E rho

/-- PDF p.8: equivalence map on physical totally symmetric qubit operators,
zero-extended on the orthogonal complement of the input Bose space. -/
def toQubitMap (m M : ℕ) (T : Superop (Fin (m + 1)) (Fin (M + 1))) :
    Superop (Qubits m) (Qubits M) :=
  fun rho => QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M *
    T ((QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m)ᴴ * rho * QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m) * (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M)ᴴ

/-- PDF p.8: inverse map, compression into the real occupation coordinates. -/
def toPhotonMap (m M : ℕ) (T : Superop (Qubits m) (Qubits M)) :
    Superop (Fin (m + 1)) (Fin (M + 1)) :=
  fun rho => (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M)ᴴ *
    T (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m * rho * (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m)ᴴ) * QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M

/-- PDF p.8: physical channel on the Bose corner in Bool tensor coordinates.
A finite Kraus extension is CP; only the Bose corner has trace preservation. -/
def BoseChannel (m M : ℕ) (T : Superop (Qubits m) (Qubits M)) : Prop :=
  let P := QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m * (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding m)ᴴ
  let Q := QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M * (QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding M)ᴴ
  (∃ n : ℕ, ∃ E : Fin n → Matrix (Qubits M) (Qubits m) ℂ,
    ∀ rho, T rho = krausApply E rho) ∧
  (∀ rho, T rho = T (P * rho * P)) ∧
  (∀ rho, Q * T rho * Q = T rho) ∧
  ∀ rho, (T rho).trace = (P * rho * P).trace

/-- PDF p.8: scalar success probability of a covariant selected photon map,
computed on a fixed reference input. -/
def mapWeight (m M : ℕ) (T : Superop (Fin (m + 1)) (Fin (M + 1))) : ℝ :=
  (T (pureDensity (ket (0 : Fin (m + 1))))).trace.re

/-- PDF p.8: fixed scalar normalization, not nonlinear division by rho's trace. -/
def normalizeMap (m M : ℕ) (T : Superop (Fin (m + 1)) (Fin (M + 1))) :
    Superop (Fin (m + 1)) (Fin (M + 1)) :=
  fun rho => ((mapWeight m M T : ℂ)⁻¹) • T rho

/-! Appendix B is an explicitly different Hamiltonian approximation. -/

/-- PDF pp.9-10 Eq.(B1): leading large-m generator, with exact zero boundaries. -/
def leadingTransfer (A m : ℕ) (gamma : ℝ) :
    Matrix (Fin (A + 1)) (Fin (A + 1)) ℂ :=
  fun k l => if k.val = l.val + 1 then
    (gamma * Real.sqrt m * Real.sqrt ((l.val + 1 : ℝ) * (A - l.val)) : ℂ)
  else if l.val = k.val + 1 then
    (gamma * Real.sqrt m * Real.sqrt ((k.val + 1 : ℝ) * (A - k.val)) : ℂ)
  else 0

/-- PDF p.10 Eq.(B2): coefficients obtained by exponentiating B1. -/
def leadingAmplitude (A m : ℕ) (gamma t : ℝ) (l : Fin (A + 1)) : ℂ :=
  QAlgorithms.Papers.Independent.Claimed50.P15.propagator (leadingTransfer A m gamma) t l 0

/-- PDF p.10 Eq.(B3): the actual measurement probabilities in the B1 model. -/
def leadingProbability (A m : ℕ) (gamma t : ℝ) (l : Fin (A + 1)) : ℝ :=
  Complex.normSq (leadingAmplitude A m gamma t l)

/-! Additional construction sanity checks. -/

example : pairKet (0, 1) 2 = (Real.sqrt 2 : ℂ)⁻¹ ∧
    pairKet (1, 0) 2 = -(Real.sqrt 2 : ℂ)⁻¹ := by
  norm_num [pairKet]

example (m : ℕ) (gamma : ℝ) : leadingTransfer 0 m gamma = 0 := by
  ext k l
  have hk : k.val = 0 := by omega
  have hl : l.val = 0 := by omega
  simp [leadingTransfer, hk, hl]

example (M : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    meanCloneFidelity M 0 psi = 0 := by
  have hsite (k : Fin M) :
      QAlgorithms.Papers.Independent.Support21.P18.siteReduction
        (0 : Matrix (Qubits M) (Qubits M) ℂ) k = 0 := by
    ext a b
    simp [QAlgorithms.Papers.Independent.Support21.P18.siteReduction]
  simp [meanCloneFidelity, hsite, effectProb]

example (A m l : ℕ) (gamma t : ℝ)
    (rho : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    normalizedBranch A m l gamma t rho =
      ((emissionBranchWeight A m l gamma t : ℂ)⁻¹) • physicalBranch A m l gamma t rho := rfl

example (A m l : ℕ) (hl : A < l) : emissionSectorKet A m l = 0 := by
  ext p
  simp [emissionSectorKet, Nat.not_le.mpr hl]

example (A m l : ℕ) (hl : A < l) : selectExcited A m l = 0 := by
  ext p q
  simp [selectExcited, Nat.not_le.mpr hl]

example (A m : ℕ) (p q : OscBasis 2 A m) : fiveH A m 0 p q = 0 := by
  simp [fiveH]

example (A m : ℕ) (p q : VBasis A m) : vH A m 0 p q = 0 := by
  simp [vH]

example (A : ℕ) (w : VWord A) : vExcited w =
    ∑ k, (Finset.univ.filter fun s : Fin 2 => (w k s).val < 2).card := rfl

example (A m l : ℕ) (gamma t : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) :
    excitedOutcomeProbability A m l gamma t psi =
      ‖act (selectExcited A m l) (physicalOutput A m gamma t psi)‖ ^ 2 := rfl

/-- PDF pp.3-4: atom permutations act on the full energy sector. -/
def atomPermutation (A m : ℕ) (pi : Equiv.Perm (Fin A)) :
    Matrix (LambdaEnergyBasis 2 A m) (LambdaEnergyBasis 2 A m) ℂ :=
  fun p q => if p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 ∘ pi.symm then 1 else 0

/-- PDF p.8: universal operation on the physical Bose input/output corners. -/
def BoseUniversal (m M : ℕ) (T : Superop (Qubits m) (Qubits M)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, ∀ rho,
    T (QAlgorithms.Papers.Independent.Support21.P18.tensorRotation m U.val * rho *
      (QAlgorithms.Papers.Independent.Support21.P18.tensorRotation m U.val)ᴴ) =
    QAlgorithms.Papers.Independent.Support21.P18.tensorRotation M U.val * T rho *
      (QAlgorithms.Papers.Independent.Support21.P18.tensorRotation M U.val)ᴴ

end QAlgorithms.Papers.Independent.Intake100.P37


