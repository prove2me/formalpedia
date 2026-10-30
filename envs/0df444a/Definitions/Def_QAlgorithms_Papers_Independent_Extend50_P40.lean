-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40
-- name    : QAlgorithms_Papers_Independent_Extend50_P40
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:51:43.88225+00:00
-- url     : https://prove2.me/theorems/71066866-e026-4821-b700-b82628cf4f5b
-- title:
--   Definitions for Quantum cloning
-- statement:
--   The objects the formalized statements of *Quantum cloning* (arXiv:quant-ph/0511088) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Triple`
--   - `finBlochDensity`: Appendix A pp.30–31: rho(m) for real Bloch coordinates.
--   - `densityBloch`: Appendix A p.30: the Bloch coordinates computed from a qubit density.
--   - `vectorBloch`: Appendix A p.30: corrected y sign, compatible with the frozen Pauli Y.
--   - `orthogonalQubit`: II.A.3 p.8: psi perpendicular, with the source's phase convention.
--   - `depol`: II.B p.9: radial mixture, extended linearly to arbitrary operators.
--   - `bellBasisState`: Appendix A p.30: Bell order Phi+,Phi-,Psi+,Psi-.
--   - `equator`: II.D p.11 Eq.(35): normalized equatorial input, phase in radians.
--   - `cloneMarginalA`: II.A p.8: partial traces of an actual three-register pure output.
--   - `cloneMarginalB`: II.A p.8: B is the first register of the B–machine pair.
--   - `marginalMachine`: II.A p.8: machine register M is traced last.
--   - `cloneChannel`: I.D p.5: a fixed isometry's AB output channel, machine discarded.
--   - `bhMatrix`: II.A p.8 Eq.(12), corrected: sqrt(1/3) on normalized Psi+ in BOTH columns. The minus on the input |1> is retained. The printed sqrt(1/6) in column 2 has squared norm 5/6 and contradicts Eq.(13).
--   - `bhOutput`: II.A p.8: the linear Buzek–Hillery output on an arbitrary qubit vector.
--   - `NoSignalingFamily`: I.E p.6: the larger no-signaling model; no channel hypothesis is imposed. Covariance (9) is an explicit assumption, independently of equal fidelities.
--   - `singleFidelity`: II.B p.9: each site's fidelity is the trace of the actual site observable.
--   - `UniformCloner`: I.D p.5: universality and symmetry mean ONE common fidelity for all inputs/sites. This does not impose Bose support or covariance on competitors.
--   - `optimalSingle`: II.B p.9 Eq.(21): numerical common pure-state fidelity.
--   - `shuffleCloner`: II.B p.9 Eq.(22): incoherent shuffling after appending maximally mixed blanks. The Bose compression fixes the accepted corner domain, not the output domain.
--   - `sphereAverage`: II.A p.7 Eq.(10): normalized spherical average, uniform azimuth and z. This is probability measure sin(theta)dtheta dphi/(4pi), with z=cos(theta).
--   - `randomBasisCloner`: II.A p.7: actual random-basis measurement and two copies of its outcome. Complex traces preserve linearity on non-Hermitian inputs.
--   - `distributor`: II.C pp.10–11 Fig.2: B+=A; M+=A; A-=B; A+=M (all modulo d). The resulting basis permutation is (s-w+x,s+w,s+x), NOT the mod-two formula.
--   - `program`: II.C pp.10–11 Eq.(27): fixed program, independently of the unknown psi.
--   - `distributorOutput`: II.C pp.10–11: processor applied to input tensor program.
--   - `asymmetricOutput`: II.C Eq.(27): coherent identity/swap output, in the source tensor order.
--   - `QubitTradeoff`: II.C p.10 Eq.(23): the sharp qubit asymmetric fidelity inequality.
--   - `onFirstTwo`: II.C p.11 Eqs.(31),(32), II.D p.12 Eq.(42): extend an AB operator by identity on M and reindex ((A,B),M) to the fixed (A,(B,M)) order.
--   - `cerfQubit`: II.C p.11 Eq.(31): Cerf's ambient operator, not generally unitary.
--   - `cerfWeyl`: II.C p.11 Eq.(33): positive Fourier sign, shift k+m modulo d.
--   - `cerfQudit`: II.C p.11 Eq.(32), corrected: the second Weyl operator is its ADJOINT. Printed U tensor U fails the swap identity and even the d=2 symmetric test.
--   - `twoStateFidelity`: II.D p.11 Eq.(34), orthogonal case defined separately to avoid 1/0.
--   - `economicMatrix`: II.D p.12 Eq.(39): the economical isometry on input times blank |0>.
--   - `economicOutput`: II.D p.12: the actual economical output.
--   - `phaseClonerMatrix`: II.D p.12 Eq.(41): restriction to input psi_A tensor Phi+_BM.
--   - `phaseOutput`: II.D p.12: phase cloner with machine retained.
--   - `phaseCerf`: II.D p.12 Eq.(42): parentheses keep I_M outside the WHOLE Pauli sum.
--   - `asymmetryFilter`: VI.A p.26 Eq.(103): a Kraus contraction, generally not a projector.
--   - `filteredOutput`: VI.A p.26: successful unnormalized state; filter acts on B and machine.
--   - `symmetricPair`: VI.A p.25 Eq.(101): symmetric two-photon projection.
--   - `bunching`: VI.A p.25: bunching success operation, before conditioning.
--   - `Estimator`: II.E pp.13–14: a finite estimator POVM on the actual N-copy Bose corner.
--   - `estimationOutput`: II.E p.13: restored N-fold input in the outcome probability.
--   - `estimationShrink`: II.E p.14: coefficient of the optimal qubit estimator.
--   - `binaryInformation`: IV.B pp.20–22: mutual information of uniform binary variables with agreement p.
--   - `rawRate`: IV.B p.20 Eq.(81): displayed raw information rate, without preprocessing.
--   - `economicLaw`: IV.B p.21: actual sifted x-basis law of the economical attack; bits are uniform.
--   - `classicalMutualInformation`: IV.B p.20: mutual information in bits, with the standard 0 log 0 convention. Only genuine normalized finite probability laws occur in statements.
--   - `infoAB`: IV.B p.21: marginal AB of a three-bit law.
--   - `infoAE`: IV.B p.21: marginal AE of a three-bit law.
--   - `infoBE`: IV.B p.21: marginal BE of a three-bit law.
--   - `eveGivenAlice`: IV.B pp.21–22: Eve's actual two-qubit state given Alice's raw bit.
--   - `eveGivenBob`: IV.C p.22: Eve's conditional state given Bob's equiprobable sifted bit. The factor two is Bayes normalization, not an assumed independent output.
--   - `binaryHolevo`: IV.C p.22 Eq.(86): equiprobable binary Holevo quantity, in bits.
--   - `collectiveRate`: IV.C p.22 Eq.(85): the stated attack's raw collective rate.
--   - `bellDecoder`: IV.B p.21: the specified Bell-to-computational decoder, retaining phases.
--   - `discriminationState`: IV.B p.22: the binary pure states to be discriminated after reading Eve's flag.
--   - `decodedAttack`: IV.B pp.21–22 Eq.(84): normalized state after the fixed Bell decoder.
--   - `flagFactorization`: IV.B pp.21–22 Eq.(84): factorization displaying the deterministic error flag.
--   - `ancillaLaw`: IV.B p.22: Eve reads E2 in Z and E1 in X after the Bell decoder.
--   - `measureNot`: II.A.3 p.8 footnote 10: random-basis estimate followed by the opposite state.
--   - `spherical`: Appendix A p.30 Eq.(A4): spherical representative of a pure-state ray.
--   - `pdcFirstOrder`: VI.A.1 p.25 Eq.(97): normalized first-order singlet-pair creation amplitude. The two signal photons are represented in their normalized symmetric tensor sector.
--   - `bunchingVector`: VI.A.1 pp.25–26: the selected three-photon bunching amplitude, before normalization.
--   - `modeEmission`: VI.A.3 p.28 Eq.(105): coherent equal-coupling one-emission map for d modes. The two signal factors are symmetrized and the emitting ground mode is retained. This constructs the action on superpositions, rather than specifying basis fidelities.
--   - `modeOutput`: VI.A.3 p.28: actual output vector in the selected one-emission sector.
--   - `oneModeOccupation`: III.A p.15: identify a one-mode occupation tuple with its sole photon number.
--   - `oneModeCoordinates`: III.A p.15: the complete one-mode Fock space in the source's tuple coordinates. This is only a basis relabeling; no cutoff, state choice or extra hypothesis.
--   - `oneModeProjector`: III.A p.15: reuse the frozen coherent projector, transported to one-mode occupation tuples by unitary conjugation. No coherent state is redefined here.
--   - `noiseWeight`: III.A p.15 Eq.(53): normalized complex-plane noise density; t means sigma^2.
--   - `gaussianMixture`: III.A p.15 Eq.(53): actual operator-valued mixture, with the t=0 boundary set to the pure density rather than Lean's zero value of a singular integral.
--   - `OscillatorCloner`: III.A p.15: a Stinespring isometry represents a fixed normal CPTP channel. One full oscillator environment is separable and accommodates arbitrary countable Kraus rank; no photon cutoff is introduced in any register.
--   - `coherentReplicas`: III.A p.15: identical coherent input replicas, no extra input degrees of freedom.
--   - `permuteCloneOccupation`: III.A p.15: permutation of the M clone modes leaving the environment fixed.
--   - `SymmetricGaussian`: III.A p.15: exactly the source SGC restrictions on coherent inputs. Bose support is retained, but no all-input Gaussian channel action is assumed.
--   - `priorWeight`: III.C p.19 Eq.(79): normalized prior density, Sigma>0 required in uses.
--   - `priorGain`: III.C p.19: physically allowed gain. The printed gain formula is restricted to the broad-prior branch; below the threshold G=1, forced by Eq.(80).
--   - `priorFidelity`: III.C p.19 Eq.(80): reciprocal in the narrow-prior branch, as printed.
--   - `priorClone`: III.C p.19: one actual reduced clone of the amplifier/splitter construction.
--   - `priorIntegrand`: III.C p.19: average figure of merit; no pointwise universality is required.
--   - `DisplacementNoise`: III.A.2 p.16: centered displacement noise with finite added quadrature variances. A genuine probability measure supplies symmetric classical covariance; no defective frozen moment predicate is used. Singular noise laws are allowed.
--   - `addedX`: III.A.2 p.16: added x VARIANCE, not standard deviation or total output variance.
--   - `addedP`: III.A.2 p.16: added p variance in the hbar=1 convention.
--   - `noiseMixture`: III.A.2 p.16: displacement alpha=(x+i p)/sqrt(2), with a fixed law independent of the unknown coherent input.
--   - `EmissionSector`: V.B p.24 Eq.(93): permutation-symmetric atomic sector, with i photons emitted into the wrong polarization, j into the initial polarization, and A-i-j atoms still excited. This is an exact finite excitation sector, not a cutoff.
--   - `emissionRaising`: V.B p.24 Eq.(93): stimulated creation part in the normalized symmetric atomic occupation basis. The square roots include BOTH photon and atom occupation factors. N input photons and A excited atoms are different parameters.
--   - `emissionHamiltonian`: V.B p.24 Eq.(93): full Hermitian equal-coupling Hamiltonian on the conserved sector. Reabsorption is retained by adding the adjoint.
--   - `emissionInitial`: V.B p.24: all A atoms excited, no new photons yet.
--   - `emissionState`: V.B p.24: FULL e^(-iHt) evolution, not just the H^k short-time term.
--   - `emissionProbability`: V.B p.24 Eq.(92): unnormalized joint probability of k added photons, l of them in the initial polarization. Impossible events have probability zero.
--   - `emissionSuccess`: V.B p.24 Eq.(91): physical probability of the selected photon count.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, https://arxiv.org/abs/quant-ph/0511088v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

/-!
arXiv:quant-ph/0511088v1, Quantum cloning. PDF pages are cited throughout.
Reviewed paper imports are used under the independent-paper workflow override.
All new objects are local; no frozen module is modified. The six exact reuse
nodes have no duplicate theorem here. Source corrections are recorded in the
audit artifacts. Compilation and independent moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius
open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)
open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Triple (d : ℕ) := Fin d × (Fin d × Fin d)

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)
open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- Appendix A pp.30–31: rho(m) for real Bloch coordinates. -/
def finBlochDensity (m : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (QAlgorithms.Papers.Independent.Renew46.P24.blochDensity m).submatrix
    (fun i => decide (i = 1)) (fun j => decide (j = 1))

/-- Appendix A p.30: the Bloch coordinates computed from a qubit density. -/
def densityBloch (rho : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ := fun k => (rho * sigma k).trace.re

/-- Appendix A p.30: corrected y sign, compatible with the frozen Pauli Y. -/
def vectorBloch (psi : EuclideanSpace ℂ (Fin 2)) : Fin 3 → ℝ :=
  ![2 * (conj (psi 0) * psi 1).re, 2 * (conj (psi 0) * psi 1).im,
    Complex.normSq (psi 0) - Complex.normSq (psi 1)]

/-- II.A.3 p.8: psi perpendicular, with the source's phase convention. -/
def orthogonalQubit (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![-conj (psi 1), conj (psi 0)]

/-- II.B p.9: radial mixture, extended linearly to arbitrary operators. -/
def depol {d : ℕ} (eta : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (eta : ℂ) • A + (((1 - eta : ℝ) : ℂ) * A.trace) • oneMixed d

/-- Appendix A p.30: Bell order Phi+,Phi-,Psi+,Psi-. -/
def bellBasisState (k : Fin 4) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    (if k = 0 then ket (0, 0) + ket (1, 1)
     else if k = 1 then ket (0, 0) - ket (1, 1)
     else if k = 2 then ket (0, 1) + ket (1, 0)
     else ket (0, 1) - ket (1, 0))

/-- II.D p.11 Eq.(35): normalized equatorial input, phase in radians. -/
def equator (theta : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.sqrt 2 : ℂ)⁻¹,
    Complex.exp (Complex.I * (theta : ℂ)) / (Real.sqrt 2 : ℂ)]

/-- II.A p.8: partial traces of an actual three-register pure output. -/
def cloneMarginalA {d : ℕ} (psi : EuclideanSpace ℂ (Triple d)) : Matrix (Fin d) (Fin d) ℂ :=
  traceRight (pureDensity psi)

/-- II.A p.8: B is the first register of the B–machine pair. -/
def cloneMarginalB {d : ℕ} (psi : EuclideanSpace ℂ (Triple d)) : Matrix (Fin d) (Fin d) ℂ :=
  traceRight (traceLeft (pureDensity psi))

/-- II.A p.8: machine register M is traced last. -/
def marginalMachine {d : ℕ} (psi : EuclideanSpace ℂ (Triple d)) : Matrix (Fin d) (Fin d) ℂ :=
  traceLeft (traceLeft (pureDensity psi))

/-- I.D p.5: a fixed isometry's AB output channel, machine discarded. -/
def cloneChannel {d : ℕ} (V : Matrix (Triple d) (Fin d) ℂ) : Superop (Fin d) (Fin d × Fin d) :=
  fun A p q => ∑ m, (V * A * Vᴴ) (p.1, (p.2, m)) (q.1, (q.2, m))

/-- II.A p.8 Eq.(12), corrected: sqrt(1/3) on normalized Psi+ in BOTH columns.
The minus on the input |1> is retained. The printed sqrt(1/6) in column 2
has squared norm 5/6 and contradicts Eq.(13). -/
def bhMatrix : Matrix (Triple 2) (Fin 2) ℂ :=
  fun p i => if i = 0 then
    if p = (0, (0, 1)) then (Real.sqrt (2 / 3) : ℂ)
    else if p = (0, (1, 0)) ∨ p = (1, (0, 0)) then -(Real.sqrt (1 / 6) : ℂ)
    else 0
  else
    if p = (1, (1, 0)) then -(Real.sqrt (2 / 3) : ℂ)
    else if p = (0, (1, 1)) ∨ p = (1, (0, 1)) then (Real.sqrt (1 / 6) : ℂ)
    else 0

/-- II.A p.8: the linear Buzek–Hillery output on an arbitrary qubit vector. -/
def bhOutput (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 (bhMatrix.mulVec psi)

/-- I.E p.6: the larger no-signaling model; no channel hypothesis is imposed.
Covariance (9) is an explicit assumption, independently of equal fidelities. -/
def NoSignalingFamily (F : Superop (Fin 2) (Fin 2 × Fin 2)) (eta : ℝ) : Prop :=
  (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
    IsDensityMatrix (F (pureDensity psi)) ∧
    traceRight (F (pureDensity psi)) = depol eta (pureDensity psi) ∧
    traceLeft (F (pureDensity psi)) = depol eta (pureDensity psi)) ∧
  (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (psi : EuclideanSpace ℂ (Fin 2)), ‖psi‖ = 1 →
    F ((U : Matrix (Fin 2) (Fin 2) ℂ) * pureDensity psi * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) =
      Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) * F (pureDensity psi) *
        (Matrix.kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) ∧
  F (pureDensity (equator 0)) + F (pureDensity (equator Real.pi)) =
    F (pureDensity (ket (0 : Fin 2))) + F (pureDensity (ket (1 : Fin 2)))

/-- II.B p.9: each site's fidelity is the trace of the actual site observable. -/
def singleFidelity {d N M : ℕ} (T : CloneMap d N M) (psi : EuclideanSpace ℂ (Fin d)) (j : Fin M) : ℝ :=
  (siteObservable (pureDensity psi) j * T (pureDensity (coherentTensor N psi))).trace.re

/-- I.D p.5: universality and symmetry mean ONE common fidelity for all inputs/sites.
This does not impose Bose support or covariance on competitors. -/
def UniformCloner {d N M : ℕ} (T : CloneMap d N M) (f : ℝ) : Prop :=
  ∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 → ∀ j : Fin M, singleFidelity T psi j = f

/-- II.B p.9 Eq.(21): numerical common pure-state fidelity. -/
def optimalSingle (d N M : ℕ) : ℝ :=
  (N : ℝ) / M + ((M : ℝ) - N) * (N + 1) / (M * ((N : ℝ) + d))

/-- II.B p.9 Eq.(22): incoherent shuffling after appending maximally mixed blanks.
The Bose compression fixes the accepted corner domain, not the output domain. -/
def shuffleCloner {d N M : ℕ} (hNM : N ≤ M) : CloneMap d N M :=
  fun A => ((d : ℂ)⁻¹ ^ (M - N) *
    (Fintype.card (Equiv.Perm (Fin M)) : ℂ)⁻¹) •
    ∑ p : Equiv.Perm (Fin M),
      let P := QAlgorithms.Schur.tensorPermutation d M p
      P * tensorWithIdentity hNM (boseProjector d N * A * boseProjector d N) * Pᴴ

/-- II.A p.7 Eq.(10): normalized spherical average, uniform azimuth and z.
This is probability measure sin(theta)dtheta dphi/(4pi), with z=cos(theta). -/
def sphereAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin 3 → ℝ) → E) : E :=
  (1 / (4 * Real.pi) : ℝ) •
    ∫ a in (0 : ℝ)..(2 * Real.pi), ∫ z in (-1 : ℝ)..1,
      f ![Real.sqrt (1 - z ^ 2) * Real.cos a,
          Real.sqrt (1 - z ^ 2) * Real.sin a, z]

/-- II.A p.7: actual random-basis measurement and two copies of its outcome.
Complex traces preserve linearity on non-Hermitian inputs. -/
def randomBasisCloner (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  sphereAverage fun b =>
    let P := finBlochDensity b
    let Q := 1 - P
    (P * A).trace • Matrix.kronecker P P + (Q * A).trace • Matrix.kronecker Q Q

/-- II.C pp.10–11 Fig.2: B+=A; M+=A; A-=B; A+=M (all modulo d).
The resulting basis permutation is (s-w+x,s+w,s+x), NOT the mod-two formula. -/
def distributor (d : ℕ) : Matrix (Triple d) (Triple d) ℂ :=
  fun y x => if y = (x.1 - x.2.1 + x.2.2, (x.1 + x.2.1, x.1 + x.2.2)) then 1 else 0

/-- II.C pp.10–11 Eq.(27): fixed program, independently of the unknown psi. -/
def program (d : ℕ) (a b : ℝ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  (a : ℂ) • QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d) + (b : ℂ) •
    WithLp.toLp 2 (fun p => if p.1.val = 0 then (Real.sqrt d : ℂ)⁻¹ else 0)

/-- II.C pp.10–11: processor applied to input tensor program. -/
def distributorOutput {d : ℕ} (a b : ℝ) (psi : EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Triple d) :=
  WithLp.toLp 2 ((distributor d).mulVec (tensorVec psi (program d a b)))

/-- II.C Eq.(27): coherent identity/swap output, in the source tensor order. -/
def asymmetricOutput {d : ℕ} (a b : ℝ) (psi : EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Triple d) :=
  WithLp.toLp 2 fun p => (a : ℂ) * psi p.1 * QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d) p.2 +
    (b : ℂ) * psi p.2.1 * QAlgorithms.Papers.Independent.Information100.P22.bell (Fin d) (p.1, p.2.2)

/-- II.C p.10 Eq.(23): the sharp qubit asymmetric fidelity inequality. -/
def QubitTradeoff (fA fB : ℝ) : Prop :=
  1 / 2 - (1 - fA) - (1 - fB) ≤ Real.sqrt ((1 - fA) * (1 - fB))

/-- II.C p.11 Eqs.(31),(32), II.D p.12 Eq.(42): extend an AB operator
by identity on M and reindex ((A,B),M) to the fixed (A,(B,M)) order. -/
def onFirstTwo {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Triple d) (Triple d) ℂ :=
  (Matrix.kronecker A (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
    (fun p => ((p.1, p.2.1), p.2.2)) (fun q => ((q.1, q.2.1), q.2.2))

example {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (p q : Triple d) :
    onFirstTwo A p q = A (p.1, p.2.1) (q.1, q.2.1) *
      (1 : Matrix (Fin d) (Fin d) ℂ) p.2.2 q.2.2 := rfl

/-- II.C p.11 Eq.(31): Cerf's ambient operator, not generally unitary. -/
def cerfQubit (v x : ℝ) : Matrix (Triple 2) (Triple 2) ℂ :=
  onFirstTwo ((v : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
    (x : ℂ) • ∑ k : Fin 3, Matrix.kronecker (sigma k) (sigma k))

/-- II.C p.11 Eq.(33): positive Fourier sign, shift k+m modulo d. -/
def cerfWeyl (d : ℕ) (m n : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  letI : NeZero d := ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le m.val) m.isLt)⟩
  let e := ZMod.finEquiv d
  (QAlgorithms.Papers.Independent.Information100.P34.weyl (e m) (e n)).submatrix e e

/-- II.C p.11 Eq.(32), corrected: the second Weyl operator is its ADJOINT.
Printed U tensor U fails the swap identity and even the d=2 symmetric test. -/
def cerfQudit (d : ℕ) (v x : ℝ) : Matrix (Triple d) (Triple d) ℂ :=
  onFirstTwo ((v : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) +
    (x : ℂ) • ∑ m : Fin d, ∑ n : Fin d,
      if m.val = 0 ∧ n.val = 0 then 0
      else Matrix.kronecker (cerfWeyl d m n) (cerfWeyl d m n)ᴴ)

/-- II.D p.11 Eq.(34), orthogonal case defined separately to avoid 1/0. -/
def twoStateFidelity (s : ℝ) : ℝ := if s = 0 then 1 else
  1 / 2 + Real.sqrt 2 / (32 * s) * (1 + s) *
    (3 - 3 * s + Real.sqrt (1 - 2 * s + 9 * s ^ 2)) *
    Real.sqrt (-1 + 2 * s + 3 * s ^ 2 + (1 - s) * Real.sqrt (1 - 2 * s + 9 * s ^ 2))

/-- II.D p.12 Eq.(39): the economical isometry on input times blank |0>. -/
def economicMatrix (theta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun p i => if i = 0 then if p = (0, 0) then 1 else 0
    else if p = (1, 0) then (Real.cos theta : ℂ)
    else if p = (0, 1) then (Real.sin theta : ℂ) else 0

/-- II.D p.12: the actual economical output. -/
def economicOutput (theta : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 ((economicMatrix theta).mulVec psi)

/-- II.D p.12 Eq.(41): restriction to input psi_A tensor Phi+_BM. -/
def phaseClonerMatrix (theta : ℝ) : Matrix (Triple 2) (Fin 2) ℂ :=
  fun p i => (Real.sqrt 2 : ℂ)⁻¹ *
    (if i = 0 then
      if p = (0, (0, 0)) then 1
      else if p = (0, (1, 1)) then (Real.cos theta : ℂ)
      else if p = (1, (0, 1)) then (Real.sin theta : ℂ) else 0
    else
      if p = (1, (0, 0)) then (Real.cos theta : ℂ)
      else if p = (0, (1, 0)) then (Real.sin theta : ℂ)
      else if p = (1, (1, 1)) then 1 else 0)

/-- II.D p.12: phase cloner with machine retained. -/
def phaseOutput (theta : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 ((phaseClonerMatrix theta).mulVec psi)

/-- II.D p.12 Eq.(42): parentheses keep I_M outside the WHOLE Pauli sum. -/
def phaseCerf (theta : ℝ) : Matrix (Triple 2) (Triple 2) ℂ :=
  let F := (1 + Real.cos theta) / 2
  onFirstTwo
    ((F : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + ((1 - F : ℝ) : ℂ) • Matrix.kronecker (sigma 2) (sigma 2) +
      (Real.sqrt (F * (1 - F)) : ℂ) •
        (Matrix.kronecker (sigma 0) (sigma 0) + Matrix.kronecker (sigma 1) (sigma 1)))

/-- VI.A p.26 Eq.(103): a Kraus contraction, generally not a projector. -/
def asymmetryFilter (T : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((2 * T - 1 : ℝ) : ℂ) • 1 + ((2 * (1 - T) : ℝ) : ℂ) • pureDensity (bellBasisState 3)

/-- VI.A p.26: successful unnormalized state; filter acts on B and machine. -/
def filteredOutput (T : ℝ) (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 ((Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (asymmetryFilter T)).mulVec (bhOutput psi))

/-- VI.A p.25 Eq.(101): symmetric two-photon projection. -/
def symmetricPair : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1 - pureDensity (bellBasisState 3)

/-- VI.A p.25: bunching success operation, before conditioning. -/
def bunching (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  symmetricPair * Matrix.kronecker A (oneMixed 2) * symmetricPair

/-- II.E pp.13–14: a finite estimator POVM on the actual N-copy Bose corner. -/
structure Estimator (N : ℕ) where
  outcomes : ℕ
  effects : Fin outcomes → TensorMat 2 N
  positive : ∀ i, (effects i).PosSemidef
  complete : ∑ i, effects i = boseProjector 2 N
  guess : Fin outcomes → EuclideanSpace ℂ (Fin 2)
  normalized : ∀ i, ‖guess i‖ = 1

/-- II.E p.13: restored N-fold input in the outcome probability. -/
def estimationOutput {N : ℕ} (E : Estimator N) (psi : EuclideanSpace ℂ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, (E.effects i * pureDensity (coherentTensor N psi)).trace • pureDensity (E.guess i)

/-- II.E p.14: coefficient of the optimal qubit estimator. -/
def estimationShrink (N : ℕ) : ℝ := (N : ℝ) / (N + 2)

/-- IV.B pp.20–22: mutual information of uniform binary variables with agreement p. -/
def binaryInformation (p : ℝ) : ℝ := 1 - binEntropy2 p

/-- IV.B p.20 Eq.(81): displayed raw information rate, without preprocessing. -/
def rawRate (iab iae ibe : ℝ) : ℝ := iab - min iae ibe

/-- IV.B p.21: actual sifted x-basis law of the economical attack; bits are uniform. -/
def economicLaw (theta : ℝ) (a b e : Bool) : ℝ :=
  (1 / 2) * pureFidelity
    (tensorVec (equator (if b then Real.pi else 0)) (equator (if e then Real.pi else 0)))
    (pureDensity (economicOutput theta (equator (if a then Real.pi else 0))))

/-- IV.B p.20: mutual information in bits, with the standard 0 log 0 convention.
Only genuine normalized finite probability laws occur in statements. -/
def classicalMutualInformation {I J : Type*} [Fintype I] [Fintype J] (p : I → J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i j * Real.log (p i j / ((∑ y, p i y) * ∑ x, p x j)) / Real.log 2

/-- IV.B p.21: marginal AB of a three-bit law. -/
def infoAB (p : Bool → Bool → Bool → ℝ) : ℝ :=
  classicalMutualInformation fun a b => ∑ e, p a b e

/-- IV.B p.21: marginal AE of a three-bit law. -/
def infoAE (p : Bool → Bool → Bool → ℝ) : ℝ :=
  classicalMutualInformation fun a e => ∑ b, p a b e

/-- IV.B p.21: marginal BE of a three-bit law. -/
def infoBE (p : Bool → Bool → Bool → ℝ) : ℝ :=
  classicalMutualInformation fun b e => ∑ a, p a b e

/-- IV.B pp.21–22: Eve's actual two-qubit state given Alice's raw bit. -/
def eveGivenAlice (theta : ℝ) (a : Bool) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  traceLeft (pureDensity (phaseOutput theta (equator (if a then Real.pi else 0))))

/-- IV.C p.22: Eve's conditional state given Bob's equiprobable sifted bit.
The factor two is Bayes normalization, not an assumed independent output. -/
def eveGivenBob (theta : ℝ) (b : Bool) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let average := (1 / 2 : ℂ) •
    (pureDensity (phaseOutput theta (equator 0)) + pureDensity (phaseOutput theta (equator Real.pi)))
  (2 : ℂ) • traceLeft
    (Matrix.kronecker (pureDensity (equator (if b then Real.pi else 0)))
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) * average)

/-- IV.C p.22 Eq.(86): equiprobable binary Holevo quantity, in bits. -/
def binaryHolevo {I : Type*} [Fintype I] [DecidableEq I]
    (rho0 rho1 : Matrix I I ℂ) : ℝ :=
  vnEntropy ((1 / 2 : ℂ) • (rho0 + rho1)) - (vnEntropy rho0 + vnEntropy rho1) / 2

/-- IV.C p.22 Eq.(85): the stated attack's raw collective rate. -/
def collectiveRate (theta : ℝ) : ℝ :=
  binaryInformation ((1 + Real.cos theta) / 2) -
    min (binaryHolevo (eveGivenAlice theta false) (eveGivenAlice theta true))
      (binaryHolevo (eveGivenBob theta false) (eveGivenBob theta true))

/-- IV.B p.21: the specified Bell-to-computational decoder, retaining phases. -/
def bellDecoder : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ k : Fin 4,
    if p = (![ (0, 0), (1, 1), (1, 0), (0, 1)] : Fin 4 → (Fin 2 × Fin 2)) k
    then conj (bellBasisState k q) else 0

/-- IV.B p.22: the binary pure states to be discriminated after reading Eve's flag. -/
def discriminationState (theta : ℝ) (bit : Bool) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.sqrt ((1 + Real.cos theta) / 2) : ℂ),
    (if bit then -1 else 1) * (Real.sqrt ((1 - Real.cos theta) / 2) : ℂ)]

/-- IV.B pp.21–22 Eq.(84): normalized state after the fixed Bell decoder. -/
def decodedAttack (theta : ℝ) (bit : Bool) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 ((Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) bellDecoder).mulVec
    (phaseOutput theta (equator (if bit then Real.pi else 0))))

/-- IV.B pp.21–22 Eq.(84): factorization displaying the deterministic error flag. -/
def flagFactorization (theta : ℝ) (bit : Bool) : EuclideanSpace ℂ (Triple 2) :=
  (Real.sqrt ((1 + Real.cos theta) / 2) : ℂ) •
      tensorVec (equator (if bit then Real.pi else 0)) (tensorVec (discriminationState theta bit) (ket (0 : Fin 2))) +
    ((if bit then 1 else -1) * (Real.sqrt ((1 - Real.cos theta) / 2) : ℂ)) •
      tensorVec (equator (if bit then 0 else Real.pi)) (tensorVec (discriminationState theta (!bit)) (ket (1 : Fin 2)))

/-- IV.B p.22: Eve reads E2 in Z and E1 in X after the Bell decoder. -/
def ancillaLaw (theta : ℝ) (a b : Bool) (e : Bool × Bool) : ℝ :=
  (1 / 2) * pureFidelity
    (tensorVec (equator (if b then Real.pi else 0))
      (tensorVec (equator (if e.1 then Real.pi else 0)) (ket (if e.2 then (1 : Fin 2) else 0))))
    (pureDensity (decodedAttack theta a))

/-- Appendix A: small tests pin the tensor order, Y sign and endpoint conventions. -/
example : sigma 1 0 1 = -Complex.I := by simp [sigma, QAlgorithms.QubitChannels.sigma, pauliY]

example : bhMatrix (0, (0, 1)) 0 = (Real.sqrt (2 / 3) : ℂ) := by simp [bhMatrix]

example : distributor 2 (1, (1, 1)) (1, (0, 0)) = 1 := by norm_num [distributor]

example : program 2 1 0 = QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2) := by simp [program]

example (psi : EuclideanSpace ℂ (Fin 2)) : asymmetricOutput 1 0 psi = tensorVec psi (QAlgorithms.Papers.Independent.Information100.P22.bell (Fin 2)) := by
  ext p
  simp [asymmetricOutput, tensorVec]

example : twoStateFidelity 0 = 1 := by simp [twoStateFidelity]

example : economicMatrix 0 (1, 0) 1 = 1 := by simp [economicMatrix]

example : asymmetryFilter 1 = 1 := by norm_num [asymmetryFilter]

example : estimationShrink 0 = 0 := by norm_num [estimationShrink]

example (f : (Fin 3 → ℝ) → ℝ) (h : ∀ b, f b = 0) : sphereAverage f = 0 := by
  simp [sphereAverage, h]

/-- II.A.3 p.8 footnote 10: random-basis estimate followed by the opposite state. -/
def measureNot (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sphereAverage fun b =>
    let P := finBlochDensity b
    let Q := 1 - P
    (P * A).trace • Q + (Q * A).trace • P

/-- Appendix A p.30 Eq.(A4): spherical representative of a pure-state ray. -/
def spherical (theta azimuth : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos (theta / 2) : ℂ),
    Complex.exp (Complex.I * (azimuth : ℂ)) * (Real.sin (theta / 2) : ℂ)]

/-- VI.A.1 p.25 Eq.(97): normalized first-order singlet-pair creation amplitude.
The two signal photons are represented in their normalized symmetric tensor sector. -/
def pdcFirstOrder (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 fun p => (Real.sqrt 6 : ℂ)⁻¹ * ∑ j : Fin 2,
    (psi p.1 * (if p.2.1 = j then 1 else 0) +
     (if p.1 = j then 1 else 0) * psi p.2.1) * orthogonalQubit (ket j) p.2.2

/-- VI.A.1 pp.25–26: the selected three-photon bunching amplitude, before normalization. -/
def bunchingVector (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Triple 2) :=
  WithLp.toLp 2 fun p => ∑ a : Fin 2, ∑ b : Fin 2,
    symmetricPair (p.1, p.2.1) (a, b) * psi a * bellBasisState 3 (b, p.2.2)

/-- VI.A.3 p.28 Eq.(105): coherent equal-coupling one-emission map for d modes.
The two signal factors are symmetrized and the emitting ground mode is retained.
This constructs the action on superpositions, rather than specifying basis fidelities. -/
def modeEmission (d : ℕ) : Matrix (Triple d) (Fin d) ℂ :=
  fun p i => (Real.sqrt (2 * ((d : ℝ) + 1)) : ℂ)⁻¹ *
    ((if p.1 = i ∧ p.2.1 = p.2.2 then 1 else 0) +
     (if p.2.1 = i ∧ p.1 = p.2.2 then 1 else 0))

/-- VI.A.3 p.28: actual output vector in the selected one-emission sector. -/
def modeOutput {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Triple d) :=
  WithLp.toLp 2 ((modeEmission d).mulVec psi)

example : spherical 0 0 = ket (0 : Fin 2) := by
  ext i
  fin_cases i <;> simp [spherical, ket]

example : measureNot 0 = 0 := by simp [measureNot, sphereAverage]

example (d : ℕ) : modeOutput (0 : EuclideanSpace ℂ (Fin d)) = 0 := by simp [modeOutput]

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator IsModeDensity FockWeylSystem)
open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProduct NormalizedCoherent IsReducedDensity FockCanonicalAction
   ModeUnitary twoModeAmplifierQuadratures modeMixingQuadratures embeddedOpticalBeam
   displacedThermal cloneNoise cloneFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentProjector)

/-- III.A p.15: identify a one-mode occupation tuple with its sole photon number. -/
def oneModeOccupation : (Fin 1 → ℕ) ≃ ℕ where
  toFun j := j 0
  invFun n := fun _ => n
  left_inv j := by
    funext k
    exact congrArg j (Subsingleton.elim (0 : Fin 1) k)
  right_inv _ := rfl

/-- III.A p.15: the complete one-mode Fock space in the source's tuple coordinates.
This is only a basis relabeling; no cutoff, state choice or extra hypothesis. -/
def oneModeCoordinates :
    QAlgorithms.Papers.Independent.Dependency50.P39.Fock ≃ₗᵢ[ℂ] ModeHilbert 1 where
  toLinearEquiv :=
    { toFun := fun u => ⟨fun j => u (oneModeOccupation j),
        memℓp_gen (oneModeOccupation.summable_iff.mpr
          ((lp.memℓp u).summable (by norm_num)))⟩
      invFun := fun u => ⟨fun n => u (oneModeOccupation.symm n),
        memℓp_gen (oneModeOccupation.symm.summable_iff.mpr
          ((lp.memℓp u).summable (by norm_num)))⟩
      left_inv := by intro u; ext n; simp
      right_inv := by intro u; ext j; simp
      map_add' := by intro u v; rfl
      map_smul' := by intro c u; rfl }
  norm_map' := by
    intro u
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact oneModeOccupation.tsum_eq (fun n => ‖u n‖ ^ (2 : ENNReal).toReal)

/-- III.A p.15: reuse the frozen coherent projector, transported to one-mode
occupation tuples by unitary conjugation. No coherent state is redefined here. -/
def oneModeProjector (alpha : ℂ) : ModeOperator 1 :=
  (oneModeCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (coherentProjector alpha)).comp
    oneModeCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap

example (n : ℕ) : oneModeOccupation (fun _ => n) = n := rfl

example (u : QAlgorithms.Papers.Independent.Dependency50.P39.Fock)
    (j : Fin 1 → ℕ) : oneModeCoordinates u j = u (j 0) := rfl

example (alpha : ℂ) : oneModeProjector alpha =
    (oneModeCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (coherentProjector alpha)).comp
      oneModeCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap := rfl

/-- III.A p.15 Eq.(53): normalized complex-plane noise density; t means sigma^2. -/
def noiseWeight (t : ℝ) (beta : ℂ) : ℝ :=
  Real.exp (-Complex.normSq beta / t) / (Real.pi * t)

/-- III.A p.15 Eq.(53): actual operator-valued mixture, with the t=0 boundary
set to the pure density rather than Lean's zero value of a singular integral. -/
def gaussianMixture (t : ℝ) (alpha : ℂ) : ModeOperator 1 :=
  if t = 0 then oneModeProjector alpha
  else ∫ beta : ℂ, (noiseWeight t beta : ℂ) • oneModeProjector (alpha + beta)

/-- III.A p.15: a Stinespring isometry represents a fixed normal CPTP channel.
One full oscillator environment is separable and accommodates arbitrary countable
Kraus rank; no photon cutoff is introduced in any register. -/
abbrev OscillatorCloner (N M : ℕ) := ModeHilbert N →ₗᵢ[ℂ] ModeHilbert (M + 1)

/-- III.A p.15: identical coherent input replicas, no extra input degrees of freedom. -/
def coherentReplicas (N : ℕ) (alpha : ℂ) : ModeHilbert N :=
  coherentProduct (fun _ : Fin N => alpha)

/-- III.A p.15: permutation of the M clone modes leaving the environment fixed. -/
def permuteCloneOccupation {M : ℕ} (p : Equiv.Perm (Fin M))
    (j : Fin (M + 1) → ℕ) : Fin (M + 1) → ℕ :=
  fun k => if h : k.val < M then j ⟨(p ⟨k.val, h⟩).val, by omega⟩ else j k

/-- III.A p.15: exactly the source SGC restrictions on coherent inputs.
Bose support is retained, but no all-input Gaussian channel action is assumed. -/
def SymmetricGaussian {N M : ℕ} (V : OscillatorCloner N M) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ alpha : ℂ,
    NormalizedCoherent (fun _ : Fin N => alpha) ∧
    (∀ p : Equiv.Perm (Fin M), ∀ j : Fin (M + 1) → ℕ,
      V (coherentReplicas N alpha) (permuteCloneOccupation p j) = V (coherentReplicas N alpha) j) ∧
    ∀ k : Fin M,
      IsReducedDensity
        (InnerProductSpace.rankOne ℂ (V (coherentReplicas N alpha)) (V (coherentReplicas N alpha)))
        ⟨k.val, by omega⟩ (gaussianMixture t alpha)

/-- III.C p.19 Eq.(79): normalized prior density, Sigma>0 required in uses. -/
def priorWeight (Sigma : ℝ) (alpha : ℂ) : ℝ :=
  Real.exp (-Complex.normSq alpha / (2 * Sigma ^ 2)) / (2 * Real.pi * Sigma ^ 2)

/-- III.C p.19: physically allowed gain. The printed gain formula is restricted
to the broad-prior branch; below the threshold G=1, forced by Eq.(80). -/
def priorGain (Sigma : ℝ) : ℝ :=
  if 1 / 2 + 1 / Real.sqrt 2 ≤ Sigma ^ 2 then 8 * Sigma ^ 4 / (2 * Sigma ^ 2 + 1) ^ 2 else 1

/-- III.C p.19 Eq.(80): reciprocal in the narrow-prior branch, as printed. -/
def priorFidelity (Sigma : ℝ) : ℝ :=
  if 1 / 2 + 1 / Real.sqrt 2 ≤ Sigma ^ 2 then (4 * Sigma ^ 2 + 2) / (6 * Sigma ^ 2 + 1)
  else 1 / ((3 - 2 * Real.sqrt 2) * Sigma ^ 2 + 1)

/-- III.C p.19: one actual reduced clone of the amplifier/splitter construction. -/
def priorClone (W : FockWeylSystem 1) (Sigma : ℝ) (alpha : ℂ) : ModeOperator 1 :=
  displacedThermal W ((Real.sqrt (priorGain Sigma / 2) : ℂ) * alpha) ((priorGain Sigma - 1) / 2)

/-- III.C p.19: average figure of merit; no pointwise universality is required. -/
def priorIntegrand (W : FockWeylSystem 1) (Sigma : ℝ) (alpha : ℂ) : ℝ :=
  priorWeight Sigma alpha *
    (inner ℂ (coherentProduct (fun _ : Fin 1 => alpha))
      (priorClone W Sigma alpha (coherentProduct (fun _ : Fin 1 => alpha)))).re

example (alpha : ℂ) : gaussianMixture 0 alpha = oneModeProjector alpha := by
  simp [gaussianMixture]

example : priorGain 0 = 1 := by norm_num [priorGain]; positivity

example {M : ℕ} (j : Fin (M + 1) → ℕ) :
    permuteCloneOccupation (Equiv.refl (Fin M)) j = j := by
  funext k
  simp [permuteCloneOccupation]

/-- III.A.2 p.16: centered displacement noise with finite added quadrature
variances. A genuine probability measure supplies symmetric classical covariance;
no defective frozen moment predicate is used. Singular noise laws are allowed. -/
structure DisplacementNoise where
  law : Measure (ℝ × ℝ)
  probability : IsProbabilityMeasure law
  finiteX : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) law
  finiteP : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) law
  centeredX : (∫ z : ℝ × ℝ, z.1 ∂law) = 0
  centeredP : (∫ z : ℝ × ℝ, z.2 ∂law) = 0

/-- III.A.2 p.16: added x VARIANCE, not standard deviation or total output variance. -/
def addedX (mu : DisplacementNoise) : ℝ := ∫ z : ℝ × ℝ, z.1 ^ 2 ∂mu.law

/-- III.A.2 p.16: added p variance in the hbar=1 convention. -/
def addedP (mu : DisplacementNoise) : ℝ := ∫ z : ℝ × ℝ, z.2 ^ 2 ∂mu.law

/-- III.A.2 p.16: displacement alpha=(x+i p)/sqrt(2), with a fixed law
independent of the unknown coherent input. -/
def noiseMixture (mu : DisplacementNoise) (alpha : ℂ) : ModeOperator 1 :=
  ∫ z : ℝ × ℝ,
    oneModeProjector (alpha + ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) / (Real.sqrt 2 : ℂ)) ∂mu.law

/-- V.B p.24 Eq.(93): permutation-symmetric atomic sector, with i photons
emitted into the wrong polarization, j into the initial polarization, and
A-i-j atoms still excited. This is an exact finite excitation sector, not a cutoff. -/
abbrev EmissionSector (A : ℕ) :=
  {q : Fin (A + 1) × Fin (A + 1) // q.1.val + q.2.val ≤ A}

/-- V.B p.24 Eq.(93): stimulated creation part in the normalized symmetric
atomic occupation basis. The square roots include BOTH photon and atom occupation
factors. N input photons and A excited atoms are different parameters. -/
def emissionRaising (N A : ℕ) : Matrix (EmissionSector A) (EmissionSector A) ℂ :=
  fun q r =>
    (if q.val.1 = r.val.1 ∧ q.val.2.val = r.val.2.val + 1 then
      (Real.sqrt (((N : ℝ) + r.val.2.val + 1) * (r.val.2.val + 1) *
        ((A : ℝ) - r.val.1.val - r.val.2.val)) : ℂ) else 0) +
    (if q.val.2 = r.val.2 ∧ q.val.1.val = r.val.1.val + 1 then
      (Real.sqrt ((r.val.1.val + 1 : ℝ) ^ 2 *
        ((A : ℝ) - r.val.1.val - r.val.2.val)) : ℂ) else 0)

/-- V.B p.24 Eq.(93): full Hermitian equal-coupling Hamiltonian on the conserved
sector. Reabsorption is retained by adding the adjoint. -/
def emissionHamiltonian (N A : ℕ) (g : ℝ) : Matrix (EmissionSector A) (EmissionSector A) ℂ :=
  (g : ℂ) • (emissionRaising N A + (emissionRaising N A)ᴴ)

/-- V.B p.24: all A atoms excited, no new photons yet. -/
def emissionInitial (A : ℕ) : EmissionSector A := ⟨(0, 0), by simp⟩

/-- V.B p.24: FULL e^(-iHt) evolution, not just the H^k short-time term. -/
def emissionState (N A : ℕ) (g t : ℝ) : EuclideanSpace ℂ (EmissionSector A) :=
  WithLp.toLp 2
    ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • emissionHamiltonian N A g)).mulVec
      (ket (emissionInitial A)))

/-- V.B p.24 Eq.(92): unnormalized joint probability of k added photons,
l of them in the initial polarization. Impossible events have probability zero. -/
def emissionProbability (N A k l : ℕ) (g t : ℝ) : ℝ :=
  ∑ q : EmissionSector A,
    if q.val.1.val + q.val.2.val = k ∧ q.val.2.val = l
    then Complex.normSq (emissionState N A g t q) else 0

/-- V.B p.24 Eq.(91): physical probability of the selected photon count. -/
def emissionSuccess (N A k : ℕ) (g t : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), emissionProbability N A k l g t

example (N A : ℕ) : emissionHamiltonian N A 0 = 0 := by
  simp [emissionHamiltonian]

example (A : ℕ) : (emissionInitial A).val = (0, 0) := rfl

end QAlgorithms.Papers.Independent.Extend50.P40


