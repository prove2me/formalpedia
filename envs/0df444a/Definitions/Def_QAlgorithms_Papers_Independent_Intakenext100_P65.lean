-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P65
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:22:34.625551+00:00
-- url     : https://prove2.me/theorems/df9bf7f1-caf0-4c9c-9900-679eeface4fa
-- title:
--   Definitions for Performance and structure of single-mode bosonic codes
-- statement:
--   The objects the formalized statements of *Performance and structure of single-mode bosonic codes* (arXiv:1708.05010) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FockCoordinates`: PDF pp.2--3: number-basis coordinates, prior to imposing the Hilbert domain.
--   - `fockDomain`: PDF p.2: the full oscillator Hilbert domain, expressed in its countable ONB.
--   - `fockNormSq`: PDF p.2: squared Hilbert norm on the square-summable domain.
--   - `fockInner`: PDF p.2: inner product, conjugate-linear in the first entry.
--   - `fockMomentDomain`: PDF pp.2,4: a finite photon-number moment has a summability domain.
--   - `numberMoment`: PDF pp.4,18: kth number moment, only used on `fockMomentDomain`.
--   - `codeMoment`: PDF p.4 (2.1): literal half-sum of the two logical number moments.
--   - `annPower`: PDF p.2: coefficient of a^k, including its factorial normalization.
--   - `annDomain`: PDF p.2: natural domain of the unbounded annihilation power.
--   - `lossCoefficient`: PDF p.2 (1.4): the exact loss coefficient for input occupation n, zero below l.
--   - `lossVector`: PDF p.2 (1.4): loss Kraus action on the full number basis.
--   - `qecBlock`: PDF p.8 (4.1): actual compression of E_l^dagger E_k, not a free QEC matrix.
--   - `qecC`: PDF p.8 (4.4): coefficient of the identity.
--   - `qecZ`: PDF p.8 (4.4): coefficient of logical Z in the chosen basis.
--   - `qecX`: PDF p.8 (4.4): coefficient of logical X, including nonsymmetric off-diagonal blocks.
--   - `liouvilleBasis`: PDF p.3 (1.8): I,X,Y,Z, using the accepted Bool-indexed Pauli matrices with Fin 2 labels 0,1 mapped to false,true.
--   - `liouville`: PDF p.3 (1.8): Pauli Liouville matrix; this is distinct from the Choi matrix.
--   - `traceReference`: PDF p.7 (3.3): trace over the reference, leaving the channel's output marginal.
--   - `reverseInformation`: PDF p.7 (3.3): reverse coherentCoordinates information, without capacity optimization. The frozen output-first Choi operator is unnormalized; multiplying by 1/2 gives the trace-one qubit Choi state in (1.9).
--   - `qubitFrobeniusSq`: PDF p.7 (3.4): squared Frobenius norm from accepted Advance50.P29, specialized to the effective qubit channel.
--   - `worstPureFidelity`: PDF p.24 (A2): minimum over normalized pure inputs; compactness and CPTP supply a nonempty bounded set, with attainment asserted below.
--   - `residueProject`: PDF p.9 (5.3): periodic residue projector, allowing signed residue labels.
--   - `coherentCoordinates`: PDF p.9: normalized coherentCoordinates-state coefficients for real amplitude a.
--   - `catNorm`: PDF p.9 (5.2): the actual projected coherentCoordinates-state probability.
--   - `catCodeCoordinates`: PDF p.9 (5.1): normalized projected coherentCoordinates coordinates; a>0 in every use.
--   - `residueCheck`: PDF p.9 (5.7): bounded number-phase rotation.
--   - `residueLogicalZ`: PDF p.9 following (5.7): the specified square root of the check is logical Z.
--   - `catNormFourier`: PDF p.9 (5.5): Fourier projection using exact coherentCoordinates-state overlaps.
--   - `catLossRatio`: PDF pp.9--11: probability ratios with signed residues, before taking any limit.
--   - `poissonWeight`: PDF p.10 (5.12): Poisson weight whose mean g*a^2 varies with a.
--   - `antipodal`: PDF p.14 (6.11): finite spin coefficients, indexed by twice the spin.
--   - `binomialCodeCoordinates`: PDF p.11 (6.1): direct full-Fock binomialCodeCoordinates coordinates.
--   - `binomialParity`: PDF p.12 (6.4): the positive/negative logical combinations.
--   - `binomialGenerator`: PDF p.12 (6.5): exact generating polynomial, with plus/minus sign.
--   - `spinX`: PDF p.14: standard spin-x matrix, on m=0,...,M for spin M/2.
--   - `embedOne`: PDF pp.14--15: transport of a coefficient vector to one mode.
--   - `embedTwo`: PDF p.15 Fig.7(a), p.27: two-mode transport with the spacing in BOTH occupations. Printed (6.16) drops a spacing factor; use the explicit preceding basis map.
--   - `qubitDickeCoordinates`: PDF p.15: accepted Information100.P22.dicke in Fin 2 word coordinates; Bool false,true correspond to 0,1. Infeasible excitation weights give zero.
--   - `embedDicke`: PDF p.15 (6.14): the spaced Dicke transport (K >= M(S+1) at use sites).
--   - `smallGenerator`: PDF p.17: even/odd spin generator on the stated seven-dimensional invariant space.
--   - `smallUnitary`: PDF p.17 (6.21): a=8,b=5, with identity extension outside the invariant space.
--   - `smallBasis`: PDF p.17 Tables II--III: actual normalized code, dephasing residual, loss, and failure vectors. Residual normalization is sqrt(3), correcting the false coefficient 2 in (6.20).
--   - `totalQuditExcitation`: PDF p.28 (C4): totalQuditExcitation of an M-qudit computational word.
--   - `extendedCount`: PDF p.27 (C2),(C4): number of words of a given total totalQuditExcitation.
--   - `extendedVector`: PDF p.27 (C4): normalized extended binomialCodeCoordinates vector, distinct from a general qudit Dicke vector.
--   - `quditFourierFactor`: PDF p.28 (C8): positive Fourier phase, matching the explicit backwards shift (C7).
--   - `extendedCoefficients`: PDF p.27 (C3): totalQuditExcitation-basis coefficients, including the endpoint (d-1)M.
--   - `permCode`: PDF p.27 (C3): the new multi-qudit code, in extended-binomialCodeCoordinates coordinates.
--   - `fourierProduct`: PDF p.28 (C9): tensor product of M identical Fourier vectors.
--   - `nextLabel`: PDF p.28 (C7): the input label one step above the output label.
--   - `collectiveShift`: PDF p.28 (C10): average of the backwards cyclic shifts on individual qudits.
--   - `compressedShift`: PDF p.28: compression to the extended-binomialCodeCoordinates span, of dimension (d-1)M+1.
--   - `weylPhase`: PDF p.28 (D1b): the positive Weyl convention.
--   - `lossEntry`: PDF p.2 (1.4): number-basis kernel of a single loss Kraus operator.
--   - `lossProduct`: PDF p.19 (7.12): genuine product kernel, before the displacement expansion.
--   - `lossDisplacementIntegrand`: PDF p.19 (7.12): integrand INCLUDING the factor 1/pi, on complex-plane Lebesgue measure.
--   - `fockDensity`: PDF pp.2,20: positive trace-one full Fock kernels. Positivity of every finite principal compression and summability of the nonnegative diagonal characterize positive trace-class operators; there is no fixed cutoff.
--   - `lossChannel`: PDF p.2: pure loss, by the countable Kraus sum on actual Fock kernels.
--   - `amplifierChannel`: PDF p.20 (7.20): amplification after loss; Kraus operators sqrt(1-g) E_l^dagger.
--   - `displaceDensity`: PDF p.20 (7.21): displacement conjugation, evaluated on all matrix entries.
--   - `amplifiedLossDensity`: PDF p.20 (7.21): density of the amplified-loss displacement distribution on C.
--   - `idealComb`: PDF p.18 (7.5): distributional square-code comb acting linearly on tests.
--   - `regularizedLattice`: PDF pp.18,29 (7.6),(D5): Gaussian-Abel regularized coherentCoordinates-lattice sum. The ordered product is D_real D_imag; it is evaluated on the vacuum in position coordinates.
--   - `kernelLattice`: PDF p.29 (D9): normalizer-lattice displacement, with signed mu-nu offset.
--   - `kernelPhase`: PDF p.29 (D9): phase for the positive Weyl convention.
--   - `idealDisplacementKernel`: PDF p.29 (D9): weak delta-comb kernel, evaluated against a test function.
--   - `smearedWave`: PDF pp.18,29 (7.7c),(D10): actual Gaussian-smeared comb wavefunction. The factor sqrt(2/sqrt(pi)) is the D9 weak-kernel normalization, not unit norm.
--   - `displaceWave`: PDF p.29 (D10): D_z on position wavefunctions under the positive Weyl convention.
--   - `smearedNorm`: PDF p.29: exact, generally nonunit, squared norm of the smeared vector.
--   - `normalizedSmearedWave`: PDF pp.18,29: individual normalization; finite-delta logical orthogonality is NOT assumed.
--   - `smearedKernelIntegral`: PDF p.29 (D10): convolution after evaluating the weak delta kernel; the factor 1/(pi*d^2/2) and both ordered Weyl factors are retained.
--   - `smearedKernelSum`: PDF p.29 (D11): exact finite-smearing lattice kernel, including the envelope.
--   - `hermitePhys`: PDF p.18 (7.9): physicists' Hermite polynomial for the oscillator basis.
--   - `hermiteWave`: PDF p.18: normalized position wavefunction of the nth Fock state.
--   - `gkpFock`: PDF p.18 (7.7c): actual Fock coefficients of the individually normalized smeared wave.
--   - `LatticeShape`: PDF pp.20--21: the two lattice geometries explicitly covered by the bound.
--   - `gkpNormalizerPoint`: PDF pp.20--21: lattice normalizer step, covolume pi/2; stabilizers have twice the steps.
--   - `nearestLattice`: PDF p.20 (7.22): syndrome rounding in the normalizer lattice. A fixed classical choice only resolves measure-zero ties; it is independent of the logical input.
--   - `correctableCell`: PDF p.20: central Voronoi cell, including ties.
--   - `modularSyndrome`: PDF p.20 (7.22): measured residual displacement after the chosen ideal correction.
--   - `logicalCoset`: PDF p.20: normalizer modulo stabilizer (2L), i.e. the residual logical Pauli coset.
--   - `amplifiedLossLaw`: PDF p.20 (7.21): actual Gaussian measure, with no probability axiom assumed.
--   - `cosetProbability`: PDF pp.20--21: exact probabilities of the four logical cosets, including identity translates.
--   - `cosetPauli`: PDF p.20: logical X^a Z^b action after ideal modular correction.
--   - `idealRecoveredChannel`: PDF p.20 (7.22): logical channel constructed from syndrome and lattice cosets, with the amplification noise already included. It has no physical ideal-state encoder.
--   - `centralSuccess`: PDF p.20 (7.23): guaranteed central square-cell probability.
--   - `centralFailure`: PDF p.21 (7.24): central-cell failure, which can exceed logical entanglement infidelity.
--   - `noJump`: PDF p.22 (8.3): no-jump damping, with jump-rate scalar factors deliberately omitted.
--   - `jumpTrajectory`: PDF p.22 (8.3): chronological product of actual annihilations and damping intervals.
--   - `trajectoryScalar`: PDF p.22: the scalar relating the trajectory to the integrated loss Kraus operator.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, https://arxiv.org/abs/1708.05010v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

/-!
Statements from Albert et al., arXiv:1708.05010v3. All page references are PDF pages.
Oscillator formulas use the complete number basis, never a numerical Fock cutoff.
A coordinate sequence is admitted as a Hilbert vector only with `fockDomain`;
unbounded powers carry `annDomain` or `fockMomentDomain`. Ideal combs instead act on
Schwartz test functions. No ideal comb is declared to be a unit Hilbert vector.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)
open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.2--3: number-basis coordinates, prior to imposing the Hilbert domain. -/
abbrev FockCoordinates := ℕ → ℂ

/-- PDF p.2: the full oscillator Hilbert domain, expressed in its countable ONB. -/
def fockDomain (v : FockCoordinates) : Prop := Summable (fun n => Complex.normSq (v n))

/-- PDF p.2: squared Hilbert norm on the square-summable domain. -/
def fockNormSq (v : FockCoordinates) : ℝ := ∑' n, Complex.normSq (v n)

/-- PDF p.2: inner product, conjugate-linear in the first entry. -/
def fockInner (v w : FockCoordinates) : ℂ := ∑' n, conj (v n) * w n

/-- PDF pp.2,4: a finite photon-number moment has a summability domain. -/
def fockMomentDomain (v : FockCoordinates) (k : ℕ) : Prop :=
  Summable (fun n : ℕ => (n : ℝ) ^ k * Complex.normSq (v n))

/-- PDF pp.4,18: kth number moment, only used on `fockMomentDomain`. -/
def numberMoment (v : FockCoordinates) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ k * Complex.normSq (v n)

/-- PDF p.4 (2.1): literal half-sum of the two logical number moments. -/
def codeMoment (B : Fin 2 → FockCoordinates) (k : ℕ) : ℝ :=
  (numberMoment (B 0) k + numberMoment (B 1) k) / 2

/-- PDF p.2: coefficient of a^k, including its factorial normalization. -/
def annPower (k : ℕ) (v : FockCoordinates) : FockCoordinates :=
  fun n => (Real.sqrt ((Nat.factorial (n + k) : ℝ) / Nat.factorial n) : ℂ) * v (n + k)

/-- PDF p.2: natural domain of the unbounded annihilation power. -/
def annDomain (k : ℕ) (v : FockCoordinates) : Prop := fockDomain v ∧ fockDomain (annPower k v)

/-- PDF p.2 (1.4): the exact loss coefficient for input occupation n, zero below l. -/
def lossCoefficient (g : ℝ) (l n : ℕ) : ℝ :=
  if l ≤ n then Real.sqrt (Nat.choose n l : ℝ) * Real.sqrt g ^ l *
    Real.sqrt (1 - g) ^ (n - l) else 0

/-- PDF p.2 (1.4): loss Kraus action on the full number basis. -/
def lossVector (g : ℝ) (l : ℕ) (v : FockCoordinates) : FockCoordinates :=
  fun n => (lossCoefficient g l (n + l) : ℂ) * v (n + l)

/-- PDF p.8 (4.1): actual compression of E_l^dagger E_k, not a free QEC matrix. -/
def qecBlock (B : Fin 2 → FockCoordinates) (g : ℝ) (l k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => fockInner (lossVector g l (B i)) (lossVector g k (B j))

/-- PDF p.8 (4.4): coefficient of the identity. -/
def qecC (B : Fin 2 → FockCoordinates) (g : ℝ) (l k : ℕ) : ℝ :=
  ((qecBlock B g l k 0 0 + qecBlock B g l k 1 1) / 2).re

/-- PDF p.8 (4.4): coefficient of logical Z in the chosen basis. -/
def qecZ (B : Fin 2 → FockCoordinates) (g : ℝ) (l k : ℕ) : ℝ :=
  ((qecBlock B g l k 0 0 - qecBlock B g l k 1 1) / 2).re

/-- PDF p.8 (4.4): coefficient of logical X, including nonsymmetric off-diagonal blocks. -/
def qecX (B : Fin 2 → FockCoordinates) (g : ℝ) (l k : ℕ) : ℝ :=
  ((qecBlock B g l k 0 1 + qecBlock B g l k 1 0) / 2).re

/-- PDF p.3 (1.8): I,X,Y,Z, using the accepted Bool-indexed Pauli matrices
with Fin 2 labels 0,1 mapped to false,true. -/
def liouvilleBasis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, (fun i j => pauliX (decide (i.val = 1)) (decide (j.val = 1))),
    (fun i j => pauliY (decide (i.val = 1)) (decide (j.val = 1))),
    (fun i j => pauliZ (decide (i.val = 1)) (decide (j.val = 1)))]

/-- PDF p.3 (1.8): Pauli Liouville matrix; this is distinct from the Choi matrix. -/
def liouville (T : Superop (Fin 2) (Fin 2)) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun k l => ((liouvilleBasis k * T (liouvilleBasis l)).trace) / 2

/-- PDF p.7 (3.3): trace over the reference, leaving the channel's output marginal. -/
def traceReference (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ r, R (i, r) (j, r)

/-- PDF p.7 (3.3): reverse coherentCoordinates information, without capacity optimization.
The frozen output-first Choi operator is unnormalized; multiplying by 1/2
gives the trace-one qubit Choi state in (1.9). -/
def reverseInformation (T : Superop (Fin 2) (Fin 2)) : ℝ :=
  vnEntropy (traceReference ((1 / 2 : ℂ) • outputFirstChoi T)) - vnEntropy ((1 / 2 : ℂ) • outputFirstChoi T)

/-- PDF p.7 (3.4): squared Frobenius norm from accepted Advance50.P29,
specialized to the effective qubit channel. -/
def qubitFrobeniusSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Advance50.P29.frobeniusSq A

/-- PDF p.24 (A2): minimum over normalized pure inputs; compactness and CPTP
supply a nonempty bounded set, with attainment asserted below. -/
def worstPureFidelity (d : ℕ) (T : Superop (Fin d) (Fin d)) : ℝ :=
  sInf {r : ℝ | ∃ v : EuclideanSpace ℂ (Fin d), ‖v‖ = 1 ∧
    r = effectProb (pureDensity v) (T (pureDensity v))}

/-- PDF p.9 (5.3): periodic residue projector, allowing signed residue labels. -/
def residueProject (S : ℕ) (r : ℤ) (v : FockCoordinates) : FockCoordinates :=
  fun n => if (n : ℤ) % (2 * (S + 1) : ℕ) = r % (2 * (S + 1) : ℕ) then v n else 0

/-- PDF p.9: normalized coherentCoordinates-state coefficients for real amplitude a. -/
def coherentCoordinates (a : ℝ) : FockCoordinates :=
  QAlgorithms.Papers.Independent.Frontier18.P14.coherentCoefficient (a : ℂ)

/-- PDF p.9 (5.2): the actual projected coherentCoordinates-state probability. -/
def catNorm (a : ℝ) (S : ℕ) (r : ℤ) : ℝ :=
  fockNormSq (residueProject S r (coherentCoordinates a))

/-- PDF p.9 (5.1): normalized projected coherentCoordinates coordinates; a>0 in every use. -/
def catCodeCoordinates (a : ℝ) (S : ℕ) (mu : Fin 2) : FockCoordinates :=
  fun n => residueProject S ((S + 1) * mu.val : ℕ) (coherentCoordinates a) n /
    (Real.sqrt (catNorm a S ((S + 1) * mu.val : ℕ)) : ℂ)

/-- PDF p.9 (5.7): bounded number-phase rotation. -/
def residueCheck (S : ℕ) (v : FockCoordinates) : FockCoordinates :=
  fun n => Complex.exp (Complex.I * (2 * Real.pi * (n : ℝ) / (S + 1))) * v n

/-- PDF p.9 following (5.7): the specified square root of the check is logical Z. -/
def residueLogicalZ (S : ℕ) (v : FockCoordinates) : FockCoordinates :=
  fun n => Complex.exp (Complex.I * (Real.pi * (n : ℝ) / (S + 1))) * v n

/-- PDF p.9 (5.5): Fourier projection using exact coherentCoordinates-state overlaps. -/
def catNormFourier (a : ℝ) (S : ℕ) (mu : Fin 2) : ℂ :=
  (1 / (2 * (S + 1) : ℂ)) * ∑ s ∈ Finset.range (2 * (S + 1)),
    (-1 : ℂ) ^ (mu.val * s) *
      Complex.exp ((a ^ 2 : ℝ) * (Complex.exp (Complex.I * (Real.pi * (s : ℝ) / (S + 1))) - 1))

/-- PDF pp.9--11: probability ratios with signed residues, before taking any limit. -/
def catLossRatio (a : ℝ) (S : ℕ) (g : ℝ) (l : ℕ) (mu : Fin 2) : ℝ :=
  catNorm (a * Real.sqrt (1 - g)) S ((((S + 1) * mu.val : ℕ) : ℤ) - (l : ℤ)) /
    catNorm a S ((S + 1) * mu.val : ℕ)

/-- PDF p.10 (5.12): Poisson weight whose mean g*a^2 varies with a. -/
def poissonWeight (a g : ℝ) (l : ℕ) : ℝ :=
  (g * a ^ 2) ^ l * Real.exp (-g * a ^ 2) / Nat.factorial l

/-- PDF p.14 (6.11): finite spin coefficients, indexed by twice the spin. -/
def antipodal (M : ℕ) (mu : Fin 2) (m : Fin (M + 1)) : ℂ :=
  (-1 : ℂ) ^ (mu.val * m.val) * (Real.sqrt (Nat.choose M m.val) / Real.sqrt ((2 : ℝ) ^ M) : ℝ)

/-- PDF p.11 (6.1): direct full-Fock binomialCodeCoordinates coordinates. -/
def binomialCodeCoordinates (N S : ℕ) (mu : Fin 2) : FockCoordinates :=
  fun n => if h : n % (S + 1) = 0 ∧ n / (S + 1) ≤ N + 1 then
    antipodal (N + 1) mu ⟨n / (S + 1), Nat.lt_succ_of_le h.2⟩ else 0

/-- PDF p.12 (6.4): the positive/negative logical combinations. -/
def binomialParity (N S : ℕ) (mu : Fin 2) : FockCoordinates :=
  fun n => (binomialCodeCoordinates N S 0 n + (-1 : ℂ) ^ mu.val * binomialCodeCoordinates N S 1 n) / (Real.sqrt 2 : ℂ)

/-- PDF p.12 (6.5): exact generating polynomial, with plus/minus sign. -/
def binomialGenerator (N S : ℕ) (minus : Bool) : Polynomial ℝ :=
  ((Polynomial.C (1 / 2)) *
    (1 + Polynomial.C (if minus then -1 else 1) * Polynomial.X ^ (S + 1))) ^ (N + 1)

/-- PDF p.14: standard spin-x matrix, on m=0,...,M for spin M/2. -/
def spinX (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ :=
  fun i j => if i.val = j.val + 1 then
      (Real.sqrt (((j.val + 1 : ℕ) : ℝ) * (M - j.val)) / 2 : ℝ)
    else if j.val = i.val + 1 then
      (Real.sqrt (((i.val + 1 : ℕ) : ℝ) * (M - i.val)) / 2 : ℝ) else 0

/-- PDF pp.14--15: transport of a coefficient vector to one mode. -/
def embedOne (M S : ℕ) (v : Fin (M + 1) → ℂ) : FockCoordinates :=
  fun n => ∑ m, if n = (S + 1) * m.val then v m else 0

/-- PDF p.15 Fig.7(a), p.27: two-mode transport with the spacing in BOTH occupations.
Printed (6.16) drops a spacing factor; use the explicit preceding basis map. -/
def embedTwo (M S : ℕ) (v : Fin (M + 1) → ℂ) : ℕ × ℕ → ℂ :=
  fun n => ∑ m, if n = ((S + 1) * (M - m.val), (S + 1) * m.val) then v m else 0

/-- PDF p.15: accepted Information100.P22.dicke in Fin 2 word coordinates;
Bool false,true correspond to 0,1. Infeasible excitation weights give zero. -/
def qubitDickeCoordinates (K r : ℕ) (x : Fin K → Fin 2) : ℂ :=
  QAlgorithms.Papers.Independent.Information100.P22.dicke (I := Fin K) r
    (fun i => decide ((x i).val = 1))

/-- PDF p.15 (6.14): the spaced Dicke transport (K >= M(S+1) at use sites). -/
def embedDicke (M S K : ℕ) (v : Fin (M + 1) → ℂ) (x : Fin K → Fin 2) : ℂ :=
  ∑ m, v m * qubitDickeCoordinates K ((S + 1) * m.val) x

/-- PDF p.17: even/odd spin generator on the stated seven-dimensional invariant space. -/
def smallGenerator : Matrix (Fin 7) (Fin 7) ℂ :=
  let even : Matrix (Fin 7) (Fin 4) ℂ := fun n m => if n.val = 2 * m.val then 1 else 0
  let odd : Matrix (Fin 7) (Fin 3) ℂ := fun n m => if n.val = 2 * m.val + 1 then 1 else 0
  8 • (even * spinX 3 * evenᴴ) ^ 2 + (odd * spinX 2 * oddᴴ) ^ 2

/-- PDF p.17 (6.21): a=8,b=5, with identity extension outside the invariant space. -/
def smallUnitary : Matrix (Fin 7) (Fin 7) ℂ :=
  NormedSpace.exp (((((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) • smallGenerator))

/-- PDF p.17 Tables II--III: actual normalized code, dephasing residual, loss, and failure vectors.
Residual normalization is sqrt(3), correcting the false coefficient 2 in (6.20). -/
def smallBasis (j : Fin 7) (n : Fin 7) : ℂ :=
  if h0 : j.val < 2 then binomialCodeCoordinates 2 1 ⟨j.val, by omega⟩ n.val
  else if h1 : j.val < 4 then
    (((n.val : ℝ) - 3) / Real.sqrt 3 : ℝ) * binomialCodeCoordinates 2 1 ⟨j.val - 2, by omega⟩ n.val
  else if h2 : j.val < 6 then
    annPower 1 (binomialCodeCoordinates 2 1 ⟨j.val - 4, by omega⟩) n.val / (Real.sqrt 3 : ℂ)
  else if n.val = 1 then (1 / Real.sqrt 2 : ℝ)
  else if n.val = 5 then (-1 / Real.sqrt 2 : ℝ) else 0

/-- Small exact sanity cases for the new coordinate constructors. -/

example : lossCoefficient (0 : ℝ) 1 0 = 0 := by simp [lossCoefficient]

example (v : FockCoordinates) : residueProject 0 0 v 0 = v 0 := by simp [residueProject]

example : coherentCoordinates 0 0 = 1 := by simp [coherentCoordinates,
  QAlgorithms.Papers.Independent.Frontier18.P14.coherentCoefficient]

example : binomialCodeCoordinates 0 0 0 0 = (1 / Real.sqrt 2 : ℝ) := by
  simp [binomialCodeCoordinates, antipodal]

example : (spinX 0) 0 0 = 0 := by simp [spinX]

example (v : Fin 1 → ℂ) : embedTwo 0 0 v (0, 0) = v 0 := by simp [embedTwo]

/-- PDF p.28 (C4): totalQuditExcitation of an M-qudit computational word. -/
def totalQuditExcitation {d M : ℕ} (x : Fin M → Fin d) : ℕ := ∑ i, (x i).val

/-- PDF p.27 (C2),(C4): number of words of a given total totalQuditExcitation. -/
def extendedCount (d M m : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin M → Fin d => totalQuditExcitation x = m)).card

/-- PDF p.27 (C4): normalized extended binomialCodeCoordinates vector, distinct from a general qudit Dicke vector. -/
def extendedVector (d M m : ℕ) (x : Fin M → Fin d) : ℂ :=
  if totalQuditExcitation x = m then (1 / Real.sqrt (extendedCount d M m) : ℝ) else 0

/-- PDF p.28 (C8): positive Fourier phase, matching the explicit backwards shift (C7). -/
def quditFourierFactor (d : ℕ) (mu m : ℕ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * (mu : ℝ) * (m : ℝ) / d))

/-- PDF p.27 (C3): totalQuditExcitation-basis coefficients, including the endpoint (d-1)M. -/
def extendedCoefficients (d M : ℕ) (mu : Fin d) (m : Fin ((d - 1) * M + 1)) : ℂ :=
  quditFourierFactor d mu.val m.val *
    (Real.sqrt (extendedCount d M m.val) / Real.sqrt ((d : ℝ) ^ M) : ℝ)

/-- PDF p.27 (C3): the new multi-qudit code, in extended-binomialCodeCoordinates coordinates. -/
def permCode (d M : ℕ) (mu : Fin d) (x : Fin M → Fin d) : ℂ :=
  ∑ m : Fin ((d - 1) * M + 1), extendedCoefficients d M mu m * extendedVector d M m.val x

/-- PDF p.28 (C9): tensor product of M identical Fourier vectors. -/
def fourierProduct (d M : ℕ) (mu : Fin d) (x : Fin M → Fin d) : ℂ :=
  ∏ i, quditFourierFactor d mu.val (x i).val / (Real.sqrt d : ℂ)

/-- PDF p.28 (C7): the input label one step above the output label. -/
def nextLabel {d : ℕ} (hd : 0 < d) (j : Fin d) : Fin d :=
  ⟨(j.val + 1) % d, Nat.mod_lt _ hd⟩

/-- PDF p.28 (C10): average of the backwards cyclic shifts on individual qudits. -/
def collectiveShift (d M : ℕ) (hd : 0 < d) :
    Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ :=
  fun x y => (1 / (M : ℂ)) * ∑ k : Fin M,
    if y = Function.update x k (nextLabel hd (x k)) then 1 else 0

/-- PDF p.28: compression to the extended-binomialCodeCoordinates span, of dimension (d-1)M+1. -/
def compressedShift (d M : ℕ) (hd : 0 < d) :
    Matrix (Fin ((d - 1) * M + 1)) (Fin ((d - 1) * M + 1)) ℂ :=
  let V : Matrix (Fin M → Fin d) (Fin ((d - 1) * M + 1)) ℂ :=
    fun x m => extendedVector d M m.val x
  Vᴴ * collectiveShift d M hd * V

/-- PDF p.28 (D1b): the positive Weyl convention. -/
def weylPhase (a b : ℂ) : ℂ := Complex.exp ((a * conj b - conj a * b) / 2)

/-- PDF p.2 (1.4): number-basis kernel of a single loss Kraus operator. -/
def lossEntry (g : ℝ) (l n m : ℕ) : ℂ :=
  if m = n + l then (lossCoefficient g l m : ℂ) else 0

/-- PDF p.19 (7.12): genuine product kernel, before the displacement expansion. -/
def lossProduct (g : ℝ) (l k n m : ℕ) : ℂ :=
  ∑' j, conj (lossEntry g l j n) * lossEntry g k j m

/-- PDF p.19 (7.12): integrand INCLUDING the factor 1/pi, on complex-plane Lebesgue measure. -/
def lossDisplacementIntegrand (g : ℝ) (l k n m : ℕ) (z : ℂ) : ℂ :=
  (Real.exp (-(1 - g) * Complex.normSq z / 2) / Real.pi : ℝ) *
    displacementEntry (conj z) l k * displacementEntry ((Real.sqrt g : ℂ) * z) n m

section FockDensityOrder

open scoped ComplexOrder

/-- PDF pp.2,20: positive trace-one full Fock kernels. Positivity of every finite
principal compression and summability of the nonnegative diagonal characterize
positive trace-class operators; there is no fixed cutoff. -/
def fockDensity (R : ℕ → ℕ → ℂ) : Prop :=
  (∀ d : ℕ, Matrix.PosSemidef ((fun i j : Fin d => R i.val j.val) : Matrix (Fin d) (Fin d) ℂ)) ∧
    Summable (fun n => (R n n).re) ∧ (∑' n, (R n n).re) = 1

end FockDensityOrder

/-- PDF p.2: pure loss, by the countable Kraus sum on actual Fock kernels. -/
def lossChannel (g : ℝ) (R : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  ∑' l, (lossCoefficient g l (n + l) * lossCoefficient g l (m + l) : ℝ) * R (n + l) (m + l)

/-- PDF p.20 (7.20): amplification after loss; Kraus operators sqrt(1-g) E_l^dagger. -/
def amplifierChannel (g : ℝ) (R : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  ∑ l ∈ Finset.range (min n m + 1),
    ((1 - g) * lossCoefficient g l n * lossCoefficient g l m : ℝ) * R (n - l) (m - l)

/-- PDF p.20 (7.21): displacement conjugation, evaluated on all matrix entries. -/
def displaceDensity (z : ℂ) (R : ℕ → ℕ → ℂ) (n m : ℕ) : ℂ :=
  ∑' j, ∑' k, displacementEntry z n j * R j k * conj (displacementEntry z m k)

/-- PDF p.20 (7.21): density of the amplified-loss displacement distribution on C. -/
def amplifiedLossDensity (g : ℝ) (z : ℂ) : ℝ :=
  (1 - g) / (Real.pi * g) * Real.exp (-(1 - g) / g * Complex.normSq z)

/-- PDF p.18 (7.5): distributional square-code comb acting linearly on tests. -/
def idealComb (mu : Fin 2) (f : ℝ → ℂ) : ℂ :=
  ∑' n : ℤ, f (Real.sqrt Real.pi * (2 * (n : ℝ) + mu.val))

/-- PDF pp.18,29 (7.6),(D5): Gaussian-Abel regularized coherentCoordinates-lattice sum.
The ordered product is D_real D_imag; it is evaluated on the vacuum in position coordinates. -/
def regularizedLattice (mu : Fin 2) (r x : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ,
    let q := Real.sqrt Real.pi * (2 * (n.1 : ℝ) + mu.val)
    (Real.exp (-r * ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2)) *
      Real.rpow Real.pi (-1 / 4 : ℝ) * Real.exp (-(x - q) ^ 2 / 2) : ℝ) *
        Complex.exp (Complex.I * (Real.sqrt Real.pi * (n.2 : ℝ) * (x - q)))

/-- PDF p.29 (D9): normalizer-lattice displacement, with signed mu-nu offset. -/
def kernelLattice (mu nu : Fin 2) (n : ℤ × ℤ) : ℂ :=
  (Real.sqrt (Real.pi / 2) : ℂ) *
    (((2 * (n.1 : ℝ) + (mu.val : ℝ) - nu.val) : ℂ) + Complex.I * (n.2 : ℝ))

/-- PDF p.29 (D9): phase for the positive Weyl convention. -/
def kernelPhase (mu nu : Fin 2) (n : ℤ × ℤ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi * ((n.1 : ℝ) + ((mu.val : ℝ) + nu.val) / 2) * (n.2 : ℝ)))

/-- PDF p.29 (D9): weak delta-comb kernel, evaluated against a test function. -/
def idealDisplacementKernel (mu nu : Fin 2) (f : ℂ → ℂ) : ℂ :=
  ∑' n : ℤ × ℤ, kernelPhase mu nu n * f (kernelLattice mu nu n)

/-- PDF pp.18,29 (7.7c),(D10): actual Gaussian-smeared comb wavefunction.
The factor sqrt(2/sqrt(pi)) is the D9 weak-kernel normalization, not unit norm. -/
def smearedWave (mu : Fin 2) (d x : ℝ) : ℂ :=
  (Real.sqrt (2 / Real.sqrt Real.pi) : ℂ) * ∑' n : ℤ,
    let q := Real.sqrt Real.pi * (2 * (n : ℝ) + mu.val)
    (Real.exp (-(x - q) ^ 2 / (2 * d ^ 2) - d ^ 2 * (x + q) ^ 2 / 8) : ℝ)

/-- PDF p.29 (D10): D_z on position wavefunctions under the positive Weyl convention. -/
def displaceWave (z : ℂ) (v : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Real.sqrt 2 * z.im * x - z.re * z.im) : ℝ)) *
    v (x - Real.sqrt 2 * z.re)

/-- PDF p.29: exact, generally nonunit, squared norm of the smeared vector. -/
def smearedNorm (mu : Fin 2) (d : ℝ) : ℝ := ∫ x : ℝ, Complex.normSq (smearedWave mu d x)

/-- PDF pp.18,29: individual normalization; finite-delta logical orthogonality is NOT assumed. -/
def normalizedSmearedWave (mu : Fin 2) (d x : ℝ) : ℂ :=
  smearedWave mu d x / (Real.sqrt (smearedNorm mu d) : ℂ)

/-- PDF p.29 (D10): convolution after evaluating the weak delta kernel; the factor
1/(pi*d^2/2) and both ordered Weyl factors are retained. -/
def smearedKernelIntegral (mu nu : Fin 2) (d : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ × ℤ, kernelPhase mu nu n *
    ∫ b : ℂ,
      (Real.exp (-(Complex.normSq b + Complex.normSq (kernelLattice mu nu n + b - z)) / d ^ 2) /
        (Real.pi * d ^ 2 / 2) : ℝ) *
        weylPhase (-b) z * weylPhase (z - b) (kernelLattice mu nu n + b - z)

/-- PDF p.29 (D11): exact finite-smearing lattice kernel, including the envelope. -/
def smearedKernelSum (mu nu : Fin 2) (d : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ × ℤ, kernelPhase mu nu n *
    (Real.exp (-Complex.normSq (z - kernelLattice mu nu n) / (2 * d ^ 2) -
      d ^ 2 * Complex.normSq (z + kernelLattice mu nu n) / 8) : ℝ)

/-- PDF p.18 (7.9): physicists' Hermite polynomial for the oscillator basis. -/
def hermitePhys : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => 2 * Polynomial.X * hermitePhys n - Polynomial.derivative (hermitePhys n)

/-- PDF p.18: normalized position wavefunction of the nth Fock state. -/
def hermiteWave (n : ℕ) (x : ℝ) : ℝ :=
  (hermitePhys n).eval x * Real.exp (-x ^ 2 / 2) /
    Real.sqrt ((2 : ℝ) ^ n * Nat.factorial n * Real.sqrt Real.pi)

/-- PDF p.18 (7.7c): actual Fock coefficients of the individually normalized smeared wave. -/
def gkpFock (d : ℝ) (mu : Fin 2) : FockCoordinates :=
  fun n => ∫ x : ℝ, (hermiteWave n x : ℂ) * normalizedSmearedWave mu d x

/-- PDF pp.20--21: the two lattice geometries explicitly covered by the bound. -/
inductive LatticeShape where
  | square
  | hexagonal
  deriving DecidableEq

/-- PDF pp.20--21: lattice normalizer step, covolume pi/2; stabilizers have twice the steps. -/
def gkpNormalizerPoint (shape : LatticeShape) (n : ℤ × ℤ) : ℂ :=
  match shape with
  | .square => (Real.sqrt (Real.pi / 2) : ℂ) * ((n.1 : ℂ) + Complex.I * (n.2 : ℂ))
  | .hexagonal => (Real.sqrt (Real.pi / Real.sqrt 3) : ℂ) *
      ((n.1 : ℂ) + (n.2 : ℂ) * (1 / 2 + Complex.I * (Real.sqrt 3 / 2 : ℝ)))

/-- PDF p.20 (7.22): syndrome rounding in the normalizer lattice.
A fixed classical choice only resolves measure-zero ties; it is independent of the logical input. -/
def nearestLattice (shape : LatticeShape) (z : ℂ) : ℤ × ℤ :=
  Classical.epsilon (fun n => ∀ m : ℤ × ℤ, ‖z - gkpNormalizerPoint shape n‖ ≤ ‖z - gkpNormalizerPoint shape m‖)

/-- PDF p.20: central Voronoi cell, including ties. -/
def correctableCell (shape : LatticeShape) : Set ℂ :=
  {z | ∀ n : ℤ × ℤ, ‖z‖ ≤ ‖z - gkpNormalizerPoint shape n‖}

/-- PDF p.20 (7.22): measured residual displacement after the chosen ideal correction. -/
def modularSyndrome (shape : LatticeShape) (z : ℂ) : ℂ := z - gkpNormalizerPoint shape (nearestLattice shape z)

/-- PDF p.20: normalizer modulo stabilizer (2L), i.e. the residual logical Pauli coset. -/
def logicalCoset (shape : LatticeShape) (z : ℂ) : Fin 2 × Fin 2 :=
  (⟨((nearestLattice shape z).1 % 2).toNat, by omega⟩,
   ⟨((nearestLattice shape z).2 % 2).toNat, by omega⟩)

/-- PDF p.20 (7.21): actual Gaussian measure, with no probability axiom assumed. -/
def amplifiedLossLaw (g : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (amplifiedLossDensity g z))

/-- PDF pp.20--21: exact probabilities of the four logical cosets, including identity translates. -/
def cosetProbability (shape : LatticeShape) (g : ℝ) (c : Fin 2 × Fin 2) : ℝ :=
  (amplifiedLossLaw g {z | logicalCoset shape z = c}).toReal

/-- PDF p.20: logical X^a Z^b action after ideal modular correction. -/
def cosetPauli (c : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (liouvilleBasis 1) ^ c.1.val * (liouvilleBasis 3) ^ c.2.val

/-- PDF p.20 (7.22): logical channel constructed from syndrome and lattice cosets,
with the amplification noise already included. It has no physical ideal-state encoder. -/
def idealRecoveredChannel (shape : LatticeShape) (g : ℝ) : Superop (Fin 2) (Fin 2) :=
  krausApply (fun c : Fin 2 × Fin 2 => (Real.sqrt (cosetProbability shape g c) : ℂ) • cosetPauli c)

/-- PDF p.20 (7.23): guaranteed central square-cell probability. -/
def centralSuccess (g : ℝ) : ℝ :=
  (amplifiedLossLaw g {z | |z.re| ≤ Real.sqrt (Real.pi / 8) ∧ |z.im| ≤ Real.sqrt (Real.pi / 8)}).toReal

/-- PDF p.21 (7.24): central-cell failure, which can exceed logical entanglement infidelity. -/
def centralFailure (g : ℝ) : ℝ :=
  (amplifiedLossLaw g {z | ¬ (|z.re| ≤ Real.sqrt (Real.pi / 8) ∧ |z.im| ≤ Real.sqrt (Real.pi / 8))}).toReal

/-- PDF p.22 (8.3): no-jump damping, with jump-rate scalar factors deliberately omitted. -/
def noJump (k t : ℝ) (v : FockCoordinates) : FockCoordinates :=
  fun n => (Real.exp (-k * t * n / 2) : ℂ) * v n

/-- PDF p.22 (8.3): chronological product of actual annihilations and damping intervals. -/
def jumpTrajectory (k t : ℝ) {l : ℕ} (times : Fin l → ℝ) (v : FockCoordinates) : FockCoordinates :=
  let final := (List.ofFn times).foldl
    (fun (s : ℝ × FockCoordinates) tau => (tau, annPower 1 (noJump k (tau - s.1) s.2))) (0, v)
  noJump k (t - final.1) final.2

/-- PDF p.22: the scalar relating the trajectory to the integrated loss Kraus operator. -/
def trajectoryScalar (k : ℝ) {l : ℕ} (times : Fin l → ℝ) (g : ℝ) : ℝ :=
  Real.sqrt (Nat.factorial l) * Real.exp (-k * (∑ i, times i) / 2) / Real.sqrt g ^ l

/-- Sanity tests: endpoints, orientations, and empty trajectories. -/

example (d : ℕ) (mu m : ℕ) : quditFourierFactor d mu 0 = 1 := by simp [quditFourierFactor]

example : displacementEntry 0 0 0 = 1 := by simp [QAlgorithms.Papers.Independent.Frontier18.P14.displacementEntry,
  Complex.normSq_zero]

example (mu : Fin 2) : idealComb mu (fun _ => 0) = 0 := by simp [idealComb]

example : kernelLattice 0 0 (0, 0) = 0 := by simp [kernelLattice]

example (g : ℝ) : amplifiedLossDensity g 0 = (1 - g) / (Real.pi * g) := by simp [amplifiedLossDensity]

example (k t : ℝ) (v : FockCoordinates) :
    jumpTrajectory k t (fun i : Fin 0 => Fin.elim0 i) v = noJump k t v := by
  simp [jumpTrajectory]

end QAlgorithms.Papers.Independent.Intakenext100.P65


