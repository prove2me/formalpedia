-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
-- name    : QAlgorithms_Papers_Independent_Information100_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:02:48.678862+00:00
-- url     : https://prove2.me/theorems/170f2713-4218-415b-b5fe-13eb72b5a02e
-- title:
--   Definitions for All coherent measurements provide observational ergotropic advantage
-- statement:
--   The objects the formalized statements of *All coherent measurements provide observational ergotropic advantage* (arXiv:2609.18735) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `energyDephasing`: Paper p.3: complete dephasing in the fixed energy eigenbasis, for arbitrary dimension.
--   - `energyExpectation`: Paper p.3: Tr(H X), where H is diagonal with the real energies E.
--   - `passiveEnergy`: Paper p.3, Eq.(4): minimum energy on the unitary orbit. For Hermitian X this real infimum is attained on the compact nonempty unitary group.
--   - `ergotropicCoarseGraining`: Paper pp.3–4, Eqs.(9),(12): measure-and-prepare coarse-graining, extended linearly on all operators. A zero-trace effect contributes zero, including zero POVM outcomes.
--   - `observationalErgotropy`: Paper p.3, Eq.(8): observational ergotropy for the actual input energy.
--   - `incoherentErgotropy`: Paper p.3, Eq.(7): ergotropy of the completely dephased input.
--   - `measurementIncoherent`: Paper p.2: every effect is diagonal in this same reference basis.
--   - `incoherentWorkBenchmark`: Paper pp.4–5, Eq.(18): the benchmark ranges over any positive finite number of outcomes, independently of the number of outcomes of the given measurement.
--   - `observationalAdvantage`: Paper p.5, Eq.(19): computed maximum excess over the incoherent ergotropy. For a POVM in positive dimension the density set is compact and nonempty.
--   - `rankOneEnergyMeasurement`: Paper p.2: a rank-one projective measurement has one projector for each vector of an orthonormal basis; in particular, exactly d outcomes.
--   - `postprocessedEnergyMeasurement`: Paper p.2, Eq.(1): classical post-processing with column-stochastic coefficients.
--   - `advantageCeilingWitness`: Paper pp.5–6, Proposition 1: a maximally coherent pure state and a subset of outcomes that sums to its projector; every complementary effect annihilates it.
--   - `largestEnergyEigenvalue`: Paper pp.6–7: the maximum eigenvalue of a Hermitian matrix, expressed by its Rayleigh variational formula on unit vectors. This compact supremum is attained.
--   - `spectralAdvantageTerm`: Paper p.6, Theorem 2: optimization over effects of trace k, with the coarse-graining channel computed from M. For 0 ≤ k ≤ d this is a compact nonempty feasible set.
--   - `measurementCoherenceRobustness`: Paper p.2, Eq.(2): robustness is the least nonnegative mixing amount with an arbitrary POVM with the same outcomes that yields an incoherent POVM. The feasible set is nonempty and its minimum finite for every finite POVM; no feasibility premise is added.
--   - `measurementLinfCoherence`: Paper p.2, Eq.(3): maximum over i < j of the sum of absolute off-diagonal entries. The empty maximum in dimension one is defined as zero by real sSup.
--   - `minimumAdjacentEnergyGap`: Paper p.8, Eq.(41): minimum over all adjacent energy gaps. Used only for d ≥ 2.
--   - `ergotropicBlochMatrix`: Paper pp.4,12: Bloch density matrix, with frozen Pauli-Y sign and ground state |0>.
--   - `ergotropicBlochLengthSquared`: Paper p.4: squared Euclidean length of a real Bloch vector.
--   - `ergotropicBlochDot`: Paper p.4: Euclidean scalar product of the Bloch vectors.
--   - `ergotropicBinary`: Paper pp.4,12: binary measurement with first effect A and complementary effect.
--   - `ergotropicBlochMeasurement`: Paper p.4: binary Bloch measurement; projective when its Bloch vector has length one.
--   - `ergotropicQuotient`: Paper p.4, Eq.(16): extended-real optimized quotient, only where the actual incoherent ergotropy is strictly positive. Negative pointwise ratios are retained.
--   - `noisyErgotropicTrine`: Paper pp.8–9: noisy equatorial trine, with c in [0,1] in physical statements.
--   - `ergotropicSpectralWidth`: Paper p.14, Eq.(C20): spectral width of a Hermitian matrix.
--   - `qutritPopulationWidth`: Paper p.14, Eq.(C29): largest minus smallest diagonal population.
--   - `advantagePIOKraus`: Paper p.13, Eqs.(C5),(C9): explicit PIO Kraus operators.
--   - `ergotropicKrausDual`: Paper p.13, Eq.(C1): Heisenberg dual of a finite Kraus map on each effect.
--   - `ergotropicPIOFamily`: Paper p.13: PIO implementation K_j=U_j P_j with orthogonal diagonal projectors resolving the identity and incoherent unitary U_j. Unitarity plus one supported entry per column is the monomial-unitary condition; no unitality on states is assumed.
--   - `advantagePIOOriginal`: Paper p.13, Eq.(C11): original binary qutrit measurement in the PIO counterexample.
--   - `advantagePIOInput`: Paper p.15, Eq.(C49): common optimizing density matrix for the two measurements.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, https://arxiv.org/abs/2609.18735v1

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Statements from Mahanti et al., arXiv:2609.18735v1. All page numbers are PDF pages.
The reference coordinates are the energy eigenbasis. Scalar extrema below are taken only
over the indicated physical objects. In positive finite dimension their feasible sets are
nonempty and compact (robustness has a finite attained minimum). No such facts are premises.
The sole empty-set convention used physically is zero l-infinity coherence in dimension one.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.3: complete dephasing in the fixed energy eigenbasis, for arbitrary dimension. -/
def energyDephasing {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => X i i

/-- Paper p.3: Tr(H X), where H is diagonal with the real energies E. -/
def energyExpectation {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, E i * (X i i).re

/-- Paper p.3, Eq.(4): minimum energy on the unitary orbit. For Hermitian X this
real infimum is attained on the compact nonempty unitary group. -/
def passiveEnergy {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
    r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)}

/-- Paper pp.3–4, Eqs.(9),(12): measure-and-prepare coarse-graining, extended linearly
on all operators. A zero-trace effect contributes zero, including zero POVM outcomes. -/
def ergotropicCoarseGraining {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ u, if (M u).trace = 0 then 0 else ((M u * X).trace / (M u).trace) • M u

/-- Paper p.3, Eq.(8): observational ergotropy for the actual input energy. -/
def observationalErgotropy {d n : ℕ} (E : Fin d → ℝ)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  energyExpectation E X - passiveEnergy E (ergotropicCoarseGraining M X)

/-- Paper p.3, Eq.(7): ergotropy of the completely dephased input. -/
def incoherentErgotropy {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  energyExpectation E (energyDephasing X) - passiveEnergy E (energyDephasing X)

/-- Paper p.2: every effect is diagonal in this same reference basis. -/
def measurementIncoherent {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ u, energyDephasing (M u) = M u

/-- Paper pp.4–5, Eq.(18): the benchmark ranges over any positive finite number of
outcomes, independently of the number of outcomes of the given measurement. -/
def incoherentWorkBenchmark {d : ℕ} (E : Fin d → ℝ)
    (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r | ∃ n : ℕ, 0 < n ∧ ∃ N : Fin n → Matrix (Fin d) (Fin d) ℂ,
    IsPOVM N ∧ measurementIncoherent N ∧ r = observationalErgotropy E N X}

/-- Paper p.5, Eq.(19): computed maximum excess over the incoherent ergotropy.
For a POVM in positive dimension the density set is compact and nonempty. -/
def observationalAdvantage {d n : ℕ} (E : Fin d → ℝ)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
    r = observationalErgotropy E M X - incoherentErgotropy E X}

/-- Paper p.2: a rank-one projective measurement has one projector for each vector
of an orthonormal basis; in particular, exactly d outcomes. -/
def rankOneEnergyMeasurement {d : ℕ} (M : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ B : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)),
    ∀ i, M i = pureDensity (B i)

/-- Paper p.2, Eq.(1): classical post-processing with column-stochastic coefficients. -/
def postprocessedEnergyMeasurement {d n : ℕ} (D : Fin n → Fin d → ℝ)
    (M : Fin d → Matrix (Fin d) (Fin d) ℂ) : Fin n → Matrix (Fin d) (Fin d) ℂ :=
  fun j => ∑ i, (D j i : ℂ) • M i

/-- Paper pp.5–6, Proposition 1: a maximally coherent pure state and a subset of
outcomes that sums to its projector; every complementary effect annihilates it. -/
def advantageCeilingWitness {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) : Prop :=
  IsState v ∧ (∀ i, Complex.normSq (v i) = 1 / (d : ℝ)) ∧
    (∑ u ∈ S, M u) = pureDensity v ∧ ∀ u, u ∉ S → act (M u) v = 0

/-- Paper pp.6–7: the maximum eigenvalue of a Hermitian matrix, expressed by its
Rayleigh variational formula on unit vectors. This compact supremum is attained. -/
def largestEnergyEigenvalue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r | ∃ v : EuclideanSpace ℂ (Fin d), IsState v ∧
    r = (∑ i, ∑ j, conj (v i) * A i j * v j).re}

/-- Paper p.6, Theorem 2: optimization over effects of trace k, with the coarse-graining
channel computed from M. For 0 ≤ k ≤ d this is a compact nonempty feasible set. -/
def spectralAdvantageTerm {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (k : ℕ) : ℝ :=
  sSup {r | ∃ Q : Matrix (Fin d) (Fin d) ℂ, IsEffect Q ∧ Q.trace = (k : ℂ) ∧
    r = largestEnergyEigenvalue
      (ergotropicCoarseGraining M Q - energyDephasing (ergotropicCoarseGraining M Q))}

/-- Paper p.2, Eq.(2): robustness is the least nonnegative mixing amount with an
arbitrary POVM with the same outcomes that yields an incoherent POVM. The feasible
set is nonempty and its minimum finite for every finite POVM; no feasibility premise is added. -/
def measurementCoherenceRobustness {d n : ℕ}
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf {r | 0 ≤ r ∧ ∃ P N : Fin n → Matrix (Fin d) (Fin d) ℂ,
    IsPOVM P ∧ IsPOVM N ∧ measurementIncoherent N ∧
      ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u}

/-- Paper p.2, Eq.(3): maximum over i < j of the sum of absolute off-diagonal entries.
The empty maximum in dimension one is defined as zero by real sSup. -/
def measurementLinfCoherence {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup {r | ∃ i j : Fin d, i < j ∧ r = ∑ u, ‖M u i j‖}

/-- Paper p.8, Eq.(41): minimum over all adjacent energy gaps. Used only for d ≥ 2. -/
def minimumAdjacentEnergyGap {d : ℕ} (E : Fin d → ℝ) : ℝ :=
  sInf {r | ∃ i j : Fin d, j.val = i.val + 1 ∧ r = E j - E i}

/-- Paper pp.4,12: Bloch density matrix, with frozen Pauli-Y sign and ground state |0>. -/
def ergotropicBlochMatrix (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 + v 2 : ℝ) : ℂ) / 2, ((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / 2;
    ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / 2, ((1 - v 2 : ℝ) : ℂ) / 2]

/-- Paper p.4: squared Euclidean length of a real Bloch vector. -/
def ergotropicBlochLengthSquared (v : Fin 3 → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- Paper p.4: Euclidean scalar product of the Bloch vectors. -/
def ergotropicBlochDot (v w : Fin 3 → ℝ) : ℝ := ∑ i, v i * w i

/-- Paper pp.4,12: binary measurement with first effect A and complementary effect. -/
def ergotropicBinary {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Fin 2 → Matrix (Fin d) (Fin d) ℂ := ![A, 1 - A]

/-- Paper p.4: binary Bloch measurement; projective when its Bloch vector has length one. -/
def ergotropicBlochMeasurement (v : Fin 3 → ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ergotropicBinary (ergotropicBlochMatrix v)

/-- Paper p.4, Eq.(16): extended-real optimized quotient, only where the actual
incoherent ergotropy is strictly positive. Negative pointwise ratios are retained. -/
def ergotropicQuotient (E : ℝ) (M : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : EReal :=
  sSup {r | ∃ X : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix X ∧
    0 < incoherentErgotropy ![0, E] X ∧
    r = ((observationalErgotropy ![0, E] M X / incoherentErgotropy ![0, E] X : ℝ) : EReal)}

/-- Paper pp.8–9: noisy equatorial trine, with c in [0,1] in physical statements. -/
def noisyErgotropicTrine (c : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun u => ((2 / 3 : ℝ) : ℂ) • ergotropicBlochMatrix
    (![![c, 0, 0], ![-c / 2, c * Real.sqrt 3 / 2, 0],
      ![-c / 2, -c * Real.sqrt 3 / 2, 0]] u)

/-- Paper p.14, Eq.(C20): spectral width of a Hermitian matrix. -/
def ergotropicSpectralWidth {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  largestEnergyEigenvalue A + largestEnergyEigenvalue (-A)

/-- Paper p.14, Eq.(C29): largest minus smallest diagonal population. -/
def qutritPopulationWidth (X : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  max (X 0 0).re (max (X 1 1).re (X 2 2).re) -
    min (X 0 0).re (min (X 1 1).re (X 2 2).re)

/-- Paper p.13, Eqs.(C5),(C9): explicit PIO Kraus operators. -/
def advantagePIOKraus : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![1, 0, 0; 0, 1, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 0, 0, 0]]

/-- Paper p.13, Eq.(C1): Heisenberg dual of a finite Kraus map on each effect. -/
def ergotropicKrausDual {d k : ℕ} (K : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ j, (K j)ᴴ * A * K j

/-- Paper p.13: PIO implementation K_j=U_j P_j with orthogonal diagonal projectors
resolving the identity and incoherent unitary U_j. Unitarity plus one supported entry
per column is the monomial-unitary condition; no unitality on states is assumed. -/
def ergotropicPIOFamily {d k : ℕ} (K : Fin k → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ P U : Fin k → Matrix (Fin d) (Fin d) ℂ,
    (∑ j, P j) = 1 ∧
    (∀ j, (P j).IsHermitian ∧ P j * P j = P j ∧ energyDephasing (P j) = P j) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧
    (∀ j, (U j)ᴴ * U j = 1 ∧ U j * (U j)ᴴ = 1 ∧
      (∀ b, ∃ a, ∀ c, c ≠ a → U j c b = 0)) ∧ ∀ j, K j = U j * P j

/-- Paper p.13, Eq.(C11): original binary qutrit measurement in the PIO counterexample. -/
def advantagePIOOriginal : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
  ergotropicBinary !![11/50, -7/20, 0; -7/20, 29/50, 0; 0, 0, 29/50]

/-- Paper p.15, Eq.(C49): common optimizing density matrix for the two measurements. -/
def advantagePIOInput : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/3, -1/3, 0; -1/3, 1/3, 0; 0, 0, 1/3]

/-! Complete sanity examples for local definitions (no theorem proofs in this draft). -/

example {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    energyDephasing X i i = X i i := by simp [energyDephasing]

example {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (energyDephasing X) = energyExpectation E X := by
  simp [energyExpectation, energyDephasing]

example {d n : ℕ} : ergotropicCoarseGraining (fun _ : Fin n => (0 : Matrix (Fin d) (Fin d) ℂ)) 0 = 0 := by
  simp [ergotropicCoarseGraining]

example {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ergotropicBinary A 0 = A := by rfl

example (v : Fin 3 → ℝ) :
    ergotropicBlochMatrix v 0 1 = ((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / 2 := by rfl

example : ergotropicBlochLengthSquared ![0, 0, 1] = 1 := by
  norm_num [ergotropicBlochLengthSquared, Fin.sum_univ_succ]

example : noisyErgotropicTrine 0 0 0 0 = (1 / 3 : ℂ) := by
  norm_num [noisyErgotropicTrine, ergotropicBlochMatrix] <;> rfl

example : advantagePIOKraus 1 0 2 = 1 := by rfl

end QAlgorithms.Papers.Independent.Information100.P38


