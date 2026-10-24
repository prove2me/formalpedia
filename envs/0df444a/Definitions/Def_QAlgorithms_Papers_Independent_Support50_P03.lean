-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03
-- name    : QAlgorithms_Papers_Independent_Support50_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:21:59.688811+00:00
-- url     : https://prove2.me/theorems/63c56a31-e2e3-47ba-b445-020500827faf
-- title:
--   Definitions for Gaussian hypothesis testing and quantum illumination
-- statement:
--   The objects the formalized statements of *Gaussian hypothesis testing and quantum illumination* (arXiv:1608.06991) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HalfVacuumCovariance`: Physical covariances in vacuum-I/2 units, PDF p.2, (3)--(4). Unlike accepted interleaved vacuum-I PhysicalCovariance predicates, this uses grouped coordinates and V+iOmega/2. Positivity is Hermitian, not entrywise.
--   - `repeatBlock`: Repeated block A direct-sum A, PDF pp.2,7,12.
--   - `GroupedWilliamsonData`: Williamson data with the source's transpose convention, PDF p.2. Unlike Frontier30.P02.WilliamsonData, the modes are unordered and the reconstruction is S D S^T, rather than M^T D M. This is normal-mode data, not an ordinary diagonalization hypothesis.
--   - `realArcoth`: Real inverse hyperbolic cotangent, PDF p.3, after (6). Only abs x > 1 is used in matrix-function conclusions; its endpoint default is never used to model the source's singular Gibbs matrix.
--   - `FaithfulSpectrum`: Faithful Gaussian covariance spectrum, PDF pp.2,10.
--   - `gibbsMatrix`: Equation (6); used only with a faithful spectrum and symplectic S.
--   - `modeEigenbasis`: U tensor I from (A3), PDF p.7.
--   - `signedDiagonal`: The compatible eigenvalue diagonal [-D] direct-sum D in (A4).
--   - `arcothNodes`: DISTINCT nodes of the finite real spectrum of 2iVOmega. Finset.image removes repetitions, including repeated symplectic eigenvalues.
--   - `arcothPolynomial`: Primary matrix-function interpolation polynomial for Appendix A. On the diagonalizable matrices asserted below, interpolation on distinct spectral points is the usual spectral matrix function, independently of any choice of eigenvectors. Its values use real arcoth only at real eigenvalues.
--   - `spectralArcoth`: Polynomial functional calculus, defined independently of S and U (A5). The theorem guards the spectrum away from the poles at plus/minus one.
--   - `pureModeF1`: Grouped continuous extension f1 at a pure mode, (D2), PDF pp.10--11.
--   - `pureModeF2`: Grouped continuous extension f2 at a pure mode, (D2), PDF pp.10--11.
--   - `standardV0`: The reduced covariance V0 of (E2), PDF p.12.
--   - `pauliZ`: Pauli Z in (E1), PDF p.12.
--   - `standardParity`: I2 direct-sum Pauli Z in (E1), PDF p.12.
--   - `standardCovariance`: The complete standard covariance (E1), in grouped quadrature order.
--   - `standardY`: Discriminant y in (E6), PDF p.12; positivity is a conclusion below.
--   - `standardSpectrum`: Spectrum ordered as (nu_minus, nu_plus), exactly the diagonal in (E5).
--   - `standardOmegaPlus`: The positive diagonal entry omega_plus in (E5), PDF p.12.
--   - `standardOmegaMinus`: Signed omega_minus: (E5) needs sign(c), and zero at c=0. The printed positive root is correct for the application's c >= 0 only.
--   - `standardS0`: Signed S0 from (E5), PDF p.12.
--   - `standardS`: Constructed full symplectic matrix of (E4), PDF p.12.
--   - `standardReducedGibbs`: Reduced Gibbs factor S0 arcoth(2D) S0 in (E9), PDF p.12. Only faithful standard spectra are used in the Gibbs equality below.
-- source:
--   Gaussian hypothesis testing and quantum illumination, arXiv:1608.06991v2, https://arxiv.org/abs/1608.06991v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

/-!
Gaussian hypothesis testing and quantum illumination, arXiv:1608.06991v2.
The three independent algebraic/endpoint nodes below do not replace oscillator
states by finite matrices: their objects are the actual finite covariance matrices.
Operator-dependent nodes are explicitly deferred in this unit's HARD.md/GAPS.json.
Exact coordinate and matrix primitives reuse pinned accepted modules.
The remaining paper-specific definitions are local, with complete bodies. Compilation is
pending the separately authorized batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators ComplexOrder Topology Matrix

namespace QAlgorithms.Papers.Independent.Support50.P03

-- These accepted primitives use exactly the grouped coordinate type and matrix entries.
open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase complexify sigma thermalCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

/-- Physical covariances in vacuum-I/2 units, PDF p.2, (3)--(4).
Unlike accepted interleaved vacuum-I PhysicalCovariance predicates, this uses
grouped coordinates and V+iOmega/2. Positivity is Hermitian, not entrywise. -/
def HalfVacuumCovariance {n : ℕ} (V : PhaseMatrix n) : Prop :=
  V.transpose = V ∧ V.PosDef ∧
    (complexify V + (Complex.I / 2) • complexify (sigma n)).PosSemidef

/-- Repeated block A direct-sum A, PDF pp.2,7,12. -/
def repeatBlock {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : PhaseMatrix n :=
  Matrix.fromBlocks A 0 0 A

/-- Williamson data with the source's transpose convention, PDF p.2.
Unlike Frontier30.P02.WilliamsonData, the modes are unordered and the
reconstruction is S D S^T, rather than M^T D M. This is normal-mode data,
not an ordinary diagonalization hypothesis. -/
def GroupedWilliamsonData {n : ℕ} (V : PhaseMatrix n) (nu : Fin n → ℝ)
    (S : PhaseMatrix n) : Prop :=
  (∀ j, (1 / 2 : ℝ) ≤ nu j) ∧
    S ∈ Matrix.symplecticGroup (Fin n) ℝ ∧
    V = S * thermalCovariance nu * S.transpose

/-- Real inverse hyperbolic cotangent, PDF p.3, after (6).
Only abs x > 1 is used in matrix-function conclusions; its endpoint default
is never used to model the source's singular Gibbs matrix. -/
def realArcoth (x : ℝ) : ℝ := Real.log ((x + 1) / (x - 1)) / 2

/-- Faithful Gaussian covariance spectrum, PDF pp.2,10. -/
def FaithfulSpectrum {n : ℕ} (nu : Fin n → ℝ) : Prop :=
  ∀ j, (1 / 2 : ℝ) < nu j

/-- Equation (6); used only with a faithful spectrum and symplectic S. -/
def gibbsMatrix {n : ℕ} (S : PhaseMatrix n) (nu : Fin n → ℝ) : PhaseMatrix n :=
  (-2 : ℝ) • (sigma n * S * thermalCovariance (fun j => realArcoth (2 * nu j)) *
    S.transpose * sigma n)

/-- U tensor I from (A3), PDF p.7. -/
def modeEigenbasis (n : ℕ) : Matrix (Phase n) (Phase n) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 1
      (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))
      ((-Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ))

/-- The compatible eigenvalue diagonal [-D] direct-sum D in (A4). -/
def signedDiagonal {n : ℕ} (nu : Fin n → ℝ) : PhaseMatrix n :=
  Matrix.fromBlocks (Matrix.diagonal (fun j => -nu j)) 0 0 (Matrix.diagonal nu)

/-- DISTINCT nodes of the finite real spectrum of 2iVOmega.
Finset.image removes repetitions, including repeated symplectic eigenvalues. -/
def arcothNodes {n : ℕ} (nu : Fin n → ℝ) : Finset ℂ := by
  classical
  exact Finset.univ.image (fun k : Phase n =>
    match k with
    | Sum.inl j => ((-2 * nu j : ℝ) : ℂ)
    | Sum.inr j => ((2 * nu j : ℝ) : ℂ))

/-- Primary matrix-function interpolation polynomial for Appendix A.
On the diagonalizable matrices asserted below, interpolation on distinct
spectral points is the usual spectral matrix function, independently of any
choice of eigenvectors. Its values use real arcoth only at real eigenvalues. -/
def arcothPolynomial {n : ℕ} (nu : Fin n → ℝ) : Polynomial ℂ := by
  classical
  exact Lagrange.interpolate (arcothNodes nu) (fun z : ℂ => z)
    (fun z => (realArcoth z.re : ℂ))

/-- Polynomial functional calculus, defined independently of S and U (A5).
The theorem guards the spectrum away from the poles at plus/minus one. -/
def spectralArcoth {n : ℕ} (nu : Fin n → ℝ)
    (B : Matrix (Phase n) (Phase n) ℂ) : Matrix (Phase n) (Phase n) ℂ :=
  Polynomial.aeval B (arcothPolynomial nu)

/-- Grouped continuous extension f1 at a pure mode, (D2), PDF pp.10--11. -/
def pureModeF1 (lambda : ℝ) : ℝ :=
  if lambda = 1 / 2 then 0
  else (realArcoth (2 * lambda)) ^ 2 * ((2 * lambda) ^ 2 - 1)

/-- Grouped continuous extension f2 at a pure mode, (D2), PDF pp.10--11. -/
def pureModeF2 (lambda : ℝ) : ℝ :=
  if lambda = 1 / 2 then 0
  else realArcoth (2 * lambda) * ((2 * lambda) ^ 2 - 1)

/-- The reduced covariance V0 of (E2), PDF p.12. -/
def standardV0 (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, c; c, b]

/-- Pauli Z in (E1), PDF p.12. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

/-- I2 direct-sum Pauli Z in (E1), PDF p.12. -/
def standardParity : PhaseMatrix 2 :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 pauliZ

/-- The complete standard covariance (E1), in grouped quadrature order. -/
def standardCovariance (a b c : ℝ) : PhaseMatrix 2 :=
  standardParity * repeatBlock (standardV0 a b c) * standardParity

/-- Discriminant y in (E6), PDF p.12; positivity is a conclusion below. -/
def standardY (a b c : ℝ) : ℝ := (a + b) ^ 2 - 4 * c ^ 2

/-- Spectrum ordered as (nu_minus, nu_plus), exactly the diagonal in (E5). -/
def standardSpectrum (a b c : ℝ) : Fin 2 → ℝ :=
  ![(Real.sqrt (standardY a b c) - (b - a)) / 2,
    (Real.sqrt (standardY a b c) + (b - a)) / 2]

/-- The positive diagonal entry omega_plus in (E5), PDF p.12. -/
def standardOmegaPlus (a b c : ℝ) : ℝ :=
  Real.sqrt ((a + b + Real.sqrt (standardY a b c)) /
    (2 * Real.sqrt (standardY a b c)))

/-- Signed omega_minus: (E5) needs sign(c), and zero at c=0.
The printed positive root is correct for the application's c >= 0 only. -/
def standardOmegaMinus (a b c : ℝ) : ℝ :=
  if c = 0 then 0
  else (if 0 < c then 1 else -1) *
    Real.sqrt ((a + b - Real.sqrt (standardY a b c)) /
      (2 * Real.sqrt (standardY a b c)))

/-- Signed S0 from (E5), PDF p.12. -/
def standardS0 (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![standardOmegaPlus a b c, standardOmegaMinus a b c;
     standardOmegaMinus a b c, standardOmegaPlus a b c]

/-- Constructed full symplectic matrix of (E4), PDF p.12. -/
def standardS (a b c : ℝ) : PhaseMatrix 2 :=
  standardParity * repeatBlock (standardS0 a b c) * standardParity

/-- Reduced Gibbs factor S0 arcoth(2D) S0 in (E9), PDF p.12.
Only faithful standard spectra are used in the Gibbs equality below. -/
def standardReducedGibbs (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  standardS0 a b c *
    Matrix.diagonal (fun j => realArcoth (2 * standardSpectrum a b c j)) *
    standardS0 a b c

example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [sigma]

example : sigma 1 (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp [sigma]

example (n : ℕ) (nu : Fin n → ℝ) (j : Fin n) :
    thermalCovariance nu (Sum.inl j) (Sum.inl j) = nu j := by
  simp [thermalCovariance]

example (n : ℕ) (nu : Fin n → ℝ) (j : Fin n) :
    signedDiagonal nu (Sum.inl j) (Sum.inl j) = -nu j := by
  simp [signedDiagonal]

example : pureModeF1 (1 / 2) = 0 := by simp [pureModeF1]

example : pureModeF2 (1 / 2) = 0 := by simp [pureModeF2]

example (a b : ℝ) : standardOmegaMinus a b 0 = 0 := by
  simp [standardOmegaMinus]

example (a b c : ℝ) : standardV0 a b c 0 1 = c := by
  rfl

example (a b c : ℝ) :
    standardCovariance a b c (Sum.inr 0) (Sum.inr 1) = -c := by
  simp [standardCovariance, standardParity, repeatBlock, standardV0, pauliZ,
    Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type]

end QAlgorithms.Papers.Independent.Support50.P03


