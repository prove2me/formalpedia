-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
-- name    : QAlgorithms_Papers_Independent_Dependency50_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:05:51.216384+00:00
-- url     : https://prove2.me/theorems/835f632a-69f6-45e0-b804-82bee10f8cdb
-- title:
--   Definitions for The optimal unitary dilation for bosonic Gaussian channels
-- statement:
--   The objects the formalized statements of *The optimal unitary dilation for bosonic Gaussian channels* (arXiv:1009.1108) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Phase`: Quadrature order `(Q_1,...,Q_n; P_1,...,P_n)`, PDF p.2, Eq.(4).
--   - `complexify`: Entrywise complexification: ranks and kernels are complex, PDF p.2.
--   - `sigma`: Canonical symplectic form in units `hbar = 1`, PDF p.2, Eq.(4).
--   - `jointSigma`: Subsystem order `(Q_A,P_A;Q_B,P_B)`, PDF p.3, Eq.(18), p.4, Eq.(30).
--   - `commutatorDefect`: Channel commutator defect, PDF p.2, Eq.(3); no invertibility is assumed.
--   - `cpMatrix`: Complete positivity matrix `Y - i Sigma`, PDF p.2, Eq.(3).
--   - `complexKernel`: Kernel on complex column vectors, PDF p.2, Eqs.(6)–(10).
--   - `realRangeProjection`: Orthogonal projection onto the real range. For symmetric positive semidefinite `A` this is the support projector `Pi`, PDF p.7, Eqs.(A5)–(A6). Finite-dimensional subspaces are closed, so this projection always exists.
--   - `supportInverse`: Source support formula for the MP inverse on symmetric positive semidefinite matrices, PDF p.7, Eqs.(A5)–(A6), and footnote 21. Only that domain is used: `A + (1 - Pi)` is invertible there, including singular `A`. This expression is not asserted to be the MP inverse of an arbitrary nonsymmetric matrix.
--   - `rankResidual`: Residual `A - B Aplus B^T`, PDF p.7, Eq.(A2).
--   - `physicalCovariance`: Covariance description of normalized Gaussian states, PDF p.8, Eq.(B1). The form is canonical or a direct sum of canonical forms. Arbitrary first moments do not affect any of the covariance results.
--   - `pureCovariance`: A physical Gaussian covariance is pure precisely when its determinant is one, PDF p.5, Eq.(47). Used only with canonical forms of determinant one.
--   - `hasGaussianPurification`: Gaussian purification on exactly `q` ancillary modes in covariance coordinates, PDF pp.8–9, Appendix B.1. The prescribed upper-left block fixes the marginal. Purity and physicality restrict this to Gaussian purifications. No bosonic Hilbert space is replaced by a finite-dimensional truncation.
--   - `thermalCovariance`: Williamson diagonal covariance, PDF p.8, Eq.(B2).
--   - `thermalF`: Negative square-root convention, PDF p.3, Eq.(20).
--   - `thermalCross`: Explicit off-diagonal correlation block, PDF p.9, Eq.(B4).
--   - `thermalPurification`: Initial `n`-ancilla purification covariance, PDF p.9, Eqs.(B3)–(B4), before ancillary vacuum modes are removed.
--   - `unitCount`: Multiplicity of the unit symplectic eigenvalue, PDF p.9, Eqs.(B5)–(B6).
-- source:
--   The optimal unitary dilation for bosonic Gaussian channels, arXiv:1009.1108v1, https://arxiv.org/abs/1009.1108v1

import Mathlib

/-!
# Optimal Gaussian dilation: finite covariance statements
Source: Caruso–Eisert–Giovannetti–Holevo, arXiv:1009.1108v1.
The operational all-input Fock-space dilation statements are explicitly deferred
in HARD.md and GAPS.json. Covariance witnesses do not implement a channel on
arbitrary density operators.
-/

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P10

/-- Quadrature order `(Q_1,...,Q_n; P_1,...,P_n)`, PDF p.2, Eq.(4). -/
abbrev Phase (n : ℕ) := Fin n ⊕ Fin n

/-- Entrywise complexification: ranks and kernels are complex, PDF p.2. -/
def complexify {a b : Type*} (A : Matrix a b ℝ) : Matrix a b ℂ :=
  fun i j => (A i j : ℂ)

/-- Canonical symplectic form in units `hbar = 1`, PDF p.2, Eq.(4). -/
def sigma (n : ℕ) : Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- Subsystem order `(Q_A,P_A;Q_B,P_B)`, PDF p.3, Eq.(18), p.4, Eq.(30). -/
def jointSigma (n q : ℕ) :
    Matrix (Phase n ⊕ Phase q) (Phase n ⊕ Phase q) ℝ :=
  Matrix.fromBlocks (sigma n) 0 0 (sigma q)

/-- Channel commutator defect, PDF p.2, Eq.(3); no invertibility is assumed. -/
def commutatorDefect {n : ℕ} (X : Matrix (Phase n) (Phase n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  sigma n - X.transpose * sigma n * X

/-- Complete positivity matrix `Y - i Sigma`, PDF p.2, Eq.(3). -/
def cpMatrix {n : ℕ} (X Y : Matrix (Phase n) (Phase n) ℝ) :
    Matrix (Phase n) (Phase n) ℂ :=
  complexify Y - Complex.I • complexify (commutatorDefect X)

/-- Kernel on complex column vectors, PDF p.2, Eqs.(6)–(10). -/
def complexKernel {a : Type*} [Fintype a] (A : Matrix a a ℂ) :
    Submodule ℂ (a → ℂ) :=
  LinearMap.ker A.mulVecLin

/-- Orthogonal projection onto the real range. For symmetric positive semidefinite
`A` this is the support projector `Pi`, PDF p.7, Eqs.(A5)–(A6).
Finite-dimensional subspaces are closed, so this projection always exists. -/
def realRangeProjection {a : Type*} [Fintype a] [DecidableEq a]
    (A : Matrix a a ℝ) : Matrix a a ℝ :=
  fun i j =>
    ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection
      (EuclideanSpace.single j 1)) i

/-- Source support formula for the MP inverse on symmetric positive semidefinite
matrices, PDF p.7, Eqs.(A5)–(A6), and footnote 21. Only that domain is used:
`A + (1 - Pi)` is invertible there, including singular `A`. This expression is
not asserted to be the MP inverse of an arbitrary nonsymmetric matrix. -/
def supportInverse {a : Type*} [Fintype a] [DecidableEq a]
    (A : Matrix a a ℝ) : Matrix a a ℝ :=
  let P := realRangeProjection A
  P * (A + (1 - P))⁻¹ * P

/-- Residual `A - B Aplus B^T`, PDF p.7, Eq.(A2). -/
def rankResidual {a : Type*} [Fintype a] [DecidableEq a]
    (A B : Matrix a a ℝ) : Matrix a a ℝ :=
  A - B * supportInverse A * B.transpose

/-- Covariance description of normalized Gaussian states, PDF p.8, Eq.(B1).
The form is canonical or a direct sum of canonical forms. Arbitrary first
moments do not affect any of the covariance results. -/
def physicalCovariance {a : Type*} [Fintype a]
    (G omega : Matrix a a ℝ) : Prop :=
  G.transpose = G ∧ (complexify G - Complex.I • complexify omega).PosSemidef

/-- A physical Gaussian covariance is pure precisely when its determinant is one,
PDF p.5, Eq.(47). Used only with canonical forms of determinant one. -/
def pureCovariance {a : Type*} [Fintype a] [DecidableEq a]
    (G omega : Matrix a a ℝ) : Prop :=
  physicalCovariance G omega ∧ G.det = 1

/-- Gaussian purification on exactly `q` ancillary modes in covariance coordinates,
PDF pp.8–9, Appendix B.1. The prescribed upper-left block fixes the marginal.
Purity and physicality restrict this to Gaussian purifications. No bosonic
Hilbert space is replaced by a finite-dimensional truncation. -/
def hasGaussianPurification {n : ℕ}
    (G : Matrix (Phase n) (Phase n) ℝ) (q : ℕ) : Prop :=
  ∃ B : Matrix (Phase q) (Phase q) ℝ,
    ∃ C : Matrix (Phase n) (Phase q) ℝ,
      pureCovariance (Matrix.fromBlocks G C C.transpose B) (jointSigma n q)

/-- Williamson diagonal covariance, PDF p.8, Eq.(B2). -/
def thermalCovariance {n : ℕ} (D : Fin n → ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal D) 0 0 (Matrix.diagonal D)

/-- Negative square-root convention, PDF p.3, Eq.(20). -/
def thermalF (d : ℝ) : ℝ := -Real.sqrt (d ^ 2 - 1)

/-- Explicit off-diagonal correlation block, PDF p.9, Eq.(B4). -/
def thermalCross {n : ℕ} (D : Fin n → ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks 0 (Matrix.diagonal (fun j => thermalF (D j)))
    (Matrix.diagonal (fun j => thermalF (D j))) 0

/-- Initial `n`-ancilla purification covariance, PDF p.9, Eqs.(B3)–(B4),
before ancillary vacuum modes are removed. -/
def thermalPurification {n : ℕ} (D : Fin n → ℝ) :
    Matrix (Phase n ⊕ Phase n) (Phase n ⊕ Phase n) ℝ :=
  Matrix.fromBlocks (thermalCovariance D) (thermalCross D)
    (thermalCross D).transpose (thermalCovariance D)

/-- Multiplicity of the unit symplectic eigenvalue, PDF p.9, Eqs.(B5)–(B6). -/
def unitCount {n : ℕ} (D : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => D j = 1)).card

/-! Small sanity cases for coordinates, singular support, and purification counts. -/

example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [sigma]

example : sigma 1 (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp [sigma]

example (n : ℕ) : commutatorDefect (1 : Matrix (Phase n) (Phase n) ℝ) = 0 := by
  simp [commutatorDefect]

example {a : Type*} [Fintype a] [DecidableEq a] :
    realRangeProjection (0 : Matrix a a ℝ) = 0 := by
  ext i j
  simp [realRangeProjection]

example {a : Type*} [Fintype a] [DecidableEq a] :
    supportInverse (0 : Matrix a a ℝ) = 0 := by
  have hp : realRangeProjection (0 : Matrix a a ℝ) = 0 := by
    ext i j
    simp [realRangeProjection]
  simp [supportInverse, hp]

example : thermalF 1 = 0 := by
  simp [thermalF]

example (n : ℕ) : unitCount (fun _ : Fin n => (1 : ℝ)) = n := by
  simp [unitCount]

example (n : ℕ) : thermalCovariance (fun _ : Fin n => (1 : ℝ)) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [thermalCovariance, Matrix.one_apply]

example (n : ℕ) : thermalCross (fun _ : Fin n => (1 : ℝ)) = 0 := by
  ext i j
  cases i <;> cases j <;> simp [thermalCross, thermalF]

end QAlgorithms.Papers.Independent.Dependency50.P10


