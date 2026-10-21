-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P11
-- name    : QAlgorithms_Papers_Independent_Next46_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:02:36.151726+00:00
-- url     : https://prove2.me/theorems/39b7e350-46fd-40bf-b447-c7fa6e6e4da7
-- title:
--   Definitions for R\'enyi divergences as weighted non-commutative vector valued $L_p$-spaces
-- statement:
--   The objects the formalized statements of *R\'enyi divergences as weighted non-commutative vector valued $L_p$-spaces* (arXiv:1608.05317) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `supportedScalarPower`: Supported scalar spectral power, PDF p.4: every power is zero on the kernel, including power zero and negative powers.
--   - `supportedMatrixPower`: Supported real powers of finite Hermitian matrices, PDF pp.4--5. The matrix spectrum is finite, so every scalar function on it is continuous. Uses outside the positive-semidefinite cone are not part of the theorem.
--   - `MatrixSupportIncluded`: Support containment for positive matrices, PDF p.3: ker(sigma) is contained in ker(rho). This is support containment, not bounded domination in the general-algebra setting.
--   - `hilbertSchmidtSize`: Hilbert--Schmidt vector norm in the standard representation, PDF p.3. The implementing vector is sqrt(rho), rather than rho.
--   - `IsMatrixDensity`: Densities of unit implementing vectors, PDF p.3 and Definition 2, p.5. The density W ranges over all positive trace-one matrices.
--   - `matrixSpatialPowerSize`: Finite standard-representation value of the spatial-power vector norm in Eq.(10), PDF p.5. W is the density of the optimizing unit vector on the commutant, identified with a matrix by transpose. The two tensor factors act as left and right multiplication; sqrt(rho) is the input vector.
--   - `finiteAMNorm`: Definition 2, PDF p.5, in the standard finite matrix representation using Eq.(10). For p >= 2 the support-failure branch is explicitly infinite. For p < 2 the infimum retains commutant support containment. These are extended nonnegative suprema/infima, never real suprema with junk values. Only finite p >= 1 on positive inputs and n > 0 are used below.
--   - `finiteAMDivergence`: Definition 7, PDF p.8: alpha = p/2 and Q_alpha = norm^(2 alpha). Natural logarithms are extended: log(0) = -infinity and log(infinity) = infinity. The source excludes alpha = 1.
-- source:
--   R\'enyi divergences as weighted non-commutative vector valued Lₚ-spaces, arXiv:1608.05317v2, https://arxiv.org/abs/1608.05317v2

import Mathlib

/-!
Concrete standard-matrix statement from arXiv:1608.05317v2, Eq.(39).
The left side is defined by the optimization in Definition 2 and Eq.(10),
not by the sandwiched expression whose identification is asserted.
General von Neumann algebra results and three source contradictions are
recorded individually in the assigned unit's HARD.md and GAPS.json.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P11

attribute [local instance] Classical.propDecidable

/-- Supported scalar spectral power, PDF p.4: every power is zero on the
kernel, including power zero and negative powers. -/
def supportedScalarPower (s x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ s

example (s : ℝ) : supportedScalarPower s 0 = 0 := by
  simp [supportedScalarPower]

/-- Supported real powers of finite Hermitian matrices, PDF pp.4--5.
The matrix spectrum is finite, so every scalar function on it is continuous.
Uses outside the positive-semidefinite cone are not part of the theorem. -/
def supportedMatrixPower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc (supportedScalarPower s) A

example {n : ℕ} (s : ℝ) :
    supportedMatrixPower (0 : Matrix (Fin n) (Fin n) ℂ) s = 0 := by
  simp [supportedMatrixPower, supportedScalarPower]

/-- Support containment for positive matrices, PDF p.3: ker(sigma) is
contained in ker(rho). This is support containment, not bounded domination
in the general-algebra setting. -/
def MatrixSupportIncluded {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ v : Fin n → ℂ, sigma.mulVec v = 0 → rho.mulVec v = 0

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : MatrixSupportIncluded A A := by
  intro v hv
  exact hv

/-- Hilbert--Schmidt vector norm in the standard representation, PDF p.3.
The implementing vector is sqrt(rho), rather than rho. -/
def hilbertSchmidtSize {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j))

example {n : ℕ} : hilbertSchmidtSize (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hilbertSchmidtSize]

/-- Densities of unit implementing vectors, PDF p.3 and Definition 2, p.5.
The density W ranges over all positive trace-one matrices. -/
def IsMatrixDensity {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  W.PosSemidef ∧ W.trace = 1

/-- Finite standard-representation value of the spatial-power vector norm
in Eq.(10), PDF p.5. W is the density of the optimizing unit vector on the
commutant, identified with a matrix by transpose. The two tensor factors
act as left and right multiplication; sqrt(rho) is the input vector. -/
def matrixSpatialPowerSize {n : ℕ} (rho sigma W : Matrix (Fin n) (Fin n) ℂ)
    (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hilbertSchmidtSize
    (supportedMatrixPower W (1 / 2 - 1 / p) *
      supportedMatrixPower rho (1 / 2) *
      supportedMatrixPower sigma (1 / p - 1 / 2)))

/-- Definition 2, PDF p.5, in the standard finite matrix representation
using Eq.(10). For p >= 2 the support-failure branch is explicitly infinite.
For p < 2 the infimum retains commutant support containment. These are
extended nonnegative suprema/infima, never real suprema with junk values.
Only finite p >= 1 on positive inputs and n > 0 are used below. -/
def finiteAMNorm {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ)
    (p : ℝ) : ℝ≥0∞ :=
  if 2 ≤ p then
    if MatrixSupportIncluded rho sigma then
      sSup {r | ∃ W : Matrix (Fin n) (Fin n) ℂ,
        IsMatrixDensity W ∧ r = matrixSpatialPowerSize rho sigma W p}
    else ⊤
  else
    sInf {r | ∃ W : Matrix (Fin n) (Fin n) ℂ,
      IsMatrixDensity W ∧ MatrixSupportIncluded rho W ∧
        r = matrixSpatialPowerSize rho sigma W p}

example {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ) (p : ℝ)
    (hp : 2 ≤ p) (hs : ¬ MatrixSupportIncluded rho sigma) :
    finiteAMNorm rho sigma p = ⊤ := by
  simp [finiteAMNorm, hp, hs]

/-- Definition 7, PDF p.8: alpha = p/2 and Q_alpha = norm^(2 alpha).
Natural logarithms are extended: log(0) = -infinity and log(infinity) =
infinity. The source excludes alpha = 1. -/
def finiteAMDivergence {n : ℕ} (rho sigma : Matrix (Fin n) (Fin n) ℂ)
    (alpha : ℝ) : EReal :=
  ((1 / (alpha - 1) : ℝ) : EReal) *
    ENNReal.log ((finiteAMNorm rho sigma (2 * alpha)) ^ (2 * alpha))

example : ENNReal.log 0 = ⊥ := by simp

example : ENNReal.log ⊤ = ⊤ := by simp

end QAlgorithms.Papers.Independent.Next46.P11


