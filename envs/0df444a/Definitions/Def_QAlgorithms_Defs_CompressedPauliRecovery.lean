-- Prove2me | Definitions.Def_QAlgorithms_Defs_CompressedPauliRecovery
-- name    : QAlgorithms_Defs_CompressedPauliRecovery
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:34.278039+00:00
-- url     : https://prove2.me/theorems/4dfc3a39-5f07-4e14-87ab-397362787670
-- title:
--   CompressedPauliRecovery
-- statement:
--   CompressedPauliRecovery
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CompressedPauliRecovery.lean

import Definitions.Def_QAlgorithms_Defs_PauliDesigns
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.CompressedTomography

/-- Pauli sampling with the source sqrt(d/m) scale, on the Hermitian domain
(1205.2300 p.4, Eq.(1)). Positive m excludes division by zero. -/
def samplingMap {n m : ℕ} (P : Fin m → PauliDesign.Label n) (_hm : 0 < m)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (_hermitian : X.IsHermitian) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun i => Real.sqrt ((2 : ℝ)^n/m)*(pauliOps (P i)*X).trace.re

/-- The real Hilbert-Schmidt adjoint, computed from the same design
(1205.2300 p.6, Eq.(10)). -/
def samplingAdjoint {n m : ℕ} (P : Fin m → PauliDesign.Label n) (_hm : 0 < m)
    (v : EuclideanSpace ℝ (Fin m)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (Real.sqrt ((2 : ℝ)^n/m) : ℂ) • ∑ i, (v i : ℂ) • pauliOps (P i)

/-- Attained Dantzig trace minimization, without PSD or trace constraints
(1205.2300 p.4, Eq.(3)). -/
def IsDantzigSelector {n m : ℕ} (P : Fin m → PauliDesign.Label n) (hm : 0 < m)
    (y : EuclideanSpace ℝ (Fin m)) (lam : ℝ)
    (X : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  ∃ hX : X.IsHermitian,
    specNorm (samplingAdjoint P hm (samplingMap P hm X hX-y)) ≤ lam ∧
    ∀ (Y : Matrix (Qubits n) (Qubits n) ℂ) (hY : Y.IsHermitian),
      specNorm (samplingAdjoint P hm (samplingMap P hm Y hY-y)) ≤ lam →
      traceNorm X ≤ traceNorm Y

/-- Squared Euclidean residual plus trace-norm regularization
(1205.2300 p.4, Eq.(4)). -/
def lassoObjective {n m : ℕ} (P : Fin m → PauliDesign.Label n) (hm : 0 < m)
    (y : EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (hX : X.IsHermitian) : ℝ :=
  (1/2 : ℝ)*‖samplingMap P hm X hX-y‖^2+mu*traceNorm X

/-- All attained Lasso minimizers over Hermitian matrices
(1205.2300 p.4, Eq.(4)). No uniqueness or accuracy is assumed. -/
def IsMatrixLasso {n m : ℕ} (P : Fin m → PauliDesign.Label n) (hm : 0 < m)
    (y : EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    (X : Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  ∃ hX : X.IsHermitian, ∀ (Y : Matrix (Qubits n) (Qubits n) ℂ) (hY : Y.IsHermitian),
    lassoObjective P hm y mu X hX ≤ lassoObjective P hm y mu Y hY

/-- Unnormalized truncation in Mathlib's fixed, decreasing spectral basis; ties use that
basis, with no further choice (1205.2300 p.5, §II.C). -/
def bestRankApproximation {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (positive : rho.PosSemidef) (r : ℕ) (_hr : 1 ≤ r ∧ r ≤ 2^n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  let H := positive.isHermitian
  let index : Fin (Fintype.card (Qubits n)) ≃ Qubits n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  ∑ k : Fin (Fintype.card (Qubits n)), if k.val < r
    then (H.eigenvalues₀ k : ℂ) • pureDensity (H.eigenvectorBasis (index k)) else 0

example {n m : ℕ} (P : Fin m → PauliDesign.Label n) (hm : 0 < m) :
    samplingMap P hm 0 Matrix.isHermitian_zero = 0 := by
  ext i
  simp [samplingMap]

example {n m : ℕ} (P : Fin m → PauliDesign.Label n) (hm : 0 < m) :
    samplingAdjoint P hm 0 = 0 := by simp [samplingAdjoint]

example (P : Fin 1 → PauliDesign.Label 0) (x : ℝ) :
    samplingMap P (by omega) ((x : ℂ) • 1)
      (by change (((x : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ))ᴴ) = _; simp) =
      WithLp.toLp 2 (fun _ => x) := by
  ext i
  simp [samplingMap, pauliOps, Stabilizer.PauliString.toMatrix,
    Matrix.trace, Matrix.mul_apply, Matrix.one_apply]

end QAlgorithms.CompressedTomography


