-- Prove2me | Definitions.Def_QAlgorithms_Defs_DirichletShadowLearning
-- name    : QAlgorithms_Defs_DirichletShadowLearning
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:35.720985+00:00
-- url     : https://prove2.me/theorems/f0266d0f-a99b-424d-8b57-c59ebe6ba90b
-- title:
--   DirichletShadowLearning
-- statement:
--   DirichletShadowLearning
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DirichletShadowLearning.lean

import Definitions.Def_QAlgorithms_Defs_LocalPauliShadows
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.GroundStateLearning

/-- Exactly the Euclidean integer frequency ball, enumerated within its coordinate bounds
(2106.12627 pp.26-27, Eqs.(E2)-(E3); p.36, Eq.(F44)). -/
def frequencyBall (m : ℕ) (Lambda : ℝ) (_nonnegative : 0 ≤ Lambda) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset fun _ : Fin m => Finset.Icc (-⌊Lambda⌋) ⌊Lambda⌋).filter
    fun k => ∑ j, (k j : ℝ)^2 ≤ Lambda^2

/-- Length-two-cube Fourier kernel; no periodicity assumption is inserted
(2106.12627 pp.26-27, Eqs.(E2)-(E3); p.36, Eq.(F44)). -/
def dirichletKernel {m : ℕ} (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (x y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ k ∈ frequencyBall m Lambda hLambda,
    Real.cos (Real.pi*∑ j, (k j : ℝ)*(x j-y j))

/-- Named empirical single-shadow predictor, not an exact-state-label average
(2106.12627 p.27, Eq.(E3), and p.33, Eq.(F27)). -/
def predictor {n m N : ℕ} (_hN : 0 < N) (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n)
    (x : EuclideanSpace ℝ (Fin m)) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((N : ℂ)⁻¹) • ∑ i, (dirichletKernel Lambda hLambda x (data i).1 : ℂ) • snapshot (data i).2

/-- Nonnegative extended population squared-error integral, avoiding default-zero
nonintegrable Bochner risks (2106.12627 p.30, Eq.(F4)). -/
def populationRisk {n m : ℕ} (O : Matrix (Qubits n) (Qubits n) ℂ) (_hermitian : O.IsHermitian)
    (rho estimate : EuclideanSpace ℝ (Fin m) → Matrix (Qubits n) (Qubits n) ℂ)
    (_measurableRho : Measurable rho) (_measurableEstimate : Measurable estimate) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((O*(estimate x-rho x)).trace.re^2) ∂parameterCubeLaw m

/-- Partial trace onto a named ordered subsystem; the complement is summed exactly once
(2106.12627 p.13, Eq.(A8); p.4, reduced-state prediction). -/
def reducedOperator {n q : ℕ} (w : Fin q ↪ Fin n)
    (X : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.of fun a b =>
    ∑ z ∈ Finset.univ.filter (fun z : Qubits n => ∀ j, z (w j) = false),
      X (overwrite w z a) (overwrite w z b)

/-- Zero cutoff retains exactly the zero frequency (2106.12627 p.36, Eq.(F44)). -/
theorem frequencyBall_zero (m : ℕ) : frequencyBall m 0 le_rfl = {0} := by
  ext k
  simp [frequencyBall, Fintype.mem_piFinset, funext_iff]
  intro hk
  simp [hk]

example {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    dirichletKernel 0 le_rfl x y = 1 := by
  simp [dirichletKernel, frequencyBall_zero]

example {n m : ℕ} (O : Matrix (Qubits n) (Qubits n) ℂ) (hO : O.IsHermitian)
    (rho : EuclideanSpace ℝ (Fin m) → Matrix (Qubits n) (Qubits n) ℂ) (h : Measurable rho) :
    populationRisk O hO rho rho h h = 0 := by simp [populationRisk]

example {n q : ℕ} (w : Fin q ↪ Fin n) : reducedOperator w 0 = 0 := by
  ext a b
  simp [reducedOperator]

end QAlgorithms.GroundStateLearning


