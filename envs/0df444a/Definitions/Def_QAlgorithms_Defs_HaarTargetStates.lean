-- Prove2me | Definitions.Def_QAlgorithms_Defs_HaarTargetStates
-- name    : QAlgorithms_Defs_HaarTargetStates
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:39.364305+00:00
-- url     : https://prove2.me/theorems/5b763454-12d4-4fa7-900f-e4c7c196243c
-- title:
--   HaarTargetStates
-- statement:
--   HaarTargetStates
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HaarTargetStates.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open MeasureTheory

namespace QAlgorithms.TwoBasisCertification

variable {n m d k b w M K N c out : ℕ}

/-- Total Gaussian normalization; the zero Gaussian vector is replaced by
the zero computational ket (2602.11616 pp.5,9,13). -/
def haarNormalize (n : ℕ) (g : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits n) :=
  if g = 0 then zeroKet n else normalizedVec g

/-- Haar target law as normalized isotropic complex Gaussian
(2602.11616 pp.5,9,13), on unit vectors rather than phase representatives. -/
def haarTargetLaw (n : ℕ) : Measure (EuclideanSpace ℂ (Qubits n)) :=
  (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ (Qubits n))).map (haarNormalize n)

/-- Measurability excludes the nonmeasurable-map zero default
(2602.11616 p.13). -/
theorem haarNormalize_measurable (n : ℕ) : Measurable (haarNormalize n) := by
  unfold haarNormalize normalizedVec
  exact Measurable.ite (isClosed_singleton.measurableSet) measurable_const
    (by fun_prop)

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.5,9,13). -/
example (n : ℕ) : haarNormalize n 0 = zeroKet n := by simp [haarNormalize]

/-- Sanity check for the modeled source objects (arxiv-2602.11616v1, PDF pp.5,9,13). -/
example (n : ℕ) (g : EuclideanSpace ℂ (Qubits n)) :
    IsState (haarNormalize n g) := by
  by_cases h : g = 0
  · simp [haarNormalize, h, IsState, zeroKet, ket]
  · rw [haarNormalize, if_neg h]
    change ‖((‖g‖⁻¹ : ℝ) : ℂ) • g‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg g))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

end QAlgorithms.TwoBasisCertification


