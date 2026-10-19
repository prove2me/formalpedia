-- Prove2me | Definitions.Def_QAlgorithms_Defs_RobustShadowRetrieval
-- name    : QAlgorithms_Defs_RobustShadowRetrieval
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:24:21.815588+00:00
-- url     : https://prove2.me/theorems/9bd18b7a-3555-474c-a735-0b9aee69b4b3
-- title:
--   RobustShadowRetrieval
-- statement:
--   RobustShadowRetrieval
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RobustShadowRetrieval.lean

import Definitions.Def_QAlgorithms_Defs_RobustShadowCalibration
noncomputable section

open scoped Matrix

namespace QAlgorithms.RobustShadow

/-- Total identity/traceless decoder of Protocol 1, with singular a=0 retained as
failed calibration data (2011.09636 p.19; p.21). This map need not be CP. -/
def estimatedInverse {n : ℕ} (a : ℝ) (X : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (X.trace/((2 : ℂ)^n)) • 1+(a⁻¹ : ℂ) • (X-(X.trace/((2 : ℂ)^n)) • 1)

/-- Proof-derived real scale and the two independently rounded batch factors
(2011.09636 p.22, Eqs.(B19)-(B27)). No equality with the ceiling of the real
scale is asserted for the product of these separately rounded factors. -/
structure CalibrationSchedule where
  printedScale : ℝ
  batches : ℕ
  batchSize : ℕ

/-- Construct the schedule from gamma=eps*abs(f)/(1+eps) in the source proof
(2011.09636 p.22, Eqs.(B19)-(B27)). B24/B27 print 1+eps²; the substitution
requires (1+eps)². Nonzero f, of either sign, is the necessary informative
domain; the singular F_Z=1/d channel is excluded. -/
def sampleSchedule {n : ℕ} (_hn : 0 < n)
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (eps delta : ℝ) (_domain : 0 < eps ∧ 0 < delta ∧ delta ≤ 1 ∧
      zFidelity Lambda lawful ≠ ((2 : ℝ)^n)⁻¹) : CalibrationSchedule :=
  let d := (2 : ℝ)^n
  let A := (1+eps)^2*(1+d⁻¹)^2/(eps^2*(zFidelity Lambda lawful-d⁻¹)^2)
  ⟨136*Real.log (2/delta)*A,⌈2*Real.log (2/delta)⌉₊,⌈68*A⌉₊⟩

/-- Actual preparation/measurement count N*K, rather than ceil(printedScale)
(2011.09636 p.18, Protocol 1; p.22, Eq.(B24)). -/
def CalibrationSchedule.probes (S : CalibrationSchedule) : ℕ := S.batchSize*S.batches

example {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ) : estimatedInverse 1 X = X := by
  simp only [estimatedInverse,inv_one,Complex.ofReal_one,one_smul]
  abel

example {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ) :
    estimatedInverse 0 X = (X.trace/((2 : ℂ)^n)) • 1 := by simp [estimatedInverse]

example : CalibrationSchedule.probes ⟨0,2,3⟩ = 6 := rfl


/-- Finite conditional mean of later predictions under a fresh noisy shot, given
the recorded calibration value a; a=0 remains a failing calibration value
(2011.09636 pp.19,21-22). -/
def retrievalExpectation {n : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (density : IsDensityMatrix rho)
    (O : Matrix (Qubits n) (Qubits n) ℂ) (a : ℝ) : ℝ :=
  ∑ Ub : Clifford.ProjectiveGroup n × Qubits n,
    shotLaw Lambda lawful rho density Ub *
      (O * estimatedInverse a
        (conjSuperop (star ((Clifford.representative Ub.1).val : Matrix _ _ ℂ))
          (pureDensity (ket Ub.2)))).trace.re

/-- One calibration event controlling the conditional bias for every density matrix
and Hermitian observable simultaneously. Scalar identity is removed only in the
error scale, not from the prediction. A zero median fails this event
(2011.09636 pp.19,21-23). -/
def uniformBiasEvent {n N K : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (hn : 0 < n) (hN : 0 < N) (hK : 0 < K)
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (eps : ℝ) (_heps : 0 < eps)
    (record : Fin K × Fin N → Clifford.ProjectiveGroup n × Qubits n) : Prop :=
  let a := calibrationEstimate hn hN hK
    (fun i => (Clifford.representative (record i).1,(record i).2))
  a ≠ 0 ∧ ∀ rho : Matrix (Qubits n) (Qubits n) ℂ, ∀ density : IsDensityMatrix rho,
    ∀ O : Matrix (Qubits n) (Qubits n) ℂ, O.IsHermitian →
      |retrievalExpectation Lambda lawful rho density O a - (O*rho).trace.re| ≤
        eps * specNorm (O-(O.trace/((2 : ℂ)^n)) • 1)

example {n : ℕ} [Fintype (Clifford.ProjectiveGroup n)]
    (Lambda : Superop (Qubits n) (Qubits n)) (lawful : IsChannel Lambda)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (density : IsDensityMatrix rho) (a : ℝ) :
    retrievalExpectation Lambda lawful rho density 0 a = 0 := by
  simp [retrievalExpectation]

end QAlgorithms.RobustShadow


