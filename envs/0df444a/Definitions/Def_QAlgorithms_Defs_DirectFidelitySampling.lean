-- Prove2me | Definitions.Def_QAlgorithms_Defs_DirectFidelitySampling
-- name    : QAlgorithms_Defs_DirectFidelitySampling
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:15:09.279456+00:00
-- url     : https://prove2.me/theorems/44a0bb7c-adc7-4051-9c41-ca85d8023ac9
-- title:
--   DirectFidelitySampling
-- statement:
--   DirectFidelitySampling
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DirectFidelitySampling.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ENNReal

namespace QAlgorithms.DirectFidelity

variable {n m d k b w M K N c out : ℕ}

/-- Pauli characteristic function with sqrt(2^n) normalization,
1104.4695 p.1 Eq.(2); labels are phase-free Pauli strings. -/
def pauliCharacteristic (tau : Matrix (Qubits n) (Qubits n) ℂ)
    (k : Fin n → Stabilizer.Pauli) : ℝ :=
  (tau * pauliOps k).trace.re / Real.sqrt ((2 : ℝ) ^ n)

/-- Nonzero target coefficients, 1104.4695 p.2 Eqs.(3)–(4).
Ratios and repetition counts use this finite subtype. -/
def characteristicSupport (rho : Matrix (Qubits n) (Qubits n) ℂ) :
    Finset (Fin n → Stabilizer.Pauli) :=
  Finset.univ.filter fun k => pauliCharacteristic rho k ≠ 0

/-- Identity phase-free Pauli, 1104.4695 pp.1–2.
It ensures nonempty characteristic support for every normalized target. -/
theorem identityPauli_matrix (n : ℕ) :
    pauliOps (fun _ : Fin n => Stabilizer.Pauli.I) = 1 := by
  ext y z
  simp [pauliOps,Stabilizer.PauliString.toMatrix,Stabilizer.Pauli.mat,
    Matrix.one_apply,Finset.prod_boole,funext_iff]

/-- Trace-one consequence of target normalization, 1104.4695 p.1. -/
theorem pureTrace_real {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi) :
    (pureDensity psi).trace.re = 1 := by
  have hc : ∀ z, (psi z * star (psi z)).re = ‖psi z‖^2 := by
    intro z
    change (psi z * (starRingEnd ℂ) (psi z)).re = ‖psi z‖^2
    rw [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  simp only [pureDensity,Matrix.trace,Matrix.diag,Matrix.of_apply,Complex.re_sum]
  change (∑ z, (psi z * star (psi z)).re) = 1
  simp only [hc]
  rw [← EuclideanSpace.norm_sq_eq,hpsi]
  norm_num

/-- Target-only importance PMF, 1104.4695 p.2 Eq.(3).
Its weights are normalized from the actual characteristic coefficients,
with no additional target hypothesis. Eq.(2) with sigma=rho and target
purity gives sum chi^2=1, so this normalization leaves the source weights
unchanged. The identity coefficient proves strictly positive total mass. -/
def importanceLaw {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi) :
    PMF (characteristicSupport (pureDensity psi)) := by
  classical
  let idLabel := fun _ : Fin n => Stabilizer.Pauli.I
  have hchar : pauliCharacteristic (pureDensity psi) idLabel =
      (Real.sqrt ((2:ℝ)^n))⁻¹ := by
    rw [pauliCharacteristic,identityPauli_matrix,mul_one,pureTrace_real psi hpsi,one_div]
  have hne : pauliCharacteristic (pureDensity psi) idLabel ≠ 0 := by
    rw [hchar]
    exact inv_ne_zero (Real.sqrt_pos.mpr (pow_pos (by norm_num) n)).ne'
  let idMember : characteristicSupport (pureDensity psi) :=
    ⟨idLabel,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩⟩
  let weights : characteristicSupport (pureDensity psi) → ℝ≥0∞ :=
    fun j => ENNReal.ofReal (pauliCharacteristic (pureDensity psi) j.val ^ 2)
  have htotal : ∑' j, weights j ≠ 0 := by
    rw [tsum_fintype]
    apply ne_of_gt
    have hp : 0 < weights idMember := ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hne)
    exact lt_of_lt_of_le hp
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ idMember))
  have hfinite : ∑' j, weights j ≠ ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  exact PMF.normalize weights htotal hfinite

/-- Single-copy Pauli Born PMF, 1104.4695 pp.1–2.
true denotes +1 and false denotes -1. Density normalization and the
Pauli spectrum ensure both source weights (1+-Tr(sigma W))/2 are
nonnegative and sum to one. No clipped probability or assumed mean
is supplied by the input. -/
def pauliMeasurementLaw {n : ℕ} (sigma : Matrix (Qubits n) (Qubits n) ℂ)
    (hsigma : IsDensityMatrix sigma) (k : Fin n → Stabilizer.Pauli) : PMF Bool := by
  let e := (sigma * pauliOps k).trace.re
  let weights : Bool → ℝ≥0∞ :=
    fun b => ENNReal.ofReal ((1 + (if b then 1 else -1)*e)/2)
  have hpositive : 0 < ∑ b, weights b := by
    by_cases he : 0 ≤ e
    · have hp : 0 < weights true := by
        apply ENNReal.ofReal_pos.mpr
        simp only [ite_true,one_mul]
        linarith
      exact hp.trans_le (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ true))
    · have hp : 0 < weights false := by
        apply ENNReal.ofReal_pos.mpr
        simp only [Bool.false_eq_true,ite_false,neg_one_mul]
        linarith
      exact hp.trans_le (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ false))
  have htotal : ∑' b, weights b ≠ 0 := by rw [tsum_fintype]; exact hpositive.ne'
  have hfinite : ∑' b, weights b ≠ ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
  exact PMF.normalize weights htotal hfinite

/-- Sanity check for the modeled source objects (arxiv-1104.4695v3, PDF pp.1,2,4). -/
example (sigma : Matrix (Qubits n) (Qubits n) ℂ)
    (hsigma : IsDensityMatrix sigma) (k : Fin n → Stabilizer.Pauli) :
    ∑ b, pauliMeasurementLaw sigma hsigma k b = 1 := by
  simpa only [tsum_fintype] using (pauliMeasurementLaw sigma hsigma k).tsum_coe

/-- Sanity check for the modeled source objects (arxiv-1104.4695v3, PDF pp.1,2,4). -/
example (sigma : Matrix (Qubits n) (Qubits n) ℂ) (hsigma : IsDensityMatrix sigma) :
    pauliMeasurementLaw sigma hsigma (fun _ => Stabilizer.Pauli.I) true = 1 := by
  simp [pauliMeasurementLaw,identityPauli_matrix,hsigma.2,PMF.normalize_apply,
    tsum_fintype,Fintype.sum_bool]

/-- Sanity check for the modeled source objects (arxiv-1104.4695v3, PDF pp.1,2,4). -/
example (k : Fin 0 → Stabilizer.Pauli) :
    pauliCharacteristic (1 : Matrix (Qubits 0) (Qubits 0) ℂ) k = 1 := by
  simp [pauliCharacteristic, pauliOps, Stabilizer.PauliString.toMatrix,
    Matrix.trace, Matrix.mul_apply]

end QAlgorithms.DirectFidelity


