-- Prove2me | Definitions.Def_QAlgorithms_Defs_DirectFidelityEstimation
-- name    : QAlgorithms_Defs_DirectFidelityEstimation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:28.215979+00:00
-- url     : https://prove2.me/theorems/a28a6112-6510-43d2-90bd-ffa6b0edac24
-- title:
--   DirectFidelityEstimation
-- statement:
--   DirectFidelityEstimation
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DirectFidelityEstimation.lean

import Definitions.Def_QAlgorithms_Defs_DirectFidelitySampling
noncomputable section

namespace QAlgorithms.DirectFidelity

variable {n m d k b w M K N c out : ℕ}

/-- Ideal ratio on nonzero support (1104.4695 p.2 Eq.(4)).
This is an analysis quantity, not an oracle for the lab's exact expectation. -/
def idealRatio (rho sigma : Matrix (Qubits n) (Qubits n) ℂ)
    (k : characteristicSupport rho) : ℝ :=
  pauliCharacteristic sigma k.val / pauliCharacteristic rho k.val

/-- Independent setting count, 1104.4695 p.2 preceding Eq.(5).
Inputs are the nontrivial accuracy and confidence domain. -/
def settingCount (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) : ℕ :=
  ⌈1 / (eps ^ 2 * delta)⌉₊

/-- Ideal mean of the actual sampled settings (1104.4695 p.2 Eq.(5)). -/
def idealMean (rho sigma : Matrix (Qubits n) (Qubits n) ℂ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (settings : Fin (settingCount eps delta heps hdelta) → characteristicSupport rho) : ℝ :=
  (settingCount eps delta heps hdelta : ℝ)⁻¹ * ∑ i, idealRatio rho sigma (settings i)

/-- Whole-expression ceiling of the target-dependent repetition count,
1104.4695 p.2 Eq.(6). The nonzero-support subtype guards the coefficient. -/
def repetitions (rho : Matrix (Qubits n) (Qubits n) ℂ) (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) (k : characteristicSupport rho) : ℕ :=
  ⌈2 * Real.log (2 / delta) / ((2 : ℝ) ^ n * pauliCharacteristic rho k.val ^ 2 *
    settingCount eps delta heps hdelta * eps ^ 2)⌉₊

/-- A finite dependent experiment retains each sampled setting and its own
number of fresh single-copy outcomes (1104.4695 p.2 Eqs.(6)–(8)). -/
abbrev Experiment (rho : Matrix (Qubits n) (Qubits n) ℂ) (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) :=
  (settings : Fin (settingCount eps delta heps hdelta) → characteristicSupport rho) ×
    ((i : Fin (settingCount eps delta heps hdelta)) →
      Fin (repetitions rho eps delta heps hdelta (settings i)) → Bool)

/-- Product of target-only setting weights and conditional single-copy Born
weights, 1104.4695 p.2. This constructs independence and uses no lab oracle. -/
def experimentLaw (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (sigma : Matrix (Qubits n) (Qubits n) ℂ) (hsigma : IsDensityMatrix sigma)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1) :
    Experiment (pureDensity psi) eps delta heps hdelta → ℝ :=
  fun e => (∏ i, (importanceLaw psi hpsi (e.1 i)).toReal) *
    ∏ i, ∏ j, (pauliMeasurementLaw sigma hsigma (e.1 i).val (e.2 i j)).toReal

/-- Finite-copy setting estimate, 1104.4695 p.2 Eq.(7). -/
def settingEstimate (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (k : characteristicSupport rho) (outcomes : Fin (repetitions rho eps delta heps hdelta k) → Bool) :
    ℝ :=
  (∑ j, if outcomes j then (1 : ℝ) else -1) /
    (repetitions rho eps delta heps hdelta k *
      Real.sqrt ((2 : ℝ) ^ n) * pauliCharacteristic rho k.val)

/-- Returned estimate from the actual dependent experiment
(1104.4695 p.2 preceding Eq.(8)). Values are not clipped. -/
def estimate (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (e : Experiment rho eps delta heps hdelta) : ℝ :=
  (settingCount eps delta heps hdelta : ℝ)⁻¹ *
    ∑ i, settingEstimate rho eps delta heps hdelta (e.1 i) (e.2 i)

/-- Copies actually consumed by the sampled settings,
1104.4695 p.2 Eqs.(9)–(10). -/
def copyCount (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (settings : Fin (settingCount eps delta heps hdelta) → characteristicSupport rho) : ℕ :=
  ∑ i, repetitions rho eps delta heps hdelta (settings i)

/-- Sanity check for the modeled source objects (arxiv-1104.4695v3, PDF pp.2). -/
example : settingCount 1 1 (by norm_num) ⟨by norm_num, le_rfl⟩ = 1 := by
  norm_num [settingCount]

/-- Sanity check for the modeled source objects (arxiv-1104.4695v3, PDF pp.2). -/
example (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
    (k : characteristicSupport rho) :
    pauliCharacteristic rho k.val ≠ 0 := (Finset.mem_filter.mp k.property).2

end QAlgorithms.DirectFidelity


