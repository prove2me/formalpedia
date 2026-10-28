-- Prove2me | solution 1 for ADH2015.twoQubit_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:22:47.01385+00:00
-- url     : https://prove2.me/submissions/e5b2bbb3-57d1-495f-b69c-786106064e6f

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker
open ADH2015

lemma adh2q_hc : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma adh2q_LX_phi : ADH2015.logicalX *ᵥ ADH2015.phiPlus = ADH2015.psiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.logicalX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals first
    | linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc
    | linear_combination (-2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc

lemma adh2q_LX_psi : ADH2015.logicalX *ᵥ ADH2015.psiPlus = ADH2015.phiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.logicalX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals first
    | linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc
    | linear_combination (-2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc

lemma adh2q_LZ_phi : ADH2015.logicalZ *ᵥ ADH2015.phiPlus = ADH2015.phiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.logicalZ, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals first
    | linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc
    | linear_combination (-2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc

lemma adh2q_LZ_psi : ADH2015.logicalZ *ᵥ ADH2015.psiPlus = -ADH2015.psiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.logicalZ, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals first
    | linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc
    | linear_combination (-2 * (Real.sqrt 2 : ℂ)⁻¹) * adh2q_hc

lemma adh2q_XI_phi : (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ADH2015.phiPlus =
    ADH2015.psiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.pauliX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply]

lemma adh2q_XI_psi : (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ADH2015.psiPlus =
    ADH2015.phiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.pauliX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply]

lemma adh2q_IX_phi : ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX) *ᵥ ADH2015.phiPlus =
    ADH2015.psiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.pauliX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply]

lemma adh2q_IX_psi : ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX) *ᵥ ADH2015.psiPlus =
    ADH2015.phiPlus := by
  funext p
  fin_cases p <;> simp [mulVec, dotProduct, ADH2015.pauliX, ADH2015.phiPlus, ADH2015.psiPlus,
    Fintype.sum_prod_type, Fin.sum_univ_two, one_apply]

lemma adh2q_XI_herm : (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ =
    ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [ADH2015.pauliX, one_apply]

lemma adh2q_IX_herm : ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX)ᴴ =
    (1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [ADH2015.pauliX, one_apply]

lemma adh2q_LX_herm : ADH2015.logicalXᴴ = ADH2015.logicalX := by
  ext p q
  simp [ADH2015.logicalX, conjTranspose_apply]; ring

lemma adh2q_LZ_herm : ADH2015.logicalZᴴ = ADH2015.logicalZ := by
  ext p q
  simp [ADH2015.logicalZ, conjTranspose_apply]; ring

lemma adh2q_mem {v : Qubit × Qubit → ℂ} (hv : v ∈ ADH2015.twoQubitCode) :
    ∃ α β : ℂ, v = α • ADH2015.phiPlus + β • ADH2015.psiPlus := by
  obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.1 hv
  exact ⟨α, β, h.symm⟩

lemma adh2q_phi_mem : ADH2015.phiPlus ∈ ADH2015.twoQubitCode :=
  Submodule.subset_span (by simp)

lemma adh2q_psi_mem : ADH2015.psiPlus ∈ ADH2015.twoQubitCode :=
  Submodule.subset_span (by simp)

lemma adh2q_comb_mem (α β : ℂ) :
    α • ADH2015.phiPlus + β • ADH2015.psiPlus ∈ ADH2015.twoQubitCode :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ adh2q_phi_mem)
    (Submodule.smul_mem _ _ adh2q_psi_mem)

lemma adh2q_mem_symm {w : Qubit × Qubit → ℂ} (hw : w ∈ ADH2015.twoQubitCode) :
    w (0, 0) = w (1, 1) ∧ w (0, 1) = w (1, 0) := by
  obtain ⟨α, β, rfl⟩ := adh2q_mem hw
  simp [ADH2015.phiPlus, ADH2015.psiPlus]

lemma adh2q_acts_of (O : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (h1 : O *ᵥ ADH2015.phiPlus ∈ ADH2015.twoQubitCode)
    (h2 : O *ᵥ ADH2015.psiPlus ∈ ADH2015.twoQubitCode) :
    ∀ v ∈ ADH2015.twoQubitCode, O *ᵥ v ∈ ADH2015.twoQubitCode := by
  intro v hv
  obtain ⟨α, β, rfl⟩ := adh2q_mem hv
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem solution :
    ADH2015.ActsWithin ADH2015.twoQubitCode ADH2015.logicalX ∧
    ADH2015.ActsWithin ADH2015.twoQubitCode ADH2015.logicalZ ∧
    (∀ v ∈ ADH2015.twoQubitCode,
      (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ v = ADH2015.logicalX *ᵥ v ∧
      (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ *ᵥ v = ADH2015.logicalXᴴ *ᵥ v) ∧
    (¬ ∃ M : Matrix Qubit Qubit ℂ, ∀ v ∈ ADH2015.twoQubitCode,
      (M ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ v = ADH2015.logicalZ *ᵥ v) ∧
    (∀ O : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ, ADH2015.ActsWithin ADH2015.twoQubitCode O →
      ADH2015.HasRepOnE ADH2015.twoQubitCode O →
      ∃ a b : ℂ, ∀ v ∈ ADH2015.twoQubitCode, O *ᵥ v = a • v + b • (ADH2015.logicalX *ᵥ v)) ∧
    (∀ v ∈ ADH2015.twoQubitCode,
      ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX) *ᵥ v = ADH2015.logicalX *ᵥ v ∧
      ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX)ᴴ *ᵥ v = ADH2015.logicalXᴴ *ᵥ v) := by
  have hXI : ∀ v ∈ ADH2015.twoQubitCode,
      (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ v = ADH2015.logicalX *ᵥ v := by
    intro v hv
    obtain ⟨α, β, rfl⟩ := adh2q_mem hv
    simp only [mulVec_add, mulVec_smul, adh2q_XI_phi, adh2q_XI_psi, adh2q_LX_phi, adh2q_LX_psi]
  have hIX : ∀ v ∈ ADH2015.twoQubitCode,
      ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ ADH2015.pauliX) *ᵥ v = ADH2015.logicalX *ᵥ v := by
    intro v hv
    obtain ⟨α, β, rfl⟩ := adh2q_mem hv
    simp only [mulVec_add, mulVec_smul, adh2q_IX_phi, adh2q_IX_psi, adh2q_LX_phi, adh2q_LX_psi]
  have hLXin := adh2q_acts_of ADH2015.logicalX
    (by rw [adh2q_LX_phi]; exact adh2q_psi_mem) (by rw [adh2q_LX_psi]; exact adh2q_phi_mem)
  have hLZin := adh2q_acts_of ADH2015.logicalZ
    (by rw [adh2q_LZ_phi]; exact adh2q_phi_mem)
    (by rw [adh2q_LZ_psi]; exact Submodule.neg_mem _ adh2q_psi_mem)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨hLXin v hv, by rw [adh2q_LX_herm]; exact hLXin v hv⟩
  · intro v hv
    exact ⟨hLZin v hv, by rw [adh2q_LZ_herm]; exact hLZin v hv⟩
  · intro v hv
    exact ⟨hXI v hv, by rw [adh2q_XI_herm, adh2q_LX_herm]; exact hXI v hv⟩
  · rintro ⟨M, hM⟩
    have h1 := congrFun (hM _ adh2q_phi_mem) (0, 0)
    have h2 := congrFun (hM _ adh2q_psi_mem) (0, 1)
    rw [adh2q_LZ_phi] at h1
    rw [adh2q_LZ_psi] at h2
    simp [mulVec, dotProduct, ADH2015.phiPlus, ADH2015.psiPlus,
      Fintype.sum_prod_type, Fin.sum_univ_two, one_apply] at h1 h2
    have : (Real.sqrt 2 : ℂ)⁻¹ = 0 := by linear_combination (-(Real.sqrt 2 : ℂ)⁻¹ / 2) * h1 + h2 / 2
    simp at this
  · intro O hO ⟨X, hX⟩
    have hp := adh2q_mem_symm (hO _ adh2q_phi_mem).1
    rw [← (hX _ adh2q_phi_mem).1] at hp
    simp [mulVec, dotProduct, ADH2015.phiPlus,
      Fintype.sum_prod_type, Fin.sum_univ_two, one_apply] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hK : X ⊗ₖ (1 : Matrix Qubit Qubit ℂ) =
        X 0 0 • 1 + X 0 1 • (ADH2015.pauliX ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [ADH2015.pauliX, one_apply, hp1, hp2]
    refine ⟨X 0 0, X 0 1, fun v hv => ?_⟩
    rw [← (hX v hv).1, hK, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hXI v hv]
  · intro v hv
    exact ⟨hIX v hv, by rw [adh2q_IX_herm, adh2q_LX_herm]; exact hIX v hv⟩
