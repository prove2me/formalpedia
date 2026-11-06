-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
-- name    : QEC_Semantics_Dynamics_Davies_Spectral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:51:22.169457+00:00
-- url     : https://prove2.me/theorems/a84a78a5-d322-4bcb-b614-eb60e2f9013b
-- title:
--   Spectral
-- statement:
--   Definitions and structural lemmas for Spectral, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def entry (b : OrthonormalBasis ι ℂ V) (A : Operator V) (i j : ι) : ℂ :=
  inner ℂ (b i) (A (b j))
@[simp] theorem entry_zero (b : OrthonormalBasis ι ℂ V) (i j : ι) :
    entry b 0 i j = 0 := by simp [entry]
@[simp] theorem entry_add (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A + B) i j = entry b A i j + entry b B i j := by simp [entry]
@[simp] theorem entry_sub (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A - B) i j = entry b A i j - entry b B i j := by simp [entry]
@[simp] theorem entry_smul (b : OrthonormalBasis ι ℂ V) (c : ℂ)
    (A : Operator V) (i j : ι) : entry b (c • A) i j = c * entry b A i j := by
  simp [entry]
@[simp] theorem entry_real_smul (b : OrthonormalBasis ι ℂ V) (c : ℝ)
    (A : Operator V) (i j : ι) : entry b (c • A) i j = (c : ℂ) * entry b A i j := by
  simp [entry]
@[simp] theorem entry_ite (b : OrthonormalBasis ι ℂ V) (p : Prop) [Decidable p]
    (A B : Operator V) (i j : ι) :
    entry b (if p then A else B) i j = if p then entry b A i j else entry b B i j := by
  split_ifs <;> rfl
@[simp] theorem entry_one (b : OrthonormalBasis ι ℂ V) (i j : ι) :
    entry b 1 i j = if i = j then 1 else 0 := by simp [entry, b.inner_eq_ite]
@[simp] theorem entry_sum {κ : Type*} (s : Finset κ) (b : OrthonormalBasis ι ℂ V)
    (A : κ → Operator V) (i j : ι) :
    entry b (∑ k ∈ s, A k) i j = ∑ k ∈ s, entry b (A k) i j := by
  simp [entry, LinearMap.sum_apply, inner_sum]
def matrixUnit (b : OrthonormalBasis ι ℂ V) (i j : ι) : Operator V :=
  (InnerProductSpace.rankOne ℂ (b i) (b j)).toLinearMap
@[simp] theorem entry_matrixUnit (b : OrthonormalBasis ι ℂ V) (i j k l : ι) :
    entry b (matrixUnit b i j) k l = if k = i ∧ j = l then 1 else 0 := by
  simp [entry, matrixUnit, InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  split_ifs <;> simp_all
def diagonal (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) : Operator V :=
  ∑ i, (energy i : ℂ) • matrixUnit b i i
@[simp] theorem entry_diagonal (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (i j : ι) :
    entry b (diagonal b energy) i j = if i = j then (energy i : ℂ) else 0 := by
  simp only [diagonal, entry_sum, entry_smul, entry_matrixUnit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [Ne.symm hki]
  · simp
def energyProjector (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E : ℝ) : Operator V :=
  ∑ i, if energy i = E then matrixUnit b i i else 0
@[simp] theorem entry_energyProjector (b : OrthonormalBasis ι ℂ V)
    (energy : ι → ℝ) (E : ℝ) (i j : ι) :
    entry b (energyProjector b energy E) i j =
      if i = j ∧ energy i = E then 1 else 0 := by
  simp only [energyProjector, entry_sum, entry_ite, entry_matrixUnit, entry_zero]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j <;> simp [hij]
  · intro k _ hki; simp [Ne.symm hki]
  · simp
def energyValues (energy : ι → ℝ) : Finset ℝ := Finset.univ.image energy
@[simp] theorem mem_energyValues (energy : ι → ℝ) (E : ℝ) :
    E ∈ energyValues energy ↔ ∃ i, energy i = E := by simp [energyValues]
def frequencies (energy : ι → ℝ) : Finset ℝ :=
  (Finset.univ : Finset (ι × ι)).image (fun ij => energy ij.2 - energy ij.1)
@[simp] theorem mem_frequencies (energy : ι → ℝ) (ω : ℝ) :
    ω ∈ frequencies energy ↔ ∃ i j, energy j - energy i = ω := by
  simp [frequencies]
theorem neg_mem_frequencies (energy : ι → ℝ) {ω : ℝ}
    (h : ω ∈ frequencies energy) : -ω ∈ frequencies energy := by
  obtain ⟨i,j,h⟩ := (mem_frequencies energy ω).mp h
  exact (mem_frequencies energy (-ω)).mpr ⟨j,i,by linarith⟩
abbrev Frequency (energy : ι → ℝ) := {ω // ω ∈ frequencies energy}
def negFrequency (energy : ι → ℝ) : Frequency energy ≃ Frequency energy where
  toFun ω := ⟨-ω.1, neg_mem_frequencies energy ω.2⟩
  invFun ω := ⟨-ω.1, neg_mem_frequencies energy ω.2⟩
  left_inv ω := by ext; simp
  right_inv ω := by ext; simp
def frequencyComponent (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) : Operator V :=
  ∑ i, ∑ j, if energy j - energy i = ω then entry b A i j • matrixUnit b i j else 0
def hamiltonianBasis (H : Operator V) (hH : H.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := hH.eigenvectorBasis rfl
def hamiltonianEnergies (H : Operator V) (hH : H.IsSymmetric) :
    Fin (Module.finrank ℂ V) → ℝ := hH.eigenvalues rfl
end
end QEC.Semantics.Davies


