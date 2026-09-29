-- Prove2me | solution 1 for AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ba0b5f83-4ebf-542d-b9f4-6445678d3ff7

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicBox NumberField.AdelicFourier
open scoped SchwartzMap Classical

noncomputable section

namespace M4aP3B
namespace Rows
namespace SliceTensor

section Generic

variable {A : Type*} [CommRing A]

theorem mul_unipotent_mul_apply (M₁ M₂ : Matrix (Fin 2) (Fin 2) A) (τ : A) (i j : Fin 2) :
    (M₁ * !![1, τ; 0, 1] * M₂) i j = (M₁ * M₂) i j + M₁ i 0 * τ * M₂ 1 j := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) A) (τ : A) :
    ((G₁ * unipotentGL2 τ * G₂ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = (G₁ : Matrix (Fin 2) (Fin 2) A) * !![1, τ; 0, 1] * (G₂ : Matrix (Fin 2) (Fin 2) A) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe]

theorem retract_apply (G₁ G₂ : GL (Fin 2) A) (τ : A) :
    ((G₁⁻¹ * (G₁ * unipotentGL2 τ * G₂) * G₂⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = τ := by
  have h : G₁⁻¹ * (G₁ * unipotentGL2 τ * G₂) * G₂⁻¹ = unipotentGL2 τ := by group
  rw [h, unipotentGL2_coe]
  rfl

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : A → GL (Fin 2) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun τ : A => ((unipotentGL2 τ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun τ : A => (((unipotentGL2 τ)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    have h : (fun τ : A => (((unipotentGL2 τ)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))
        = fun τ => !![1, -τ; 0, 1] := rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) A) :
    Continuous fun τ : A => G₁ * unipotentGL2 τ * G₂ :=
  (continuous_const.mul continuous_unipotentGL2).mul continuous_const

theorem continuous_retract (G₁ G₂ : GL (Fin 2) A) :
    Continuous fun M : GL (Fin 2) A => ((G₁⁻¹ * M * G₂⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 :=
  (Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem 0 1

theorem hasCompactSupport_comp_mul_unipotentGL2_mul [T2Space A] {φ : GL (Fin 2) A → ℂ}
    (hφ : HasCompactSupport φ) (G₁ G₂ : GL (Fin 2) A) :
    HasCompactSupport fun τ : A => φ (G₁ * unipotentGL2 τ * G₂) := by
  refine HasCompactSupport.intro
    ((hφ.isCompact).image (continuous_retract G₁ G₂)) fun τ hτ => ?_
  by_contra hne
  refine hτ ⟨G₁ * unipotentGL2 τ * G₂, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
  exact retract_apply G₁ G₂ τ

end Generic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "e" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem glArch_unipotentGL2 (s : 𝔸) :
    AdelicLevel.glArch (𝓞 F) F (unipotentGL2 s) = unipotentGL2 s.1 := by
  apply Units.ext
  ext i j
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2 (s : 𝔸) :
    AdelicLevel.glFin (𝓞 F) F (unipotentGL2 s) = unipotentGL2 s.2 := by
  apply Units.ext
  ext i j
  rw [AdelicLevel.glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] in

theorem archEntries_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F))
    (σ : mixedEmbedding.mixedSpace F) :
    archEntries F (G₁ * unipotentGL2 ((e).symm σ) * G₂)
      = fun i j => e (((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
            * (G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) i j)
          + e ((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i 0) * σ
            * e ((G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 j) := by
  funext i j
  rw [archEntries_apply, coe_mul_unipotentGL2_mul, mul_unipotent_mul_apply, map_add, map_mul, map_mul,
    RingEquiv.apply_symm_apply]

theorem contDiff_archFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) :
    ContDiff ℝ (⊤ : ℕ∞) fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : (fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂))
      = Φ ∘ fun σ => fun i j => e (((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
            * (G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) i j)
          + e ((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i 0) * σ
            * e ((G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 j) := by
    funext σ
    rw [hfaΦ, archEntries_mul_unipotentGL2_mul]
    rfl
  rw [h]
  refine hΦ.comp ?_
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul contDiff_const)

theorem hasCompactSupport_archFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) :
    HasCompactSupport fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := by

  have h1 : HasCompactSupport fun τ : InfiniteAdeleRing F => fa (G₁ * unipotentGL2 τ * G₂) :=
    hasCompactSupport_comp_mul_unipotentGL2_mul hfa.2 G₁ G₂
  refine HasCompactSupport.intro ((h1.isCompact).image (continuous_ringEquiv_mixedSpace F)) fun σ hσ => ?_
  by_contra hne
  refine hσ ⟨(e).symm σ, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
  exact RingEquiv.apply_symm_apply _ _

def archFactorSchwartz {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) : 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  (hasCompactSupport_archFactor F hfa G₁ G₂).toSchwartzMap (contDiff_archFactor F hfa G₁ G₂)

theorem archFactorSchwartz_apply {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) (σ : mixedEmbedding.mixedSpace F) :
    archFactorSchwartz F hfa G₁ G₂ σ = fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := rfl

theorem isLocallyConstant_finFactor {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hff : IsFinTestFactor F ff) (G₁ G₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    IsLocallyConstant fun τ : FiniteAdeleRing (𝓞 F) F => ff (G₁ * unipotentGL2 τ * G₂) :=
  hff.1.comp_continuous (continuous_mul_unipotentGL2_mul G₁ G₂)

theorem hasCompactSupport_finFactor {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hff : IsFinTestFactor F ff) (G₁ G₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    HasCompactSupport fun τ : FiniteAdeleRing (𝓞 F) F => ff (G₁ * unipotentGL2 τ * G₂) :=
  hasCompactSupport_comp_mul_unipotentGL2_mul hff.2 G₁ G₂

theorem comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl (F : Type) [Field F] [NumberField F]
    {f : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn F f)
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
    (fun s => f (g₁ * AutomorphicForm.unipotentGL2 s * g₂)) ∈ NumberField.AdelicFourier.pureTensorSet F := by
  classical
  obtain ⟨fa, ff, hfa, hff, hprod⟩ := hf
  refine ⟨archFactorSchwartz F hfa (AdelicLevel.glArch (𝓞 F) F g₁) (AdelicLevel.glArch (𝓞 F) F g₂),
    fun τ => ff (AdelicLevel.glFin (𝓞 F) F g₁ * unipotentGL2 τ * AdelicLevel.glFin (𝓞 F) F g₂),
    isLocallyConstant_finFactor F hff _ _, hasCompactSupport_finFactor F hff _ _, ?_⟩
  funext s
  rw [hprod, map_mul, map_mul, map_mul, map_mul, glArch_unipotentGL2, glFin_unipotentGL2,
    archFactorSchwartz_apply, RingEquiv.symm_apply_apply]

theorem gate_unipotentGL2_one_ne_one : (unipotentGL2 (1 : F) : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h01 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [unipotentGL2_coe] at h01

theorem gate_zero (g₁ g₂ : GL (Fin 2) 𝔸) :
    (fun s : 𝔸 => (fun _ : GL (Fin 2) 𝔸 => (0 : ℂ)) (g₁ * unipotentGL2 s * g₂)) ∈ pureTensorSet F :=
  zero_mem_pureTensorSet

end M4aP3B.Rows.SliceTensor

end

#print axioms M4aP3B.Rows.SliceTensor.comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl
#print axioms M4aP3B.Rows.SliceTensor.gate_unipotentGL2_one_ne_one

theorem solution
    (F : Type) [Field F] [NumberField F]
    {f : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn F f)
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
    (fun s => f (g₁ * AutomorphicForm.unipotentGL2 s * g₂)) ∈ NumberField.AdelicFourier.pureTensorSet F := by
  first
    | exact M4aP3B.Rows.SliceTensor.comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl F hf g₁ g₂
    | (apply M4aP3B.Rows.SliceTensor.comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl <;> assumption)

end S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet
end P2MW
export P2MW.S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet (solution)
