-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/57dbb4a3-ca80-530f-a2d7-fc00737ac4c8

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain HeckeIntegralSeam FLT.SmoothVectors

noncomputable section

namespace IsotypicSpanForms

variable {F : Type} [Field F] [NumberField F]

section Cusp

theorem integrable_slice_cond {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (x : AdelicGL2 (𝓞 F) F) :
    @Integrable _ _ _ _ (adeleBorel (𝓞 F) F) (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x) := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop
    · have hinv : ∀ q : AdeleRing (𝓞 F) F, ((unipotentGL2 q)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F))
          = unipotentGL2 (-q) := fun q =>
        inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
      simp_rw [hinv]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
        fun_prop
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hIC : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) C
      (adelicAddHaar (𝓞 F) F) := hcont.continuousOn.integrableOn_compact hC
  have hIB : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := hIC.mono_set hsub
  unfold ProbabilityTheory.cond
  refine Integrable.smul_measure hIB ?_
  exact ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne'

theorem isCuspidalFn_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ)
    (hψ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 ψ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (φ + ψ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  have h2 := hψ g
  unfold constantTerm constantTermIntegrand at h1 h2 ⊢
  simp only [Pi.add_apply]
  rw [integral_add (integrable_slice_cond hφc g) (integrable_slice_cond hψc g), h1, h2, add_zero]

theorem isCuspidalFn_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (a • φ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  intro g
  have h1 := hφ g
  unfold constantTerm constantTermIntegrand at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h1, mul_zero]

end Cusp

section Smooth

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ hψ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  obtain ⟨V₂, hV₂o, hV₂⟩ := hψ
  refine ⟨V₁ ⊓ V₂, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hV₁o.inter hV₂o
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu1)
    have h2 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₂ u hu2)
    refine RightTranslationFn.ext fun y => ?_
    simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
      Pi.add_apply] at h1 h2 ⊢
    rw [h1 y, h2 y]

theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ) (hφ : IsKfSmooth F φ) :
    IsKfSmooth F (a • φ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  refine ⟨V₁, hV₁o, fun u hu => ?_⟩
  have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu)
  refine RightTranslationFn.ext fun y => ?_
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
    Pi.smul_apply] at h1 ⊢
  rw [h1 y]

end Smooth

section SmoothCuspClauses

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

abbrev pp : CarrierPins F := productionPinsOf F D U gen (adelicBox F)

theorem isSmoothCuspAutomorphicFnAt_add (ξ : (pp D U gen).Z →* ℂˣ)
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (φ + ψ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hψm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ ψ).mp hψ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (φ + ψ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, hφm.1.left_invariant γ g, hψm.1.left_invariant γ g]
    · simp only [Pi.add_apply, hφm.1.central_transform z g, hψm.1.central_transform z g, mul_add]
  have hL2 : MemLp (φ + ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := hφm.2.add hψm.2
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (φ + ψ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_add hφc hψc hφ.1.2 hψ.1.2
  · exact isKfSmooth_add hφ.2 hψ.2

theorem isSmoothCuspAutomorphicFnAt_smul (ξ : (pp D U gen).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (a • φ) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (a • φ) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, hφm.1.left_invariant γ g]
    · simp only [Pi.smul_apply, smul_eq_mul, hφm.1.central_transform z g]
      ring
  have hL2 : MemLp (a • φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
    have := hφm.2.const_mul a
    exact this
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (a • φ)).mpr ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_smul a hφ.1.2
  · exact isKfSmooth_smul a hφ.2

variable (ξ : (pp D U gen).Z →* ℂˣ) (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Φ : HeckeEigensystem F ℂ)

theorem isIsotypicCuspFormAt_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ)
    (hψ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ ψ) :
    IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ (φ + ψ) where
  smoothCusp := isSmoothCuspAutomorphicFnAt_add D U gen ξ hφ.continuous hψ.continuous
    hφ.smoothCusp hψ.smoothCusp
  continuous := hφ.continuous.add hψ.continuous
  level_invariant g u hu := by
    simp only [Pi.add_apply, hφ.level_invariant g u hu, hψ.level_invariant g u hu]
  hecke_eigen v hv := by
    obtain ⟨reps₁, hsys₁, h₁⟩ := hφ.hecke_eigen v hv
    obtain ⟨reps₂, hsys₂, h₂⟩ := hψ.hecke_eigen v hv
    refine ⟨reps₁, hsys₁, fun g => ?_⟩
    have h₁g := h₁ g
    have h₂g := h₂ g
    unfold SmoothCusp.heckeCosetSum at h₁g h₂g ⊢
    have hind : ∑ i, ψ (g * reps₁ i) = ∑ i, ψ (g * reps₂ i) :=
      HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys₂ hsys₁
        (fun g' u hu => hψ.level_invariant g' u hu) g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h₁g, hind, h₂g, mul_add]
  central_eigen v hv g := by
    simp only [Pi.add_apply, hφ.central_eigen v hv g, hψ.central_eigen v hv g, mul_add]

theorem isIsotypicCuspFormAt_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ) :
    IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ (a • φ) where
  smoothCusp := isSmoothCuspAutomorphicFnAt_smul D U gen ξ a hφ.smoothCusp
  continuous := hφ.continuous.const_smul a
  level_invariant g u hu := by
    simp only [Pi.smul_apply, hφ.level_invariant g u hu]
  hecke_eigen v hv := by
    obtain ⟨reps₁, hsys₁, h₁⟩ := hφ.hecke_eigen v hv
    refine ⟨reps₁, hsys₁, fun g => ?_⟩
    have h₁g := h₁ g
    unfold SmoothCusp.heckeCosetSum at h₁g ⊢
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [h₁g]
    ring
  central_eigen v hv g := by
    simp only [Pi.smul_apply, smul_eq_mul, hφ.central_eigen v hv g]
    ring

theorem eq_zero_or_isIsotypicCuspFormAt_of_mem {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule F (pp D U gen) ξ N S Φ) :
    φ = 0 ∨ IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ := by
  refine Submodule.span_induction (p := fun φ _ => φ = 0 ∨ IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ)
    ?_ ?_ ?_ ?_ hφ
  · exact fun φ h => Or.inr h
  · exact Or.inl rfl
  · intro φ ψ _ _ hφ hψ
    rcases hφ with rfl | hφ
    · simpa using hψ
    rcases hψ with rfl | hψ
    · simpa using Or.inr hφ
    exact Or.inr (isIsotypicCuspFormAt_add D U gen ξ N S Φ hφ hψ)
  · intro a φ _ hφ
    rcases hφ with rfl | hφ
    · exact Or.inl (smul_zero a)
    exact Or.inr (isIsotypicCuspFormAt_smul D U gen ξ N S Φ a hφ)

end SmoothCuspClauses

end IsotypicSpanForms

end

open IsotypicSpanForms in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ)
    (h0 : φ ≠ 0) :
    IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ φ := by
  rcases eq_zero_or_isIsotypicCuspFormAt_of_mem D U gen ξ N S Φ hφ with h | h
  · exact absurd h h0
  · exact h

end S_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule (solution)
