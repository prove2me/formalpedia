-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/70457c36-3501-5362-aa47-f1e222ceafa0

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicBox AutomorphicForm AutomorphicForm.CuspidalConstituent IsDedekindDomain

noncomputable section

namespace CuspSpan17

open MeasureTheory FLT.SmoothVectors NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem continuous_unipotentGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun x : A => (unipotentGL2 x : GL (Fin 2) A)) = fun x => !![(1 : A), x; 0, 1] :=
      funext fun x => unipotentGL2_coe x
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : A => (((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun x => !![(1 : A), -x; 0, 1] := funext fun x => rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem integrable_slice_cond_adelicBox {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hcont : Continuous (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) :=
    hφ.comp (continuous_unipotentGL2.mul continuous_const)
  have h1 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) C (adelicAddHaar (𝓞 F) F) :=
    hcont.continuousOn.integrableOn_compact hC
  have h2 : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := h1.mono_set hBC
  unfold ProbabilityTheory.cond
  exact h2.integrable.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

section Linear

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

local notation "PINS" => productionPinsOf F D U gen (adelicBox F)

variable (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ)

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) :=
  IsSmoothVector.add hφ hψ

theorem isKfSmooth_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) : IsKfSmooth F (c • φ) := by
  unfold IsKfSmooth at hφ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (RightTranslationFn.mk φ)) (fun h hh => ?_) hφ
  rw [MulAction.mem_stabilizer_iff] at hh ⊢
  refine RightTranslationFn.ext fun x => ?_
  have hx := congrArg (fun f => RightTranslationFn.toFun f x) hh
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at hx ⊢
  show c • φ (x * h) = c • φ x
  rw [hx]

theorem isSmoothCuspAutomorphicFnAt_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F PINS ξ φ) (hψ : IsSmoothCuspAutomorphicFnAt F PINS ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F PINS ξ (φ + ψ) := by
  obtain ⟨⟨hφa, hφcusp⟩, hφk⟩ := hφ
  obtain ⟨⟨hψa, hψcusp⟩, hψk⟩ := hψ
  refine ⟨⟨?_, ?_⟩, isKfSmooth_add F hφk hψk⟩
  ·
    unfold IsAutomorphicFnAt at hφa hψa ⊢
    rw [lsXiMemberAt_iff] at hφa hψa ⊢
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hφa.2.add hψa.2⟩
    · simp only [Pi.add_apply, hφa.1.left_invariant, hψa.1.left_invariant]
    · simp only [Pi.add_apply, hφa.1.central_transform, hψa.1.central_transform, mul_add]
  ·
    intro g
    have hi1 := integrable_slice_cond_adelicBox F hφc g
    have hi2 := integrable_slice_cond_adelicBox F hψc g
    have h1 := hφcusp g
    have h2 := hψcusp g
    unfold constantTerm constantTermIntegrand at h1 h2 ⊢
    rw [productionPinsOf_ν] at h1 h2 ⊢
    simp only [Pi.add_apply]
    have h1' : ∫ q : AdeleRing (𝓞 F) F, φ (unipotentGL2 q * g)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) = 0 := h1
    have h2' : ∫ q : AdeleRing (𝓞 F) F, ψ (unipotentGL2 q * g)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) = 0 := h2
    have hadd := integral_add hi1 hi2
    rw [h1', h2', add_zero] at hadd
    exact hadd

theorem isSmoothCuspAutomorphicFnAt_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsSmoothCuspAutomorphicFnAt F PINS ξ φ) :
    IsSmoothCuspAutomorphicFnAt F PINS ξ (c • φ) := by
  obtain ⟨⟨hφa, hφcusp⟩, hφk⟩ := hφ
  refine ⟨⟨?_, ?_⟩, isKfSmooth_smul F c hφk⟩
  · unfold IsAutomorphicFnAt at hφa ⊢
    rw [lsXiMemberAt_iff] at hφa ⊢
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hφa.2.const_smul c⟩
    · simp only [Pi.smul_apply, hφa.1.left_invariant]
    · simp only [Pi.smul_apply, hφa.1.central_transform, smul_eq_mul]; ring
  · intro g
    have h1 := hφcusp g
    unfold constantTerm constantTermIntegrand at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, h1, mul_zero]

theorem main (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ cuspKFiniteSubmodule F PINS ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F PINS ξ (rightTranslate F g x) := by
  refine Submodule.span_induction
    (p := fun φ _ => Continuous φ ∧ ∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F PINS ξ (rightTranslate F g φ))
    ?_ ?_ ?_ ?_ hx
  · intro φ hφ
    exact ⟨hφ.2.1, hφ.1⟩
  · refine ⟨continuous_const, fun g => ?_⟩
    rw [rightTranslate_zero]
    exact isSmoothCuspAutomorphicFnAt_zero F PINS ξ
  · intro u w _ _ hu hw
    refine ⟨hu.1.add hw.1, fun g => ?_⟩
    rw [rightTranslate_add]
    exact isSmoothCuspAutomorphicFnAt_add F D U gen ξ
      (hu.1.comp (continuous_id.mul continuous_const)) (hw.1.comp (continuous_id.mul continuous_const))
      (hu.2 g) (hw.2 g)
  · intro c u _ hu
    refine ⟨hu.1.const_smul c, fun g => ?_⟩
    rw [rightTranslate_smul]
    exact isSmoothCuspAutomorphicFnAt_smul F D U gen ξ c (hu.2 g)

end Linear

end CuspSpan17

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ cuspKFiniteSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ (rightTranslate K g x) :=
  CuspSpan17.main K D U gen ξ x hx

end S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule (solution)
