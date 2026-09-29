-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module_and_exists_presentation_isFrameOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/89dade43-366f-54af-8850-01a62c57d2d8

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn.AlgebraicGeometry"

open CategoryTheory.Limits

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Hom Scheme.Modules.Hom IsIntegral Scheme germ_injective_of_isIntegral Scheme.Modules Scheme.Hom.ker_apply Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.IsFrameOn"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul forget germToFunctionField ringCatSheaf Hom mk Γ empty Modules.Hom functionField affineOpens isBasis_affineOpens Modules Hom.ker_apply Opens PresheafOfModules IdealSheafData evaluation Modules.IsInvertible Modules.IsFrameOn"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "mk map subscheme ker_subschemeι ideal map_comp inclusion subschemeι map_ideal IsInvertible module moduleι"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (I : X.IdealSheafData)

noncomputable abbrev evalAt (U : X.Opens) :
    SheafOfModules X.ringCatSheaf ⥤ ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op U)) :=
  SheafOfModules.forget X.ringCatSheaf ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op U)

private noncomputable abbrev _root_.AlgebraicGeometry.Scheme.IdealSheafData.res : SheafOfModules.unit X.ringCatSheaf ⟶
    (SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  I.subschemeι.unitToPushforwardUnit

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "res"

noncomputable def isLimitMapKernelFork (U : X.Opens) :
    IsLimit ((KernelFork.ofι (kernel.ι I.res) (kernel.condition I.res)).map (evalAt U)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel I.res) (evalAt U)

theorem exact_and_mono (U : X.Opens) :
    (ShortComplex.mk ((evalAt U).map (kernel.ι I.res)) ((evalAt U).map I.res)
        (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])).Exact ∧
      Mono ((evalAt U).map (kernel.ι I.res)) := by
  rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  exact ⟨isLimitMapKernelFork I U⟩

theorem moduleι_app_injective (U : X.Opens) : Function.Injective (I.moduleι.app U) := by
  have hmono := (exact_and_mono I U).2
  rw [ModuleCat.mono_iff_injective] at hmono
  exact hmono

theorem range_moduleι_app (U : X.Opens) :
    Set.range (I.moduleι.app U) = {s : Γ(X, U) | (I.subschemeι.app U).hom s = 0} := by
  have hex := (exact_and_mono I U).1
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  ext s
  exact SetLike.ext_iff.mp hex s

theorem range_moduleι_app_eq_ideal (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) := by
  rw [range_moduleι_app]
  ext s
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  conv_rhs => rw [← I.ker_subschemeι, Scheme.Hom.ker_apply]
  rfl

section Integral

variable [IsIntegral X]

omit [IsIntegral X] in

theorem map_moduleι_app {U V : X.Opens} (i : V ⟶ U) (m : Γ(I.module, U)) :
    (MonoidalCategoryStruct.tensorUnit X.Modules).presheaf.map i.op (I.moduleι.app U m) =
      I.moduleι.app V (I.module.presheaf.map i.op m) := by
  have := (I.moduleι.mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(I.module, U) → Γ(MonoidalCategoryStruct.tensorUnit X.Modules, V))) this) m).symm

omit [IsIntegral X] in
theorem map_moduleι_app' {U V : X.Opens} (i : V ⟶ U) (m : Γ(I.module, U)) :
    X.presheaf.map i.op (I.moduleι.app U m : Γ(X, U)) = (I.moduleι.app V (I.module.presheaf.map i.op m) : Γ(X, V)) :=
  map_moduleι_app (X := X) I i m

theorem map_injective_of_nonempty {U V : X.Opens} (i : V ⟶ U) [hV : Nonempty V] :
    Function.Injective (X.presheaf.map i.op) := by
  obtain ⟨⟨x, hx⟩⟩ := hV
  intro a b h
  apply germ_injective_of_isIntegral X x (i.le hx)
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf i x hx, ← TopCat.Presheaf.germ_res_apply X.presheaf i x hx, h]

theorem exists_presentation_isFrameOn :
    ∃ (φ : ∀ V : X.Opens, Γ(I.module, V) →+ (X.functionField : Type u)),
      (∀ (V V' : X.Opens) (h : V' ≤ V), Nonempty V' → ∀ m : Γ(I.module, V), φ V' (I.module.presheaf.map (homOfLE h).op m) = φ V m) ∧
      (∀ (V : X.Opens) [Nonempty V] (a : Γ(X, V)) (m : Γ(I.module, V)), φ V (a • m) = algebraMap Γ(X, V) X.functionField a * φ V m) ∧
      (∀ V : X.Opens, Nonempty V → Function.Injective (φ V)) ∧
      (∀ (W : X.affineOpens) (hW : Nonempty (W : X.Opens)) (g : Γ(X, W)), g ∈ nonZeroDivisors Γ(X, W) → I.ideal W = Ideal.span {g} →
        ∃ m : Γ(I.module, (W : X.Opens)), Scheme.Modules.IsFrameOn m W ∧
          φ W m = (letI := hW; X.germToFunctionField (W : X.Opens) g)) := by
  classical

  let φ : ∀ V : X.Opens, Γ(I.module, V) →+ (X.functionField : Type u) := fun V =>
    if hV : Nonempty V then
      (letI := hV; (X.germToFunctionField V).hom.toAddMonoidHom.comp (I.moduleι.app V).hom)
    else 0
  have hφ : ∀ (V : X.Opens) (hV : Nonempty V) (m : Γ(I.module, V)),
      φ V m = (letI := hV; X.germToFunctionField V (I.moduleι.app V m)) := by
    intro V hV m
    simp only [φ, dif_pos hV]
    rfl
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  ·
    intro V V' h hV' m
    haveI : Nonempty V := let ⟨⟨x, hx⟩⟩ := hV'; ⟨⟨x, h hx⟩⟩
    rw [hφ V' hV', hφ V inferInstance, ← map_moduleι_app']
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) _ _ _
  ·
    intro V hV a m
    rw [hφ V hV, hφ V hV, Scheme.Modules.Hom.app_smul]
    change X.germToFunctionField V ((a : Γ(X, V)) * (show Γ(X, V) from I.moduleι.app V m)) = _
    rw [map_mul]
    rfl
  ·
    intro V hV m₁ m₂ h
    rw [hφ V hV, hφ V hV] at h
    obtain ⟨⟨x, hx⟩⟩ := hV
    exact moduleι_app_injective I V (germ_injective_of_isIntegral X (genericPoint X) ((genericPoint_specializes x).mem_open V.2 hx) h)
  ·
    intro W hW g hg hIg

    have hgmem : (g : Γ(X, W)) ∈ Set.range (I.moduleι.app W) := by
      rw [range_moduleι_app_eq_ideal]
      rw [hIg]
      exact Ideal.subset_span rfl
    obtain ⟨m, hm⟩ := hgmem
    refine ⟨m, ?_, ?_⟩
    swap
    · rw [hφ W hW, hm]

    have hWne : Nontrivial Γ(X, (W : X.Opens)) := by
      haveI := hW
      infer_instance
    have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
    intro W' hW'W _

    set m' : Γ(I.module, W') := I.module.presheaf.map (homOfLE hW'W).op m with hm'
    have hs' : (I.moduleι.app W' m' : Γ(X, W')) = X.presheaf.map (homOfLE hW'W).op g := by
      rw [hm', ← map_moduleι_app', hm]

    have huniq : ∀ (V : X.Opens) (hV : V ≤ W') (c₁ c₂ : Γ(X, V)),
        c₁ * X.presheaf.map (homOfLE (hV.trans hW'W)).op g = c₂ * X.presheaf.map (homOfLE (hV.trans hW'W)).op g → c₁ = c₂ := by
      intro V hV c₁ c₂ h
      by_cases hVne : Nonempty V
      · haveI := hVne
        have hgV : X.presheaf.map (homOfLE (hV.trans hW'W)).op g ≠ 0 := by
          intro h0
          apply hg0
          apply map_injective_of_nonempty (X := X) (homOfLE (hV.trans hW'W))
          rw [h0, map_zero]
        exact mul_right_cancel₀ hgV h
      · have hVbot : V = ⊥ := by
          ext x
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hVne ⟨⟨x, hx⟩⟩
        have hsub : Subsingleton Γ(X, V) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hVbot)
        exact hsub.elim _ _
    constructor
    ·
      intro c₁ c₂ h
      have h' := congrArg (fun n : Γ(I.module, W') => (I.moduleι.app W' n : Γ(X, W'))) h
      simp only [Scheme.Modules.Hom.app_smul] at h'
      change c₁ * (show Γ(X, W') from I.moduleι.app W' m') = c₂ * (show Γ(X, W') from I.moduleι.app W' m') at h'
      rw [hs'] at h'
      exact huniq W' le_rfl c₁ c₂ h'
    ·
      intro n
      let t : Γ(X, W') := I.moduleι.app W' n

      let ι' := {V : X.affineOpens // (V : X.Opens) ≤ W'}
      let Uc : ι' → X.Opens := fun i => i.1
      have hcov : W' ≤ iSup Uc := by
        intro x hx
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W'.2
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩

      have hloc : ∀ i : ι', ∃ c : Γ(X, Uc i), c * X.presheaf.map (homOfLE (i.2.trans hW'W)).op g = X.presheaf.map (homOfLE i.2).op t := by
        intro i
        have hti : (X.presheaf.map (homOfLE i.2).op t : Γ(X, Uc i)) ∈ I.ideal i.1 := by
          have : (X.presheaf.map (homOfLE i.2).op t : Γ(X, Uc i)) ∈ Set.range (I.moduleι.app (i.1 : X.Opens)) := by
            refine ⟨I.module.presheaf.map (homOfLE i.2).op n, ?_⟩
            rw [← map_moduleι_app']
          rwa [range_moduleι_app_eq_ideal] at this
        have hIi : I.ideal i.1 = Ideal.span {X.presheaf.map (homOfLE (i.2.trans hW'W)).op g} := by
          rw [← I.map_ideal (show i.1 ≤ W from i.2.trans hW'W), hIg, Ideal.map_span, Set.image_singleton]
          rfl
        rw [hIi, Ideal.mem_span_singleton'] at hti
        exact hti
      choose c hc using hloc

      have hcompat : TopCat.Presheaf.IsCompatible X.presheaf Uc c := by
        intro i j
        apply huniq (Uc i ⊓ Uc j) (inf_le_left.trans i.2)
        have ei := congrArg (X.presheaf.map (homOfLE (inf_le_left : Uc i ⊓ Uc j ≤ Uc i)).op) (hc i)
        have ej := congrArg (X.presheaf.map (homOfLE (inf_le_right : Uc i ⊓ Uc j ≤ Uc j)).op) (hc j)
        simp only [map_mul] at ei ej
        rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← X.presheaf.map_comp] at ei
        rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← X.presheaf.map_comp] at ej
        have e1 : (X.presheaf.map (homOfLE (inf_le_left : Uc i ⊓ Uc j ≤ Uc i)).op) (c i) * X.presheaf.map (homOfLE ((inf_le_left.trans i.2).trans hW'W)).op g
            = X.presheaf.map (homOfLE (inf_le_left.trans i.2 : Uc i ⊓ Uc j ≤ W')).op t := ei
        have e2 : (X.presheaf.map (homOfLE (inf_le_right : Uc i ⊓ Uc j ≤ Uc j)).op) (c j) * X.presheaf.map (homOfLE ((inf_le_left.trans i.2).trans hW'W)).op g
            = X.presheaf.map (homOfLE (inf_le_left.trans i.2 : Uc i ⊓ Uc j ≤ W')).op t := ej
        exact e1.trans e2.symm
      obtain ⟨cglob, hcglob, -⟩ := X.sheaf.existsUnique_gluing' Uc W' (fun i => homOfLE i.2) hcov c hcompat
      let cg : Γ(X, W') := cglob
      have hcg : ∀ i, (X.presheaf.map (homOfLE i.2).op) cg = c i := hcglob
      refine ⟨cg, ?_⟩

      apply moduleι_app_injective I W'
      rw [Scheme.Modules.Hom.app_smul]
      change cg * (show Γ(X, W') from I.moduleι.app W' m') = t
      rw [hs']
      apply X.sheaf.eq_of_locally_eq' Uc W' (fun i => homOfLE i.2) hcov
      intro i
      change (X.presheaf.map (homOfLE i.2).op) (cg * X.presheaf.map (homOfLE hW'W).op g) = (X.presheaf.map (homOfLE i.2).op) t
      rw [map_mul, hcg, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
      exact hc i

end Integral

end AlgebraicGeometry.Scheme.IdealSheafData

theorem solution
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData) (hI : I.IsInvertible) :
    Scheme.Modules.IsInvertible I.module ∧
    ∃ (φ : ∀ V : X.Opens, Γ(I.module, V) →+ (X.functionField : Type u)),
      (∀ (V V' : X.Opens) (h : V' ≤ V), Nonempty V' → ∀ m : Γ(I.module, V), φ V' (I.module.presheaf.map (homOfLE h).op m) = φ V m) ∧
      (∀ (V : X.Opens) [Nonempty V] (a : Γ(X, V)) (m : Γ(I.module, V)), φ V (a • m) = algebraMap Γ(X, V) X.functionField a * φ V m) ∧
      (∀ V : X.Opens, Nonempty V → Function.Injective (φ V)) ∧
      (∀ (W : X.affineOpens) (hW : Nonempty (W : X.Opens)) (g : Γ(X, W)), g ∈ nonZeroDivisors Γ(X, W) → I.ideal W = Ideal.span {g} →
        ∃ m : Γ(I.module, (W : X.Opens)), Scheme.Modules.IsFrameOn m W ∧
          φ W m = (letI := hW; X.germToFunctionField (W : X.Opens) g)) :=
  ⟨hI.isInvertible_module, AlgebraicGeometry.Scheme.IdealSheafData.exists_presentation_isFrameOn I⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn (solution)
