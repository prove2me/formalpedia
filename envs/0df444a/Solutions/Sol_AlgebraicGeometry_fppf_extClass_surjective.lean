-- Prove2me | solution 1 for AlgebraicGeometry.fppf_extClass_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1a4ada70-ad21-5616-a0e4-bef1b8b6530a

import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_fppf_extClass_surjective

set_option autoImplicit false
set_option linter.unusedSimpArgs false

p2m_open "CategoryTheory P2MW.S_AlgebraicGeometry_fppf_extClass_surjective.CategoryTheory CategoryTheory.Abelian P2MW.S_AlgebraicGeometry_fppf_extClass_surjective.CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"

section GeneralAbelian

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]

namespace CategoryTheory p2m_export "CategoryTheory" "Epi Category ShortComplex.Exact ShortComplex.mk Abelian Abelian.Ext Limits.zero_comp ShortComplex.Exact.lift_f mono_of_mono_fac constantSheaf Injective ShortComplex.exact_of_g_is_cokernel Limits.comp_zero Injective.ι Sheaf HasExt Category.id_comp ShortComplex ShortComplex.ShortExact EnoughInjectives Mono ShortComplex.exact_of_f_is_kernel ShortComplex.ShortExact.extClass_naturality Injective.under Category.assoc" namespace Abelian p2m_export "CategoryTheory.Abelian" "Ext.homEquiv₀ Ext Ext.comp_mk₀_id Ext.eq_zero_of_injective Ext.mk₀ mk Ext.mk₀_homEquiv₀_apply Ext.covariant_sequence_exact₁" namespace Ext p2m_export "CategoryTheory.Abelian.Ext" "homEquiv₀ zero_comp comp comp_mk₀_id eq_zero_of_injective comp_zero mk₀ mk₀_homEquiv₀_apply covariant_sequence_exact₁" end CategoryTheory.Abelian.Ext
p2m_open_scoped "CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext" in

theorem CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq
    {X Y : C} (e : Ext.{w} X Y 1) :
    ∃ (E : C) (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact), hS.extClass = e := by

  let S : ShortComplex C := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
    (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

  have he0 : e.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective (I := Injective.under Y) _

  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS e he0 (zero_add 1)
  let φ : X ⟶ S.X₃ := Ext.homEquiv₀ x₃
  haveI : Epi S.g := hS.epi_g
  haveI : Mono S.f := hS.mono_f
  have hpc : pullback.fst S.g φ ≫ S.g = pullback.snd S.g φ ≫ φ := pullback.condition

  let ι' : Y ⟶ pullback S.g φ := pullback.lift S.f 0 (by simp)
  have hι'fst : ι' ≫ pullback.fst S.g φ = S.f := pullback.lift_fst _ _ _
  have hι'snd : ι' ≫ pullback.snd S.g φ = 0 := pullback.lift_snd _ _ _
  haveI : Mono ι' := mono_of_mono_fac hι'fst

  let S' : ShortComplex C := ShortComplex.mk ι' (pullback.snd S.g φ) hι'snd
  have hS' : S'.ShortExact := by
    refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_ }
    refine KernelFork.IsLimit.ofι' ι' hι'snd (fun {A} k hk => ⟨?_, ?_⟩)
    · exact hS.exact.lift (k ≫ pullback.fst S.g φ)
        (by rw [Category.assoc, hpc, reassoc_of% hk, Limits.zero_comp])
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hι'fst, ShortComplex.Exact.lift_f]
      · simp only [Category.assoc, hι'snd, Limits.comp_zero, hk]

  let ψ : S' ⟶ S :=
    { τ₁ := 𝟙 Y
      τ₂ := pullback.fst S.g φ
      τ₃ := φ
      comm₁₂ := by dsimp only [S', S]; rw [Category.id_comp, hι'fst]
      comm₂₃ := hpc }
  refine ⟨pullback S.g φ, ι', pullback.snd S.g φ, hι'snd, hS', ?_⟩
  have hnat := ShortComplex.ShortExact.extClass_naturality hS' hS ψ
  rw [show ψ.τ₁ = 𝟙 Y from rfl, Ext.comp_mk₀_id] at hnat
  rw [hnat, show ψ.τ₃ = φ from rfl, show Ext.mk₀ φ = x₃ from Ext.mk₀_homEquiv₀_apply x₃, hx₃]

end GeneralAbelian

theorem solution
    (F : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (e : CategoryTheory.Abelian.Ext
      ((CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ))) F 1) :
    ∃ (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
      (f : F ⟶ E)
      (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)))
      (w : f ≫ g = 0)
      (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact),
      hS.extClass = e :=
  CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq e

end S_AlgebraicGeometry_fppf_extClass_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_fppf_extClass_surjective (solution)
