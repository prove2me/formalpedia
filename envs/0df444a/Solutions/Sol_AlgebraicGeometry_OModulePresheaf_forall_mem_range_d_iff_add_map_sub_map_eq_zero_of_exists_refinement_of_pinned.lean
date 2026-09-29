-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/939f1967-aad2-5837-9216-b747e25e2e8d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace P2mT2

theorem unitPullback_sub {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (a b : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (a - b) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n a -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n b := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
    erw [map_sub, map_sub, smul_sub]
    rfl
  · simp only [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, sub_zero]

theorem unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (0 : (OModulePresheaf.unit πY).cochain 𝒦 n) = 0 := by
  have := unitPullback_sub πX πY h 𝒲 𝒦 lam hlam n 0 0
  simpa using this

end P2mT2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in
theorem solution
    {κ : Type u} [Field κ] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of κ)) [IsSeparated πX]
    (𝒦 : X.OrderedAffineCover) (ψ : X ⟶ X)

    (R : Type u) [CommRing R] [Algebra κ R] (ev : R →+* κ)
    (W : Type u) [AddCommGroup W] [Module κ W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module κ M], ↥(Algebra.PointDerivations κ R ev (M)) ≃ₗ[κ] (W ⊗[κ] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
        (δ : ↥(Algebra.PointDerivations κ R ev (M))),
        Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[κ] W) g (Φ M δ))
    (V : Type u) [AddCommGroup V] [Module κ V]

    (H₁ : Type u) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) →ₗ[κ] H₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit πX).cochain 𝒦 1) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0))
    (ρψ : H₁ →ₗ[κ] H₁)
    (hρψ : ∀ (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := πX) ψ 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 0) →
        ρψ (cls₁ z) = cls₁ z')
    (θψ : W →ₗ[κ] W)

    (c c₀ c' : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)))
    (ĉ ĉ₀ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))))
    (hĉ : ∀ (a : R) (ξ : Module.Dual κ V), ((ĉ.1 a ξ).1 : (OModulePresheaf.unit πX).cochain 𝒦 1) = c.1 a ξ)
    (hĉ₀ : ∀ (a : R) (ξ : Module.Dual κ V), ((ĉ₀.1 a ξ).1 : (OModulePresheaf.unit πX).cochain 𝒦 1) = c₀.1 a ξ)
    (hc'Z : ∀ (a : R) (ξ : Module.Dual κ V), (OModulePresheaf.unit πX).d 𝒦 1 (c'.1 a ξ) = 0)

    (hrel : ∃ (𝒱₀ : X.OrderedAffineCover) (lam₀ lam₀' : 𝒱₀.ι → 𝒦.ι)
      (hl₀ : ∀ v, 𝒱₀.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₀ v)) (hl₀' : ∀ v, 𝒱₀.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₀' v)),
      ∀ (a : R) (ξ : Module.Dual κ V),
        ∃ b : (OModulePresheaf.unit πX).cochain 𝒱₀ 0,
          (OModulePresheaf.unit πX).d 𝒱₀ 0 b =
            OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c'.1 a ξ)
              - OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ)
              - OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (((Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) c))).1 a ξ)
              + OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ 1 (c.1 a ξ)) :
    (∀ (a : R) (ξ : Module.Dual κ V), c'.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0)) ↔
      (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ₀) +
          (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁))
              (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ)) -
            TensorProduct.map (LinearMap.id : W →ₗ[κ] W) (LinearMap.llcomp κ (Module.Dual κ V) H₁ H₁ ρψ)
              (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ))) = 0) := by
  classical
  obtain ⟨𝒱₀, lam₀, lam₀', hl₀, hl₀', hrel'⟩ := hrel
  obtain ⟨e₀, en, he₀, hen⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated πX 𝒦 𝒱₀ lam₀' hl₀'

  set gval : (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) :=
    LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) ((OModulePresheaf.unit πX).cochain 𝒦 1) (LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)).subtype with hgval
  set gcls : (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁) := LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁ with hgcls
  set gρ : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁) := LinearMap.llcomp κ (Module.Dual κ V) H₁ H₁ ρψ with hgρ

  have hcĉ : c = Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) ev gval ĉ := by
    apply Subtype.ext
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro ξ
    rw [Algebra.PointDerivations.map_apply_coe]
    simp only [hgval, LinearMap.llcomp_apply, Submodule.subtype_apply]
    exact (hĉ a ξ).symm

  set ĉθ : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) := (Φ (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))).symm (TensorProduct.map θψ LinearMap.id (Φ (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))) ĉ)) with hĉθ
  have hmapθ : ∀ (M M' : Type u) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
      (δ : ↥(Algebra.PointDerivations κ R ev (M))),
      Algebra.PointDerivations.map (M := M) (M' := M') ev g ((Φ M).symm (TensorProduct.map θψ LinearMap.id (Φ M δ))) =
        (Φ M').symm (TensorProduct.map θψ LinearMap.id (Φ M' (Algebra.PointDerivations.map (M := M) (M' := M') ev g δ))) := by
    intro M M' _ _ _ _ g δ
    apply (Φ M').injective
    rw [LinearEquiv.apply_symm_apply, hΦnat, LinearEquiv.apply_symm_apply, hΦnat, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, ← LinearMap.comp_apply (f := TensorProduct.map θψ LinearMap.id), ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
  have hθcoch : Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) ev gval ĉθ =
      (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) c)) := by
    rw [hĉθ, hmapθ, ← hcĉ]
  have hθval : ∀ (a : R) (ξ : Module.Dual κ V), ((ĉθ.1 a ξ).1 : (OModulePresheaf.unit πX).cochain 𝒦 1) =
      ((Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) c))).1 a ξ := by
    intro a ξ
    rw [← hθcoch, Algebra.PointDerivations.map_apply_coe]
    simp only [hgval, LinearMap.llcomp_apply, Submodule.subtype_apply]

  have hz'' : ∀ (a : R) (ξ : Module.Dual κ V), ∃ z'' : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)),
      OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ (0 + 1) (ĉ.1 a ξ).1 -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' (0 + 1) z''.1 ∈
        LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₀ 0) := by
    intro a ξ
    have hw : OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ (0 + 1) (ĉ.1 a ξ).1 ∈
        LinearMap.ker ((OModulePresheaf.unit πX).d 𝒱₀ (0 + 1)) := by
      rw [LinearMap.mem_ker, OModulePresheaf.d_unitPullback, LinearMap.mem_ker.1 (ĉ.1 a ξ).2, P2mT2.unitPullback_zero]
    obtain ⟨q, hq⟩ := (en 0).surjective (Submodule.Quotient.mk ⟨_, hw⟩)
    obtain ⟨z'', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hz₁, hz₂⟩ := hen 0 z''
    refine ⟨z'', ?_⟩
    rw [hz₂] at hq
    have := (Submodule.Quotient.eq _).1 hq.symm
    simpa using this
  choose zz hzz using hz''
  have hρ : ∀ (a : R) (ξ : Module.Dual κ V), ρψ (cls₁ (ĉ.1 a ξ)) = cls₁ (zz a ξ) :=
    fun a ξ => hρψ 𝒱₀ lam₀ lam₀' hl₀ hl₀' (ĉ.1 a ξ) (zz a ξ) (hzz a ξ)

  have key : ∀ (a : R) (ξ : Module.Dual κ V),
      (c'.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0) ↔
        cls₁ (ĉ₀.1 a ξ) + (cls₁ (ĉθ.1 a ξ) - ρψ (cls₁ (ĉ.1 a ξ))) = 0) := by
    intro a ξ
    rw [hρ, ← map_sub, ← map_add, ← add_sub_assoc, hcls₁0]

    obtain ⟨b, hb⟩ := hrel' a ξ
    have hdiff : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c'.1 a ξ - ((ĉ₀.1 a ξ + ĉθ.1 a ξ - zz a ξ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))) : (OModulePresheaf.unit πX).cochain 𝒦 1)) ∈
        LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₀ 0) := by
      have e1 : (((ĉ₀.1 a ξ + ĉθ.1 a ξ - zz a ξ : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1))) : (OModulePresheaf.unit πX).cochain 𝒦 1)) = c₀.1 a ξ + (ĉθ.1 a ξ).1 - (zz a ξ).1 := by
        simp only [Submodule.coe_add, Submodule.coe_sub, hĉ₀]
      rw [e1, P2mT2.unitPullback_sub, P2mT2.unitPullback_sub]
      have e2 : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ + (ĉθ.1 a ξ).1) =
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ) + OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (ĉθ.1 a ξ).1 := by
        have := P2mT2.unitPullback_sub πX πX (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ + (ĉθ.1 a ξ).1) (ĉθ.1 a ξ).1
        rw [add_sub_cancel_right] at this
        rw [this]; abel
      rw [e2, hθval]
      have hzz' := hzz a ξ

      change OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ 1 (ĉ.1 a ξ).1 -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (zz a ξ).1 ∈ _ at hzz'
      rw [hĉ] at hzz'
      have hb' : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c'.1 a ξ) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (c₀.1 a ξ) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 (((Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) →ₗ[κ] (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1)) (Φ (Module.Dual κ V →ₗ[κ] (OModulePresheaf.unit πX).cochain 𝒦 1) c))).1 a ξ) +
          OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₀ 𝒦 lam₀ hl₀ 1 (c.1 a ξ) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₀ 0) := ⟨b, hb⟩
      have := Submodule.sub_mem _ hb' hzz'
      convert this using 1
      abel

    have hZc' : c'.1 a ξ ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1) := LinearMap.mem_ker.2 (hc'Z a ξ)
    have hinj : ∀ w : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)),
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₀ 𝒦 lam₀' hl₀' 1 w.1 ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₀ 0) →
        (w.1 : (OModulePresheaf.unit πX).cochain 𝒦 1) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒦 0) := by
      intro w hw
      obtain ⟨hw₁, hw₂⟩ := hen 0 w
      have hq : (en 0) (Submodule.Quotient.mk w) = 0 := by
        rw [hw₂]; exact (Submodule.Quotient.mk_eq_zero _).2 (by simpa using hw)
      have h2 : (Submodule.Quotient.mk w : (OModulePresheaf.unit πX).HSucc 𝒦 0) = 0 :=
        (en 0).injective (by rw [hq, LinearEquiv.map_zero])
      have := (Submodule.Quotient.mk_eq_zero _).1 h2
      simpa using this
    have hsub := hinj (⟨c'.1 a ξ, hZc'⟩ - (ĉ₀.1 a ξ + ĉθ.1 a ξ - zz a ξ)) (by simpa only [Submodule.coe_sub] using hdiff)
    simp only [Submodule.coe_sub] at hsub
    constructor
    · intro h
      have := Submodule.sub_mem _ h hsub
      simpa using this
    · intro h
      have := Submodule.add_mem _ hsub h
      simpa using this

  have hT : Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ₀) +
        (TensorProduct.map θψ (LinearMap.id : (Module.Dual κ V →ₗ[κ] H₁) →ₗ[κ] (Module.Dual κ V →ₗ[κ] H₁))
            (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ)) -
          TensorProduct.map (LinearMap.id : W →ₗ[κ] W) (LinearMap.llcomp κ (Module.Dual κ V) H₁ H₁ ρψ)
            (Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev (LinearMap.llcomp κ (Module.Dual κ V) ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)) H₁ cls₁) ĉ))) =
      Φ (Module.Dual κ V →ₗ[κ] H₁) (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev gcls ĉ₀ +
        (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev gcls ĉθ -
          Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] H₁)) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev gρ
            (Algebra.PointDerivations.map (M := (Module.Dual κ V →ₗ[κ] ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒦 1)))) (M' := (Module.Dual κ V →ₗ[κ] H₁)) ev gcls ĉ))) := by
    rw [map_add (Φ (Module.Dual κ V →ₗ[κ] H₁)), map_sub (Φ (Module.Dual κ V →ₗ[κ] H₁)), hΦnat _ _ gρ, ← hgcls, ← hgρ]
    congr 2
    rw [hĉθ, hmapθ, LinearEquiv.apply_symm_apply]
  rw [hT, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    apply Subtype.ext
    apply LinearMap.ext; intro a; apply LinearMap.ext; intro ξ
    have := (key a ξ).1 (h a ξ)
    simpa [hgcls, hgρ, LinearMap.llcomp_apply, Algebra.PointDerivations.map_apply_coe] using this
  · intro h a ξ
    apply (key a ξ).2
    have := congrArg (fun D : ↥(Algebra.PointDerivations κ R ev (Module.Dual κ V →ₗ[κ] H₁)) => D.1 a ξ) h
    simpa [hgcls, hgρ, LinearMap.llcomp_apply, Algebra.PointDerivations.map_apply_coe] using this

end S_AlgebraicGeometry_OModulePresheaf_forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_mem_range_d_iff_add_map_sub_map_eq_zero_of_exists_refinement_of_pinned (solution)
