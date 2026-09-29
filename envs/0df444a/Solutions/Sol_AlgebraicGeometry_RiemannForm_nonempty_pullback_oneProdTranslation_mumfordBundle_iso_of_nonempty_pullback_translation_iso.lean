-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d85c7bb2-e2f6-5a15-b8f2-b0fbb532ac68

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

namespace MumfordInvariance

variable {k : Type} [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem oneProdTranslation_comp_addMor (x : Pt f) :
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L x)
        (by rw [Category.assoc, translation_over]; exact pullback.condition) ≫ addMor f L =
      addMor f L ≫ translation f L x := by
  set τ := pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L x)
        (by rw [Category.assoc, translation_over]; exact pullback.condition) with hτ
  have h1 : τ ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have h2 : τ ≫ pullback.snd f f = pullback.snd f f ≫ translation f L x := pullback.lift_snd _ _ _
  have hbase : τ ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by rw [← Category.assoc, h1]
  have hsnd : pullback.snd f f ≫ f = pullback.fst f f ≫ f := pullback.condition.symm

  let P1 : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩
  let P2 : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, hsnd⟩
  let cQ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f ≫ f ≫ x.1, by
    rw [Category.assoc, Category.assoc, x.2, specMap_algebraMap_self, Category.comp_id]⟩

  have hL := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) τ hbase P1 P2)
  have hL1 : schemeHomOverComp τ hbase P1 = P1 := Subtype.ext h1
  have hL2 : schemeHomOverComp τ hbase P2 =
      L.mul (pullback.fst f f ≫ f) P2 cQ := by
    have h := L.mul_natural f (pullback.fst f f ≫ f) (pullback.snd f f) hsnd RelativeGroupLaw.idPoint (constPt f x)
    have ha : schemeHomOverComp (pullback.snd f f) hsnd (RelativeGroupLaw.idPoint (f := f)) = P2 :=
      Subtype.ext (Category.comp_id _)
    have hb : schemeHomOverComp (pullback.snd f f) hsnd (constPt f x) = cQ := by
      apply Subtype.ext
      change pullback.snd f f ≫ f ≫ x.1 = pullback.fst f f ≫ f ≫ x.1
      rw [← Category.assoc, hsnd, Category.assoc]
    rw [ha, hb] at h
    rw [← h]
    exact Subtype.ext h2
  rw [hL1, hL2] at hL

  have hR := congrArg Subtype.val (L.mul_natural f (pullback.fst f f ≫ f) (addMor f L) (addMor_over f L)
    RelativeGroupLaw.idPoint (constPt f x))
  have hR1 : schemeHomOverComp (addMor f L) (addMor_over f L) (RelativeGroupLaw.idPoint (f := f)) =
      L.mul (pullback.fst f f ≫ f) P1 P2 := Subtype.ext (Category.comp_id _)
  have hR2 : schemeHomOverComp (addMor f L) (addMor_over f L) (constPt f x) = cQ := by
    apply Subtype.ext
    change addMor f L ≫ f ≫ x.1 = pullback.fst f f ≫ f ≫ x.1
    rw [← Category.assoc, addMor_over, Category.assoc]
  rw [hR1, hR2, L.mul_assoc] at hR

  change τ ≫ (L.mul (pullback.fst f f ≫ f) P1 P2).1 = addMor f L ≫ (L.mul f RelativeGroupLaw.idPoint (constPt f x)).1
  exact hL.trans hR.symm

noncomputable def invUnique {X : Scheme.{0}} {N M M' : X.Modules} (d : N ⊗ M ≅ 𝟙_ _) (d' : N ⊗ M' ≅ 𝟙_ _) : M' ≅ M :=
  (λ_ M').symm ≪≫ (d.symm ⊗ᵢ Iso.refl M') ≪≫ (β_ N M ⊗ᵢ Iso.refl M') ≪≫ α_ M N M' ≪≫ (Iso.refl M ⊗ᵢ d') ≪≫ ρ_ M

end MumfordInvariance

open MumfordInvariance in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (Q : L.AlgPoints hc k)
    (hQ : Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛)) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj (mumfordBundle f L 𝓛) ≅
      mumfordBundle f L 𝓛) := by
  obtain ⟨eQ⟩ := hQ
  let x := RelativeGroupLaw.AlgPoints.toPoint Q
  let T := translation f L x
  let τ := pullback.lift (pullback.fst f f) (pullback.snd f f ≫ T)
    (by rw [Category.assoc, translation_over]; exact pullback.condition)
  have h1 : τ ≫ pullback.fst f f = pullback.fst f f := pullback.lift_fst _ _ _
  have h2 : τ ≫ pullback.snd f f = pullback.snd f f ≫ T := pullback.lift_snd _ _ _
  have h3 : τ ≫ addMor f L = addMor f L ≫ T := oneProdTranslation_comp_addMor L x
  let Lv := Scheme.Modules.dual 𝓛
  obtain ⟨d⟩ := (AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛).2

  let d' : 𝓛 ⊗ (Scheme.Modules.pullback T).obj Lv ≅ 𝟙_ _ :=
    (eQ.symm ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Modules.pullbackTensorObjIso T 𝓛 Lv).symm ≪≫
      (Scheme.Modules.pullback T).mapIso d ≪≫ Scheme.Modules.pullbackTensorUnitObjIso T
  let eQv : (Scheme.Modules.pullback T).obj Lv ≅ Lv := invUnique d d'

  let E1 : (Scheme.Modules.pullback τ).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) ≅
      (Scheme.Modules.pullback (addMor f L)).obj 𝓛 :=
    (Scheme.Modules.pullbackComp τ (addMor f L)).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr h3).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp (addMor f L) T).app 𝓛).symm ≪≫ (Scheme.Modules.pullback (addMor f L)).mapIso eQ
  let E2 : (Scheme.Modules.pullback τ).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj Lv) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj Lv :=
    (Scheme.Modules.pullbackComp τ (pullback.fst f f)).app Lv ≪≫ (Scheme.Modules.pullbackCongr h1).app Lv
  let E3 : (Scheme.Modules.pullback τ).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj Lv) ≅
      (Scheme.Modules.pullback (pullback.snd f f)).obj Lv :=
    (Scheme.Modules.pullbackComp τ (pullback.snd f f)).app Lv ≪≫ (Scheme.Modules.pullbackCongr h2).app Lv ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f f) T).app Lv).symm ≪≫ (Scheme.Modules.pullback (pullback.snd f f)).mapIso eQv
  refine ⟨?_⟩
  change (Scheme.Modules.pullback τ).obj (_ ⊗ (_ ⊗ _)) ≅ _ ⊗ (_ ⊗ _)
  exact Scheme.Modules.pullbackTensorObjIso τ _ _ ≪≫ (E1 ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso τ _ _ ≪≫ (E2 ⊗ᵢ E3)))

end S_AlgebraicGeometry_RiemannForm_nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso (solution)
