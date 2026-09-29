-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b32a2dd0-138d-5578-9034-9796a676c23d

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation CerednikDrinfeld.QM"

namespace LambdaPullbackHom29

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (α : A ⟶ A) (hα : α ≫ f = f)

noncomputable abbrev sq : pullback f f ⟶ pullback f f :=
  pullback.map f f f f α α (𝟙 _) (by rw [Category.comp_id, hα]) (by rw [Category.comp_id, hα])

theorem sq_fst : sq f α hα ≫ pullback.fst f f = pullback.fst f f ≫ α := pullback.lift_fst _ _ _

theorem sq_snd : sq f α hα ≫ pullback.snd f f = pullback.snd f f ≫ α := pullback.lift_snd _ _ _

include hα in
theorem sq_addMor
    (hαhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt α hα (L.mul t P Q) = L.mul t (pushPt α hα P) (pushPt α hα Q)) :
    sq f α hα ≫ addMor f L = addMor f L ≫ α := by
  have hψ : sq f α hα ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by
    rw [← Category.assoc, sq_fst, Category.assoc, hα]
  have nat := L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) (sq f α hα) hψ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have e1 : sq f α hα ≫ addMor f L =
      (schemeHomOverComp (sq f α hα) hψ (L.mul (pullback.fst f f ≫ f)
        ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)).1 := rfl
  have p1 : schemeHomOverComp (sq f α hα) hψ (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) =
      pushPt α hα ⟨pullback.fst f f, rfl⟩ := Subtype.ext (sq_fst f α hα)
  have p2 : schemeHomOverComp (sq f α hα) hψ
        (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) =
      pushPt α hα ⟨pullback.snd f f, pullback.condition.symm⟩ := Subtype.ext (sq_snd f α hα)
  rw [e1, nat, p1, p2, ← hαhom]
  rfl

end LambdaPullbackHom29

open LambdaPullbackHom29

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (α : A ⟶ A) (hα : α ≫ f = f)
    (hαhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt α hα (L.mul t P Q) = L.mul t (pushPt α hα P) (pushPt α hα Q))
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N) :
    Nonempty (mumfordBundle f L ((Scheme.Modules.pullback α).obj N) ≅
      (Scheme.Modules.pullback
        (pullback.map f f f f α α (𝟙 _) (by rw [Category.comp_id, hα]) (by rw [Category.comp_id, hα]))).obj
          (mumfordBundle f L N)) := by
  obtain ⟨d⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 α hN
  let q := sq f α hα
  have hm : q ≫ addMor f L = addMor f L ≫ α := sq_addMor f L α hα hαhom
  let e₁ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (addMor f L)).obj N) ≅
      (Scheme.Modules.pullback (addMor f L)).obj ((Scheme.Modules.pullback α).obj N) :=
    (Scheme.Modules.pullbackComp q (addMor f L)).app N ≪≫ (Scheme.Modules.pullbackCongr hm).app N ≪≫
      ((Scheme.Modules.pullbackComp (addMor f L) α).app N).symm
  let e₂ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual N)) ≅
      (Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback α).obj N)) :=
    (Scheme.Modules.pullbackComp q (pullback.fst f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr (sq_fst f α hα)).app _ ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f f) α).app _).symm ≪≫ (Scheme.Modules.pullback (pullback.fst f f)).mapIso d
  let e₃ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual N)) ≅
      (Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual ((Scheme.Modules.pullback α).obj N)) :=
    (Scheme.Modules.pullbackComp q (pullback.snd f f)).app _ ≪≫ (Scheme.Modules.pullbackCongr (sq_snd f α hα)).app _ ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f f) α).app _).symm ≪≫ (Scheme.Modules.pullback (pullback.snd f f)).mapIso d
  exact ⟨(Scheme.Modules.pullbackTensorObjIso q _ _ ≪≫
    (e₁ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso q _ _ ≪≫ (e₂ ⊗ᵢ e₃)))).symm⟩

end S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_map_mumfordBundle (solution)
