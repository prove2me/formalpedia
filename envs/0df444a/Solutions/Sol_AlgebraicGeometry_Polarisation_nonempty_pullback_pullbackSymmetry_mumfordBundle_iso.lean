-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/47129edb-7218-5aa5-97bf-0d13b8092af5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation"

namespace LBirigid

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x y : SchemeHomOver t f) :
    (L.mul t' ⟨x.1, h ▸ x.2⟩ ⟨y.1, h ▸ y.2⟩).1 = (L.mul t x y).1 := by
  subst h; rfl

theorem one_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    (L.one t').1 = (L.one t).1 := by
  subst h; rfl

theorem nonempty_slice_iso_iff {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x : SchemeHomOver t f) (M : (pullback f f).Modules) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (⟨x.1, h ▸ x.2⟩ : SchemeHomOver t' f))).obj M ≅ 𝟙_ _) ↔
      Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj M ≅ 𝟙_ _) := by
  subst h; exact Iff.rfl

theorem pullbackSymmetry_hom_comp_addMor (hc : L.IsCommutative) :
    (pullbackSymmetry f f).hom ≫ addMor f L = addMor f L := by
  let σ := (pullbackSymmetry f f).hom
  have hσ : σ ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f := by
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst, ← pullback.condition]
  have hnat := L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) σ hσ
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have e1 : schemeHomOverComp σ hσ ⟨pullback.fst f f, rfl⟩ = ⟨pullback.snd f f, pullback.condition.symm⟩ :=
    Subtype.ext (pullbackSymmetry_hom_comp_fst f f)
  have e2 : schemeHomOverComp σ hσ ⟨pullback.snd f f, pullback.condition.symm⟩ = ⟨pullback.fst f f, rfl⟩ :=
    Subtype.ext (pullbackSymmetry_hom_comp_snd f f)
  rw [e1, e2] at hnat
  exact (congrArg Subtype.val hnat).trans (congrArg Subtype.val (hc.mul_comm _ _ _))

theorem nonempty_pullback_pullbackSymmetry_mumfordBundle_iso (hc : L.IsCommutative) (𝓜 : A.Modules) :
    Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L 𝓜) ≅ mumfordBundle f L 𝓜) := by
  let σ := (pullbackSymmetry f f).hom
  let Ps := Scheme.Modules.pullback σ
  let D := Scheme.Modules.dual 𝓜
  refine ⟨?_⟩
  calc Ps.obj (mumfordBundle f L 𝓜)
      ≅ Ps.obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓜) ⊗
          Ps.obj ((Scheme.Modules.pullback (pullback.fst f f)).obj D ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj D) :=
        Scheme.Modules.pullbackTensorObjIso σ _ _
    _ ≅ Ps.obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓜) ⊗
          (Ps.obj ((Scheme.Modules.pullback (pullback.fst f f)).obj D) ⊗ Ps.obj ((Scheme.Modules.pullback (pullback.snd f f)).obj D)) :=
        whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso σ _ _)
    _ ≅ (Scheme.Modules.pullback (σ ≫ addMor f L)).obj 𝓜 ⊗
          ((Scheme.Modules.pullback (σ ≫ pullback.fst f f)).obj D ⊗ (Scheme.Modules.pullback (σ ≫ pullback.snd f f)).obj D) :=
        ((Scheme.Modules.pullbackComp σ (addMor f L)).app 𝓜) ⊗ᵢ
          (((Scheme.Modules.pullbackComp σ (pullback.fst f f)).app D) ⊗ᵢ ((Scheme.Modules.pullbackComp σ (pullback.snd f f)).app D))
    _ ≅ (Scheme.Modules.pullback (addMor f L)).obj 𝓜 ⊗
          ((Scheme.Modules.pullback (pullback.snd f f)).obj D ⊗ (Scheme.Modules.pullback (pullback.fst f f)).obj D) :=
        ((Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_addMor L hc)).app 𝓜) ⊗ᵢ
          (((Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_fst f f)).app D) ⊗ᵢ
           ((Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_snd f f)).app D))
    _ ≅ mumfordBundle f L 𝓜 := whiskerLeftIso _ (β_ _ _)

end LBirigid

open LBirigid in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓜 : A.Modules) :
    Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj (mumfordBundle f L 𝓜) ≅ mumfordBundle f L 𝓜) := by
  exact nonempty_pullback_pullbackSymmetry_mumfordBundle_iso L hc 𝓜

end
end S_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_pullback_pullbackSymmetry_mumfordBundle_iso (solution)
