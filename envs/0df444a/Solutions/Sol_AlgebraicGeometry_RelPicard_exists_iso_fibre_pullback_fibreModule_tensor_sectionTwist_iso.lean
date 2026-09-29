-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/df19b42c-9a2f-55b9-aee5-e77001c90913

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso SmoothOfRelativeDimension IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom Spec Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp RelPicard.rigSection RelPicard.sectionIdeal RelPicard.sectionTwist Scheme.IdealSheafData.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso"
p2m_open "AlgebraicGeometry"

theorem fibreIdE9_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {k : Type u} [Field k] {C T : Scheme.{u}}

theorem fibreIdE9_isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (RelPicard.rigSection c t ε) hσq

theorem fibreIdE9_sectionIdeal_comap_section (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (ix : C ⟶ pullback c t) (hix_fst : ix ≫ pullback.fst c t = 𝟙 C)
    (hix_snd : ix ≫ pullback.snd c t = c ≫ x) :
    (RelPicard.sectionIdeal c ε t).comap ix = ε.1.ker := by
  have hrig_snd : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  have hrig_fst : RelPicard.rigSection c t ε ≫ pullback.fst c t = t ≫ ε.1 := by
    simp only [RelPicard.rigSection, pullback.lift_fst]
  haveI : IsClosedImmersion (RelPicard.rigSection c t ε) := by
    have : IsClosedImmersion (RelPicard.rigSection c t ε ≫ pullback.snd c t) := by
      rw [hrig_snd]; infer_instance
    exact IsClosedImmersion.of_comp (RelPicard.rigSection c t ε) (pullback.snd c t)

  have hsq : ε.1 ≫ ix = x ≫ RelPicard.rigSection c t ε := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hix_fst, hrig_fst, Category.comp_id, ← Category.assoc, hx,
        Category.id_comp]
    · rw [Category.assoc, Category.assoc, hix_snd, hrig_snd, Category.comp_id, ← Category.assoc, ε.2,
        Category.id_comp]
  let q : Spec (CommRingCat.of k) ⟶ pullback ix (RelPicard.rigSection c t ε) := pullback.lift ε.1 x hsq
  have hq_fst : q ≫ pullback.fst ix (RelPicard.rigSection c t ε) = ε.1 := pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd ix (RelPicard.rigSection c t ε) = x := pullback.lift_snd _ _ _
  have hB1 : pullback.fst ix (RelPicard.rigSection c t ε) =
      pullback.snd ix (RelPicard.rigSection c t ε) ≫ t ≫ ε.1 := by
    have h := congrArg (· ≫ pullback.fst c t)
      (pullback.condition (f := ix) (g := RelPicard.rigSection c t ε))
    simp only [Category.assoc, hix_fst, hrig_fst, Category.comp_id] at h
    exact h
  have hB2 : pullback.fst ix (RelPicard.rigSection c t ε) ≫ c ≫ x =
      pullback.snd ix (RelPicard.rigSection c t ε) := by
    have h := congrArg (· ≫ pullback.snd c t)
      (pullback.condition (f := ix) (g := RelPicard.rigSection c t ε))
    simp only [Category.assoc, hix_snd, hrig_snd, Category.comp_id] at h
    exact h
  have hB3 : pullback.fst ix (RelPicard.rigSection c t ε) ≫ c =
      pullback.snd ix (RelPicard.rigSection c t ε) ≫ t := by
    rw [hB1, Category.assoc, Category.assoc, ε.2, Category.comp_id]
  haveI : IsIso q := by
    refine ⟨⟨pullback.fst ix (RelPicard.rigSection c t ε) ≫ c, ?_, ?_⟩⟩
    · rw [← Category.assoc, hq_fst, ε.2]
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hq_fst, Category.id_comp, ← Category.assoc, hB3,
          Category.assoc, ← hB1]
      · rw [Category.assoc, Category.assoc, hq_snd, Category.id_comp, hB2]
  calc (RelPicard.sectionIdeal c ε t).comap ix
      = (RelPicard.rigSection c t ε).ker.comap ix := rfl
    _ = (pullback.fst ix (RelPicard.rigSection c t ε)).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (RelPicard.rigSection c t ε) ix).symm
    _ = (q ≫ pullback.fst ix (RelPicard.rigSection c t ε)).ker :=
        (Scheme.Hom.ker_comp_of_isIso q _).symm
    _ = ε.1.ker := by rw [hq_fst]

theorem fibreIdE9_nonempty_pullback_sectionTwist_iso (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (ix : C ⟶ pullback c t) (hix_fst : ix ≫ pullback.fst c t = 𝟙 C)
    (hix_snd : ix ≫ pullback.snd c t = c ≫ x) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback ix).obj (RelPicard.sectionTwist c ε t d) ≅
      ((ε.1.ker) ^ d).invModule) := by
  have hJ : (RelPicard.sectionIdeal c ε t).IsInvertible := fibreIdE9_isInvertible_sectionIdeal c ε t
  have hε : (ε.1.ker).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 ε.2
  have hcomap : ((RelPicard.sectionIdeal c ε t) ^ d).comap ix = (ε.1.ker) ^ d := by
    rw [fibreIdE9_comap_pow]
    exact congrArg (· ^ d) (fibreIdE9_sectionIdeal_comap_section c ε t x hx ix hix_fst hix_snd)
  have hI' : (((RelPicard.sectionIdeal c ε t) ^ d).comap ix).IsInvertible := by
    rw [hcomap]; exact hε.pow d
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso ix (hJ.pow d) hI'
  unfold RelPicard.sectionTwist
  exact ⟨e ≪≫ eqToIso (by rw [hcomap])⟩

end AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _) :
    ∃ φ : C ≅ pullback (pullback.snd c t) x,
      φ.hom ≫ fibreAt c t x = c ∧
      φ.hom ≫ pullback.fst (pullback.snd c t) x =
        pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]) ∧
      ∀ (F : (pullback c t).Modules) (d : ℕ),
        Nonempty ((Scheme.Modules.pullback φ.hom).obj (fibreModule c t x (F ⊗ sectionTwist c ε t d)) ≅
          (Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).obj F ⊗
            ((ε.1.ker) ^ d).invModule) := by
  have hix : 𝟙 C ≫ c = (c ≫ x) ≫ t := by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]
  let ix : C ⟶ pullback c t := pullback.lift (𝟙 C) (c ≫ x) hix
  have hix_fst : ix ≫ pullback.fst c t = 𝟙 C := pullback.lift_fst _ _ _
  have hix_snd : ix ≫ pullback.snd c t = c ≫ x := pullback.lift_snd _ _ _

  have hA : pullback.fst (pullback.snd c t) x ≫ pullback.fst c t ≫ c =
      pullback.snd (pullback.snd c t) x := by
    rw [pullback.condition (f := c) (g := t), ← Category.assoc,
      pullback.condition (f := pullback.snd c t) (g := x), Category.assoc, hx, Category.comp_id]
  let φhom : C ⟶ pullback (pullback.snd c t) x := pullback.lift ix c (by rw [hix_snd])
  have hφ_fst : φhom ≫ pullback.fst (pullback.snd c t) x = ix := pullback.lift_fst _ _ _
  have hφ_snd : φhom ≫ pullback.snd (pullback.snd c t) x = c := pullback.lift_snd _ _ _
  let φ : C ≅ pullback (pullback.snd c t) x :=
    { hom := φhom
      inv := pullback.fst (pullback.snd c t) x ≫ pullback.fst c t
      hom_inv_id := by rw [← Category.assoc, hφ_fst, hix_fst]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hφ_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, Category.assoc, hix_fst, Category.comp_id]
          · rw [Category.assoc, Category.assoc, hix_snd,
              pullback.condition (f := pullback.snd c t) (g := x), ← hA]
            simp only [Category.assoc]
        · rw [Category.assoc, Category.assoc, hφ_snd, Category.id_comp, hA] }
  refine ⟨φ, ?_, hφ_fst, fun F d => ?_⟩
  · show φhom ≫ pullback.snd (pullback.snd c t) x = c
    exact hφ_snd
  · obtain ⟨e4⟩ :=
      AlgebraicGeometry.fibreIdE9_nonempty_pullback_sectionTwist_iso c ε t x hx ix hix_fst hix_snd d
    exact ⟨(Scheme.Modules.pullbackComp φhom (pullback.fst (pullback.snd c t) x)).app
        (F ⊗ sectionTwist c ε t d) ≪≫
      (Scheme.Modules.pullbackCongr hφ_fst).app (F ⊗ sectionTwist c ε t d) ≪≫
      Scheme.Modules.pullbackTensorObjIso ix F (sectionTwist c ε t d) ≪≫
      whiskerLeftIso ((Scheme.Modules.pullback ix).obj F) e4⟩

end S_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso (solution)
