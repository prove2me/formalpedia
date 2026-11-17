-- Prove2me | solution 1 for AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:43.1006+00:00
-- url     : https://prove2.me/submissions/bacfcd36-9103-4dfd-a52b-7f3948a65ef3

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_pullback_pointLogHeight_eq
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_pointLogHeight_eq_add
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_externalTensor_pointLogHeight_eq_add_and_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SymmetricFiniteFrame

private theorem point_comp_addMor {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (x y : Scheme.KPoint f) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ Polarisation.addMor f G =
      (G.mul (𝟙 _) x y).1 := by
  let p := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hp : p ≫ (pullback.fst f f ≫ f) = 𝟙 _ := by
    simp only [p, pullback.lift_fst_assoc, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp p hp ⟨pullback.fst f f, rfl⟩ = x := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  have hy : GoodReductionJacobian.schemeHomOverComp p hp ⟨pullback.snd f f, pullback.condition.symm⟩ = y := by
    apply Subtype.ext
    exact pullback.lift_snd _ _ _
  have hn := G.mul_natural (pullback.fst f f ≫ f) (𝟙 _) p hp
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  rw [hx, hy] at hn
  exact congrArg Subtype.val hn

private theorem point_comp_negMor {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (x : Scheme.KPoint f) :
    x.1 ≫ Polarisation.negMor f G = (G.inv (𝟙 _) x).1 := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (Polarisation.idPt f) = x := by
    apply Subtype.ext
    exact Category.comp_id _
  have hn := G.mul_natural f (𝟙 _) x.1 x.2
    (G.inv f (Polarisation.idPt f)) (Polarisation.idPt f)
  rw [G.inv_mul_cancel, G.one_natural, hx] at hn
  letI := G.pointGroup (𝟙 (Spec (CommRingCat.of K)))
  have he : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (G.inv f (Polarisation.idPt f)) = G.inv (𝟙 _) x := by
    apply mul_right_cancel (b := x)
    change G.mul (𝟙 _) _ x = G.mul (𝟙 _) (G.inv (𝟙 _) x) x
    rw [G.inv_mul_cancel]
    exact hn.symm
  exact congrArg Subtype.val he

private theorem point_comp_subMor {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (x y : Scheme.KPoint f) :
    pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ Polarisation.subMor f G =
      (G.mul (𝟙 _) x (G.inv (𝟙 _) y)).1 := by
  rw [Polarisation.subMor, ← Category.assoc]
  have hpair : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫
      pullback.lift (pullback.fst f f)
        (pullback.snd f f ≫ Polarisation.negMor f G)
        (by rw [Category.assoc, Polarisation.negMor_over]; exact pullback.condition) =
      pullback.lift x.1 (G.inv (𝟙 _) y).1 (x.2.trans (G.inv (𝟙 _) y).2.symm) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        point_comp_negMor]
  rw [hpair]
  exact point_comp_addMor G x (G.inv (𝟙 _) y)

private theorem subMor_over {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f) :
    Polarisation.subMor f G ≫ f = pullback.fst f f ≫ f := by
  rw [Polarisation.subMor, Category.assoc, Polarisation.addMor_over,
    pullback.lift_fst_assoc]

/-- The parallelogram isomorphism bounds the height defect uniformly. -/
theorem _root_.solution {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ x y : Scheme.KPoint f,
      |F.height (G.mul (𝟙 _) x y) + F.height (G.mul (𝟙 _) x (G.inv (𝟙 _) y)) - 2 * F.height x - 2 * F.height y| ≤ Cp  := by
  classical
  have hpa := F.presentation.exists_pullback_pointLogHeight_eq (Polarisation.addMor f G)
  obtain ⟨Pa₀, _, _, ha⟩ := hpa
  let Pa : ((Scheme.Modules.pullback (Polarisation.addMor f G)).obj F.line).ProjPresentation
      (pullback.fst f f ≫ f) F.N :=
    { Pa₀ with toProj_π := Pa₀.toProj_π.trans (Polarisation.addMor_over f G) }
  have hps := F.presentation.exists_pullback_pointLogHeight_eq (Polarisation.subMor f G)
  obtain ⟨Ps₀, _, _, hs⟩ := hps
  let Ps : ((Scheme.Modules.pullback (Polarisation.subMor f G)).obj F.line).ProjPresentation
      (pullback.fst f f ≫ f) F.N :=
    { Ps₀ with toProj_π := Ps₀.toProj_π.trans (subMor_over G) }
  obtain ⟨_, T, _, ht⟩ := Pa.exists_tensor_pointLogHeight_eq_add Ps
  obtain ⟨Nq, Q, hQ, hq⟩ :=
    F.presentation.exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
      F.presentation_finite 2 (by norm_num)
  obtain ⟨R, hR, hr⟩ := Q.exists_externalTensor_pointLogHeight_eq_add_and_isFinite Q hQ hQ
  obtain ⟨C, hC, hbound⟩ :=
    R.exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite T
      F.parallelogramIso.some.symm hR
  refine ⟨C, hC, ?_⟩
  intro x y
  let z : Scheme.KPoint (pullback.fst f f ≫ f) :=
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm), by
      rw [pullback.lift_fst_assoc, x.2]⟩
  have haz : Pa.pointLogHeight z = F.height (G.mul (𝟙 _) x y) := by
    have hza : z.1 ≫ (Polarisation.addMor f G ≫ f) = 𝟙 _ := by
      rw [Polarisation.addMor_over]
      exact z.2
    change Pa₀.pointLogHeight ⟨z.1, hza⟩ = _
    rw [ha]
    apply congrArg F.height
    apply Subtype.ext
    exact point_comp_addMor G x y
  have hsz : Ps.pointLogHeight z = F.height (G.mul (𝟙 _) x (G.inv (𝟙 _) y)) := by
    have hzs : z.1 ≫ (Polarisation.subMor f G ≫ f) = 𝟙 _ := by
      rw [subMor_over]
      exact z.2
    change Ps₀.pointLogHeight ⟨z.1, hzs⟩ = _
    rw [hs]
    apply congrArg F.height
    apply Subtype.ext
    exact point_comp_subMor G x y
  have hrz : R.pointLogHeight z = 2 * F.height x + 2 * F.height y := by
    simpa only [z, pullback.lift_fst, pullback.lift_snd, hq, Nat.cast_ofNat, height] using hr z
  have hb := hbound z
  rw [hrz, ht, haz, hsz, abs_sub_comm] at hb
  convert hb using 1 <;> congr 1 <;> ring

end AlgebraicGeometry.SymmetricFiniteFrame
