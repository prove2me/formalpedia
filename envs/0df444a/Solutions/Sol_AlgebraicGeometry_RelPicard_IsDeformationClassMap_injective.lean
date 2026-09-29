-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8e10e953-6b27-54ab-a753-114059f87305

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective.AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective.AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Scheme.Modules Scheme.Modules.map_smul Scheme.TwoAffineOpenCover Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "dualNumberThickening oneAddEpsMul H1StructureSheaf IsDeformationClassMap RigKerDualNumber RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem isFrameOn_smul_of_isUnit {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s V) {u : Γ(X, U)} (hu : IsUnit u) :
    Scheme.Modules.IsFrameOn (u • s) V := by
  intro W hWU hWV
  have hb := hs hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (u • s) =
      X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE hWU).op s :=
    Scheme.Modules.map_smul M (homOfLE hWU) u s
  simp only [e]
  have hu' : IsUnit (X.presheaf.map (homOfLE hWU).op u) := hu.map _
  have : (fun g : Γ(X, W) => g • (X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE hWU).op s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘ (fun g => g * X.presheaf.map (homOfLE hWU).op u) := by
    funext g
    simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact hb.comp (hu'.unit.mulRight_bijective)

variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

theorem oneAddEpsMul_add (f f' : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c (f + f') = oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c f' := by
  simp only [oneAddEpsMul, map_add]
  have he : algebraMap (DualNumber A)
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 DualNumber.eps *
      algebraMap (DualNumber A) _ DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  linear_combination (-((dualNumberThickening A 𝒱 c).map01 f * (dualNumberThickening A 𝒱 c).map01 f')) * he

theorem oneAddEpsMul_zero : oneAddEpsMul A 𝒱 c 0 = 1 := by
  simp [oneAddEpsMul]

theorem oneAddEpsMul_mul_neg (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c (-f) = 1 := by
  rw [← oneAddEpsMul_add, add_neg_cancel, oneAddEpsMul_zero]

theorem oneAddEpsMul_neg_mul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    oneAddEpsMul A 𝒱 c (-f) * oneAddEpsMul A 𝒱 c f = 1 := by
  rw [mul_comm, oneAddEpsMul_mul_neg]

theorem ρ0_one_add_eps_map0 (a : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0
        (1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map0 a) =
      oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) := by
  simp only [oneAddEpsMul, map_add, map_one, map_mul, AlgHom.commutes, HomOver.map01_ρ0]

theorem ρ1_one_add_eps_map1 (a : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1
        (1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map1 a) =
      oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a) := by
  simp only [oneAddEpsMul, map_add, map_one, map_mul, AlgHom.commutes, HomOver.map01_ρ1]

end AlgebraicGeometry.RelPicard

open _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective.AlgebraicGeometry.RelPicard in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    Function.Injective δ := by
  intro x y hxy
  induction x using Quotient.ind with
  | _ M =>
  induction y using Quotient.ind with
  | _ N =>
  obtain ⟨e₀, e₁, f, h₀, h₁, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 M
  obtain ⟨e₀', e₁', f', h₀', h₁', hN⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 N
  rw [hδ M e₀ e₁ f h₀ h₁ hM, hδ N e₀' e₁' f' h₀' h₁' hN] at hxy

  obtain ⟨p, hp⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hxy)
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r0_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul] at hp

  let u₀ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 :=
    1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map0 p.1
  let u₁ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 :=
    1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map1 p.2
  have hεnil : ∀ {S : Type u} [CommRing S] [Algebra (DualNumber A) S] (s : S),
      IsNilpotent (algebraMap (DualNumber A) S DualNumber.eps * s) := by
    intro S _ _ s
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero, zero_mul]
  have hu₀ : IsUnit u₀ := (hεnil _).isUnit_one_add
  have hu₁ : IsUnit u₁ := (hεnil _).isUnit_one_add
  have h₀'' : Scheme.Modules.IsFrameOn ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U0) from u₀) • e₀') (𝒱.pullback c (DualNumber A)).U0 :=
    isFrameOn_smul_of_isUnit h₀' hu₀
  have h₁'' : Scheme.Modules.IsFrameOn ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
      (𝒱.pullback c (DualNumber A)).U1) from u₁) • e₁') (𝒱.pullback c (DualNumber A)).U1 :=
    isFrameOn_smul_of_isUnit h₁' hu₁

  have hr₀ : (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
        (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op
        (show Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0) from u₀) =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
        oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 p.1)) :=
    ρ0_one_add_eps_map0 A 𝒱 c p.1
  have hr₁ : (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
        (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op
        (show Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1) from u₁) =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
        oneAddEpsMul A 𝒱 c (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 p.2)) :=
    ρ1_one_add_eps_map1 A 𝒱 c p.2

  have hN' : N.1.L.presheaf.map (homOfLE inf_le_right).op ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U1) from u₁) • e₁') =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) •
        N.1.L.presheaf.map (homOfLE inf_le_left).op ((show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0) from u₀) • e₀') := by
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, hN, smul_smul, smul_smul, hr₀, hr₁]
    congr 1
    change oneAddEpsMul A 𝒱 c _ * oneAddEpsMul A 𝒱 c f' = oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c _
    rw [← oneAddEpsMul_add, ← oneAddEpsMul_add]
    congr 1
    linear_combination hp

  have flip : ∀ {L : (Limits.pullback c (specMap R (DualNumber A))).Modules}
      (s₀ : Γ(L, (𝒱.pullback c (DualNumber A)).U0)) (s₁ : Γ(L, (𝒱.pullback c (DualNumber A)).U1)),
      L.presheaf.map (homOfLE inf_le_right).op s₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) •
          L.presheaf.map (homOfLE inf_le_left).op s₀ →
      L.presheaf.map (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op s₀ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c (-f)) •
          L.presheaf.map (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op s₁ := by
    intro L s₀ s₁ h
    rw [h, smul_smul]
    have h1 : (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c (-f)) *
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) = 1 :=
      oneAddEpsMul_neg_mul A 𝒱 c f
    rw [h1, one_smul]
  obtain ⟨iso⟩ := Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul
    (𝒱.pullback c (DualNumber A)).sup_eq_top h₀ h₁ h₀'' h₁'' _ (flip e₀ e₁ hM) (flip _ _ hN')
  exact Quotient.sound ⟨iso⟩

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_injective (solution)
