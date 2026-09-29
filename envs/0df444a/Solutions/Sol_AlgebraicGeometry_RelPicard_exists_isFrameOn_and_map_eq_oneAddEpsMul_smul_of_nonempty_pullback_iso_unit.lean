-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/efe0a16c-438f-5b02-98fa-6a64cbb81d75

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_map_eq_mul_of_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped TensorProduct

namespace PicTanF

section Frames

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

theorem map_homOfLE_refl (s : Γ(M, U)) : M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, M.presheaf.map_id]
  rfl

theorem exists_smul_eq_of_isFrameOn {s s' : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s U)
    (hs' : Scheme.Modules.IsFrameOn s' U) :
    ∃ v w : Γ(X, U), v • s = s' ∧ w • s' = s ∧ v * w = 1 := by
  obtain ⟨v, hv⟩ := (hs (le_refl U) (le_refl U)).2 s'
  obtain ⟨w, hw⟩ := (hs' (le_refl U) (le_refl U)).2 s
  simp only [map_homOfLE_refl] at hv hw
  refine ⟨v, w, hv, hw, ?_⟩
  apply (hs (le_refl U) (le_refl U)).1
  simp only [map_homOfLE_refl]
  rw [mul_comm, mul_smul, hv, hw, one_smul]

theorem smul_left_cancel_of_isFrameOn {V W : X.Opens} {s : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) {g g' : Γ(X, W)}
    (h : g • M.presheaf.map (homOfLE hWU).op s = g' • M.presheaf.map (homOfLE hWU).op s) : g = g' :=
  (hs hWU hWV).1 h

end Frames

end PicTanF

namespace PicTanF

section Split

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {Bε : Type u} [CommRing Bε] [Algebra (DualNumber A) Bε]

noncomputable def coords : DualNumber A ⊗[A] B →ₗ[A] B × B :=
  TensorProduct.lift
    { toFun := fun d => (TrivSqZeroExt.fst d • LinearMap.id (R := A) (M := B)).prod
        (TrivSqZeroExt.snd d • LinearMap.id (R := A) (M := B))
      map_add' := fun d d' => by ext b <;> simp [add_smul]
      map_smul' := fun a d => by ext b <;> simp [mul_smul] }

@[scoped simp] theorem coords_tmul (d : DualNumber A) (b : B) :
    coords (d ⊗ₜ[A] b) = (TrivSqZeroExt.fst d • b, TrivSqZeroExt.snd d • b) := by
  simp [coords]

theorem tmul_eq (d : DualNumber A) (b : B) :
    d ⊗ₜ[A] b = (1 : DualNumber A) ⊗ₜ[A] (TrivSqZeroExt.fst d • b) +
      (DualNumber.eps : DualNumber A) • ((1 : DualNumber A) ⊗ₜ[A] (TrivSqZeroExt.snd d • b)) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.add_tmul]
  congr 1
  ext <;> simp

theorem exists_eq (e : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B → Bε)
    (hι : ∀ s, e ((1 : DualNumber A) ⊗ₜ[A] s) = ι s)
    (z : Bε) : ∃ x y : B, z = ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y := by
  obtain ⟨t, rfl⟩ := e.surjective z
  induction t using TensorProduct.induction_on with
  | zero => refine ⟨0, 0, ?_⟩; rw [← hι, TensorProduct.tmul_zero, map_zero, mul_zero, add_zero]
  | tmul d b =>
    refine ⟨TrivSqZeroExt.fst d • b, TrivSqZeroExt.snd d • b, ?_⟩
    rw [tmul_eq d b, map_add, map_smul, hι, hι]
    congr 1
    exact Algebra.smul_def _ _
  | add t t' ht ht' =>
    obtain ⟨x, y, hx⟩ := ht
    obtain ⟨x', y', hx'⟩ := ht'
    refine ⟨x + x', y + y', ?_⟩
    have hadd : ∀ a b : B, ι (a + b) = ι a + ι b := fun a b => by
      rw [← hι, ← hι, ← hι, TensorProduct.tmul_add, map_add]
    rw [map_add, hx, hx', hadd, hadd]
    ring

theorem unique (e : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B → Bε)
    (hι : ∀ s, e ((1 : DualNumber A) ⊗ₜ[A] s) = ι s) {x y x' y' : B}
    (h : ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y =
      ι x' + algebraMap (DualNumber A) Bε DualNumber.eps * ι y') :
    x = x' ∧ y = y' := by
  have key : ∀ a b : B, e ((1 : DualNumber A) ⊗ₜ[A] a + (DualNumber.eps : DualNumber A) ⊗ₜ[A] b) =
      ι a + algebraMap (DualNumber A) Bε DualNumber.eps * ι b := fun a b => by
    rw [map_add, show (DualNumber.eps : DualNumber A) ⊗ₜ[A] b =
        (DualNumber.eps : DualNumber A) • ((1 : DualNumber A) ⊗ₜ[A] b) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hι, hι, Algebra.smul_def]
  rw [← key, ← key] at h
  have h2 := congrArg coords (e.injective h)
  simp only [map_add, coords_tmul, TrivSqZeroExt.fst_one, one_smul, TrivSqZeroExt.snd_one, zero_smul,
    DualNumber.fst_eps, DualNumber.snd_eps, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq] at h2
  exact h2

theorem mul_eq (ι : B →+* Bε) (x y x' y' : B) :
    (ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y) *
      (ι x' + algebraMap (DualNumber A) Bε DualNumber.eps * ι y') =
    ι (x * x') + algebraMap (DualNumber A) Bε DualNumber.eps * ι (x * y' + x' * y) := by
  have he : algebraMap (DualNumber A) Bε DualNumber.eps * algebraMap (DualNumber A) Bε DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  simp only [map_mul, map_add]
  linear_combination (ι y * ι y') * he

end Split

section Indep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

noncomputable def ι0 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).U0_le).hom
noncomputable def ι1 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).U1_le).hom
noncomputable def ι01 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le).hom

theorem map0_eq (x) : (dualNumberThickening A 𝒱 c).map0 x = ι0 c A 𝒱 x := rfl
theorem map1_eq (x) : (dualNumberThickening A 𝒱 c).map1 x = ι1 c A 𝒱 x := rfl
theorem map01_eq (x) : (dualNumberThickening A 𝒱 c).map01 x = ι01 c A 𝒱 x := rfl

theorem oneAddEpsMul_eq (f) : oneAddEpsMul A 𝒱 c f =
    ι01 c A 𝒱 1 + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 f := by
  rw [map_one]; rfl

theorem exists_splittings :
    ∃ (e0 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0 ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0)
      (e1 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1 ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1)
      (e01 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01),
      (∀ s, e0 ((1 : DualNumber A) ⊗ₜ[A] s) = ι0 c A 𝒱 s) ∧ (∀ s, e1 ((1 : DualNumber A) ⊗ₜ[A] s) = ι1 c A 𝒱 s) ∧
      (∀ s, e01 ((1 : DualNumber A) ⊗ₜ[A] s) = ι01 c A 𝒱 s) := by
  obtain ⟨e0, e1, e01, h0, h1, h01⟩ :=
    Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf 𝒱 c A (DualNumber A)
  exact ⟨e0, e1, e01, fun s => h0 s, fun s => h1 s, fun s => h01 s⟩

end Indep

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF

section Main

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

def IsSystem (M : RigKerDualNumber.Carrier c ε A)
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) : Prop :=
  ∃ (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U1)),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 ∧
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 ∧
    M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) •
        M.1.L.presheaf.map (homOfLE inf_le_left).op e₀

theorem res_U0_eq (v : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0)) :
    (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
      (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op v =
    (show Γ(Limits.pullback c (specMap R (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0 v) := rfl
theorem res_U1_eq (v : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1)) :
    (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
      (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op v =
    (show Γ(Limits.pullback c (specMap R (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1 v) := rfl

theorem ρ0_split (a b : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0
        (ι0 c A 𝒱 a + algebraMap (DualNumber A) _ DualNumber.eps * ι0 c A 𝒱 b) =
      ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) +
        algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 b) := by
  rw [map_add, map_mul, AlgHom.commutes, ← map0_eq, ← map0_eq, ← HomOver.map01_ρ0, ← HomOver.map01_ρ0]
  rfl

theorem ρ1_split (a b : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1
        (ι1 c A 𝒱 a + algebraMap (DualNumber A) _ DualNumber.eps * ι1 c A 𝒱 b) =
      ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a) +
        algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b) := by
  rw [map_add, map_mul, AlgHom.commutes, ← map1_eq, ← map1_eq, ← HomOver.map01_ρ1, ← HomOver.map01_ρ1]
  rfl

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF

section Red

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

noncomputable abbrev red :
    HomOver (TrivSqZeroExt.fstHom R A A).toRingHom (𝒱.pullback c (DualNumber A))
      (pullback.snd c (specMap R (DualNumber A))) (𝒱.pullback c A) (pullback.snd c (specMap R A)) :=
  HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)

theorem red_hom_eq : (red c A 𝒱).hom = RelPicard.baseChangeSnd c (dualNumberReductionOver R A) := rfl

noncomputable def r01 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).inf_le).hom

theorem red_map01_eq (x) : (red c A 𝒱).map01 x = r01 c A 𝒱 x := rfl

theorem red_comp_thickening : (red c A 𝒱).hom ≫ (dualNumberThickening A 𝒱 c).hom = 𝟙 _ := by
  change RelPicard.baseChangeSnd c (LFP.stageHom R (TrivSqZeroExt.fstHom R A A)) ≫
      RelPicard.baseChangeSnd c (LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A))) = 𝟙 _
  rw [RelPicard.baseChangeSnd_comp, ← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem r01_ι01 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    r01 c A 𝒱 (ι01 c A 𝒱 x) = x := by
  change ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le ≫
    (red c A 𝒱).hom.appLE _ _ (red c A 𝒱).inf_le).hom x = x
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ : Limits.pullback c (specMap R A) ⟶ Limits.pullback c (specMap R A)), φ = 𝟙 _ →
      ∀ (e : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ φ ⁻¹ᵁ ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1)),
      (φ.appLE _ _ e).hom x = x := by
    rintro _ rfl e
    have hid : (𝟙 (Limits.pullback c (specMap R A)) : _ ⟶ _).appLE _ _ e = 𝟙 _ := by
      change (𝟙 _ : Limits.pullback c (specMap R A) ⟶ _).app _ ≫ (Limits.pullback c (specMap R A)).presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg (Limits.pullback c (specMap R A)).presheaf.map (Subsingleton.elim _ _)).trans
        ((Limits.pullback c (specMap R A)).presheaf.map_id _)
    rw [hid]
    rfl
  exact key _ (red_comp_thickening c A 𝒱) _

theorem r01_eps : r01 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).inf_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from DualNumber.fst_eps,
    map_zero] at h
  exact h

theorem r01_split (x y : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    r01 c A 𝒱 (ι01 c A 𝒱 x + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 y) = x := by
  rw [map_add, map_mul, r01_ι01, r01_eps, zero_mul, add_zero]

end Red
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF

section DualChart

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {Bε : Type u} [CommRing Bε] [Algebra (DualNumber A) Bε]
  (E : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B →+* Bε)
  (hι : ∀ s, E ((1 : DualNumber A) ⊗ₜ[A] s) = ι s)

noncomputable def ofDualNumber : DualNumber B →+* Bε where
  toFun d := ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι d.snd
  map_one' := by simp
  map_mul' d d' := by
    rw [mul_eq ι]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    congr 3
    ring
  map_zero' := by simp
  map_add' d d' := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]
    ring

theorem ofDualNumber_apply (d : DualNumber B) :
    ofDualNumber (A := A) ι d = ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι d.snd := rfl

include hι in
theorem ofDualNumber_bijective : Function.Bijective (ofDualNumber (A := A) ι) := by
  constructor
  · intro d d' h
    rw [ofDualNumber_apply, ofDualNumber_apply] at h
    obtain ⟨h1, h2⟩ := unique E ι hι h
    exact TrivSqZeroExt.ext h1 h2
  · intro z
    obtain ⟨x, y, rfl⟩ := exists_eq E ι hι z
    exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by rw [ofDualNumber_apply]; simp⟩

noncomputable def dualChartEquiv : Bε ≃+* DualNumber B :=
  (RingEquiv.ofBijective (ofDualNumber (A := A) ι) (ofDualNumber_bijective E ι hι)).symm

theorem dualChartEquiv_symm_apply (d : DualNumber B) :
    (dualChartEquiv E ι hι).symm d = ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι d.snd := rfl

theorem dualChartEquiv_ι (s : B) : dualChartEquiv E ι hι (ι s) = TrivSqZeroExt.inl s := by
  apply (dualChartEquiv E ι hι).symm.injective
  rw [RingEquiv.symm_apply_apply, dualChartEquiv_symm_apply]
  simp

theorem dualChartEquiv_eps :
    dualChartEquiv E ι hι (algebraMap (DualNumber A) Bε DualNumber.eps) = DualNumber.eps := by
  apply (dualChartEquiv E ι hι).symm.injective
  rw [RingEquiv.symm_apply_apply, dualChartEquiv_symm_apply]
  simp

theorem fst_dualChartEquiv (r : Bε →+* B) (hrι : ∀ x, r (ι x) = x)
    (hre : r (algebraMap (DualNumber A) Bε DualNumber.eps) = 0) (z : Bε) :
    (dualChartEquiv E ι hι z).fst = r z := by
  obtain ⟨x, y, rfl⟩ := exists_eq E ι hι z
  rw [map_add, map_mul, dualChartEquiv_ι, dualChartEquiv_ι, dualChartEquiv_eps, map_add, map_mul, hrι, hrι, hre,
    zero_mul, add_zero]
  simp

theorem fstHom_comp_dualChartEquiv (r : Bε →+* B) (hrι : ∀ x, r (ι x) = x)
    (hre : r (algebraMap (DualNumber A) Bε DualNumber.eps) = 0) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualChartEquiv E ι hι).toRingHom = r :=
  RingHom.ext fun z => fst_dualChartEquiv E ι hι r hrι hre z

theorem dualChartEquiv_comp_ι :
    (dualChartEquiv E ι hι).toRingHom.comp ι = (TrivSqZeroExt.inlHom B B : B →+* DualNumber B) :=
  RingHom.ext fun s => dualChartEquiv_ι E ι hι s

end DualChart
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF

section RedCharts

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

noncomputable def r0 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).U0_le).hom

noncomputable def r1 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).U1_le).hom

theorem r0_apply (z) : r0 c A 𝒱 z = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
    ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U0_le).hom z := rfl

theorem r1_apply (z) : r1 c A 𝒱 z = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
    ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U1_le).hom z := rfl

theorem red_thickening_appLE {U : (Limits.pullback c (specMap R A)).Opens}
    {V : (Limits.pullback c (specMap R (DualNumber A))).Opens}
    (h₁ : V ≤ (dualNumberThickening A 𝒱 c).hom ⁻¹ᵁ U)
    (h₂ : U ≤ (red c A 𝒱).hom ⁻¹ᵁ V) (x : Γ(Limits.pullback c (specMap R A), U)) :
    ((red c A 𝒱).hom.appLE V U h₂).hom (((dualNumberThickening A 𝒱 c).hom.appLE U V h₁).hom x) = x := by
  change ((dualNumberThickening A 𝒱 c).hom.appLE U V h₁ ≫ (red c A 𝒱).hom.appLE V U h₂).hom x = x
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ : Limits.pullback c (specMap R A) ⟶ Limits.pullback c (specMap R A)), φ = 𝟙 _ →
      ∀ (e : U ≤ φ ⁻¹ᵁ U), (φ.appLE _ _ e).hom x = x := by
    rintro _ rfl e
    have hid : (𝟙 (Limits.pullback c (specMap R A)) : _ ⟶ _).appLE _ _ e = 𝟙 _ := by
      change (𝟙 _ : Limits.pullback c (specMap R A) ⟶ _).app _ ≫ (Limits.pullback c (specMap R A)).presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg (Limits.pullback c (specMap R A)).presheaf.map (Subsingleton.elim _ _)).trans
        ((Limits.pullback c (specMap R A)).presheaf.map_id _)
    rw [hid]
    rfl
  exact key _ (red_comp_thickening c A 𝒱) _

theorem r0_ι0 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) : r0 c A 𝒱 (ι0 c A 𝒱 x) = x :=
  red_thickening_appLE c A 𝒱 (U := (𝒱.pullback c A).U0) (dualNumberThickening A 𝒱 c).U0_le (red c A 𝒱).U0_le x

theorem r1_ι1 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) : r1 c A 𝒱 (ι1 c A 𝒱 x) = x :=
  red_thickening_appLE c A 𝒱 (U := (𝒱.pullback c A).U1) (dualNumberThickening A 𝒱 c).U1_le (red c A 𝒱).U1_le x

theorem r0_eps : r0 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).U0_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from DualNumber.fst_eps,
    map_zero] at h
  exact h

theorem r1_eps : r1 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).U1_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from DualNumber.fst_eps,
    map_zero] at h
  exact h

theorem exists_ringEquiv_dualNumber_chart0 :
    ∃ θ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0),
      (∀ z, (θ z).fst = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
          ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
          (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U0_le).hom z) ∧
      (∀ s, θ (ι0 c A 𝒱 s) = TrivSqZeroExt.inl s) ∧
      θ (algebraMap (DualNumber A) _ DualNumber.eps) = DualNumber.eps := by
  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  exact ⟨dualChartEquiv E0 (ι0 c A 𝒱) hE0,
    fst_dualChartEquiv E0 (ι0 c A 𝒱) hE0 (r0 c A 𝒱) (r0_ι0 c A 𝒱) (r0_eps c A 𝒱),
    dualChartEquiv_ι E0 (ι0 c A 𝒱) hE0, dualChartEquiv_eps E0 (ι0 c A 𝒱) hE0⟩

theorem exists_ringEquiv_dualNumber_chart1 :
    ∃ θ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1),
      (∀ z, (θ z).fst = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
          ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
          (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U1_le).hom z) ∧
      (∀ s, θ (ι1 c A 𝒱 s) = TrivSqZeroExt.inl s) ∧
      θ (algebraMap (DualNumber A) _ DualNumber.eps) = DualNumber.eps := by
  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  exact ⟨dualChartEquiv E1 (ι1 c A 𝒱) hE1,
    fst_dualChartEquiv E1 (ι1 c A 𝒱) hE1 (r1 c A 𝒱) (r1_ι1 c A 𝒱) (r1_eps c A 𝒱),
    dualChartEquiv_ι E1 (ι1 c A 𝒱) hE1, dualChartEquiv_eps E1 (ι1 c A 𝒱) hE1⟩

end RedCharts
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF

section FrameHelpers

variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}

theorem isFrameOn_smul {s : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s V) {u : Γ(X, U)} (hu : IsUnit u) :
    Scheme.Modules.IsFrameOn (u • s) V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (u • s) =
      X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE hWU).op s := Scheme.Modules.map_smul _ _ _ _
  have : (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op (u • s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘
        (fun g : Γ(X, W) => g * X.presheaf.map (homOfLE hWU).op u) := by
    funext g
    simp only [Function.comp_apply, e, mul_smul]
  rw [this]
  exact (hs hWU hWV).comp (Units.mulRight (hu.map (X.presheaf.map (homOfLE hWU).op).hom).unit).bijective

end FrameHelpers
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF1S

section Yoga

variable {X Y Z : Scheme.{u}}

theorem pullback_comp_unit (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso h.some ≪≫
    Scheme.Modules.pullbackUnitIso g⟩

theorem pullback_congr_unit {f f' : Y ⟶ X} (hf : f = f') (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackCongr hf).app M).symm ≪≫ h.some⟩

theorem unit_of_pullback_iso_inv (α : Y ≅ Z) (N : Y.Modules)
    (h : Nonempty ((Scheme.Modules.pullback α.inv).obj N ≅ SheafOfModules.unit Z.ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    ((Scheme.Modules.pullbackCongr α.hom_inv_id).app N).symm ≪≫
    ((Scheme.Modules.pullbackComp α.hom α.inv).app N).symm ≪≫
    (Scheme.Modules.pullback α.hom).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso α.hom⟩

end Yoga
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

section Chart

variable {X X₀ : Scheme.{u}}

theorem nonempty_pullback_ι_iso_unit (red : X₀ ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hU : IsAffineOpen U) (U₀ : X₀.Opens) (hU₀ : IsAffineOpen U₀) (hle : U₀ ≤ red ⁻¹ᵁ U)
    (h0 : Nonempty ((Scheme.Modules.pullback red).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf))
    (θ : Γ(X, U) ≃+* DualNumber Γ(X₀, U₀))
    (hθ : ∀ z, TrivSqZeroExt.fst (θ z) = (red.appLE U U₀ hle).hom z) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) := by

  let φ : Γ(X, U) ⟶ CommRingCat.of (DualNumber Γ(X₀, U₀)) := CommRingCat.ofHom θ.toRingHom
  let ψ : CommRingCat.of (DualNumber Γ(X₀, U₀)) ⟶ Γ(X, U) := CommRingCat.ofHom θ.symm.toRingHom
  have hφψ : φ ≫ ψ = 𝟙 _ := by apply CommRingCat.hom_ext; exact RingHom.ext fun x => by simp [φ, ψ]
  have hψφ : ψ ≫ φ = 𝟙 _ := by apply CommRingCat.hom_ext; exact RingHom.ext fun x => by simp [φ, ψ]
  let α : (U : Scheme.{u}) ≅ Spec (CommRingCat.of (DualNumber Γ(X₀, U₀))) :=
    hU.isoSpec ≪≫ ⟨Spec.map ψ, Spec.map φ, by rw [← Spec.map_comp, hφψ, Spec.map_id], by rw [← Spec.map_comp, hψφ, Spec.map_id]⟩

  let M' : (Spec (CommRingCat.of (DualNumber Γ(X₀, U₀)))).Modules := (Scheme.Modules.pullback (α.inv ≫ U.ι)).obj M
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback _

  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X₀, U₀) Γ(X₀, U₀) Γ(X₀, U₀)).toRingHom) ≫
      α.inv ≫ U.ι = hU₀.fromSpec ≫ red := by
    have hα : α.inv ≫ U.ι = Spec.map φ ≫ hU.fromSpec := by
      change (Spec.map φ ≫ hU.isoSpec.inv) ≫ U.ι = _
      rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    rw [hα, ← Category.assoc, ← Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec red hU hU₀ hle]
    congr 2
    ext z
    change TrivSqZeroExt.fst (θ z) = _
    exact hθ z

  have h0' : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X₀, U₀) Γ(X₀, U₀) Γ(X₀, U₀)).toRingHom))).obj M' ≅
        SheafOfModules.unit (Spec (CommRingCat.of Γ(X₀, U₀))).ringCatSheaf) := by
    refine ⟨((Scheme.Modules.pullbackComp _ _).app M) ≪≫ ?_⟩
    refine (pullback_congr_unit hsq.symm M ?_).some
    rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
    exact pullback_comp_unit _ _ M (pullback_comp_unit _ _ M h0)

  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction Γ(X₀, U₀) M' hM' h0'
  exact unit_of_pullback_iso_inv α _ ⟨((Scheme.Modules.pullbackComp α.inv U.ι).app M).symm.symm ≪≫ e⟩

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF1S
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

namespace PicTanF1S

section F1

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

private theorem _root_.PicTanF1S.exists_ringEquiv_dualNumber_chart0 :
    ∃ θ : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0) ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0),
      ∀ z, TrivSqZeroExt.fst (θ z) =
        ((RelPicard.baseChangeSnd c (dualNumberReductionOver R A)).appLE
          ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
          (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (dualNumberReductionOver R A)).ge).hom z := by
  obtain ⟨θ, h, -, -⟩ := PicTanF.exists_ringEquiv_dualNumber_chart0 c A 𝒱
  exact ⟨θ, h⟩

p2m_export "PicTanF1S" "exists_ringEquiv_dualNumber_chart0"
private theorem _root_.PicTanF1S.exists_ringEquiv_dualNumber_chart1 :
    ∃ θ : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1) ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1),
      ∀ z, TrivSqZeroExt.fst (θ z) =
        ((RelPicard.baseChangeSnd c (dualNumberReductionOver R A)).appLE
          ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
          (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (dualNumberReductionOver R A)).ge).hom z := by
  obtain ⟨θ, h, -, -⟩ := PicTanF.exists_ringEquiv_dualNumber_chart1 c A 𝒱
  exact ⟨θ, h⟩

p2m_export "PicTanF1S" "exists_ringEquiv_dualNumber_chart1"
end F1
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF1S
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

open PicTanF1S in
theorem F1_chartTrivial
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)
    (M : (Limits.pullback c (specMap R (DualNumber A))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj M ≅ 𝟙_ _)) :
    (∃ e₀ : Γ(M, (𝒱.pullback c (DualNumber A)).U0), Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0) ∧
    (∃ e₁ : Γ(M, (𝒱.pullback c (DualNumber A)).U1), Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1) := by
  have h0' : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj M ≅
      SheafOfModules.unit.{u} (Limits.pullback c (specMap R A)).ringCatSheaf) := h0
  constructor
  · obtain ⟨θ, hθ⟩ := exists_ringEquiv_dualNumber_chart0 c A 𝒱
    obtain ⟨e⟩ := nonempty_pullback_ι_iso_unit (RelPicard.baseChangeSnd c (dualNumberReductionOver R A)) M hM
      ((𝒱.pullback c (DualNumber A)).U0) (𝒱.pullback c (DualNumber A)).isAffineOpen_U0
      ((𝒱.pullback c A).U0) (𝒱.pullback c A).isAffineOpen_U0
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (dualNumberReductionOver R A)).ge h0' θ hθ
    exact Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit _ e
  · obtain ⟨θ, hθ⟩ := exists_ringEquiv_dualNumber_chart1 c A 𝒱
    obtain ⟨e⟩ := nonempty_pullback_ι_iso_unit (RelPicard.baseChangeSnd c (dualNumberReductionOver R A)) M hM
      ((𝒱.pullback c (DualNumber A)).U1) (𝒱.pullback c (DualNumber A)).isAffineOpen_U1
      ((𝒱.pullback c A).U1) (𝒱.pullback c A).isAffineOpen_U1
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (dualNumberReductionOver R A)).ge h0' θ hθ
    exact Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit _ e

namespace PicTanF

section Frames2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

local notation "Xε" => Limits.pullback c (specMap R (DualNumber A))
local notation "XA" => Limits.pullback c (specMap R A)

def IsSystemN (N : (Limits.pullback c (specMap R (DualNumber A))).Modules)
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) : Prop :=
  ∃ (e₀ : Γ(N, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒱.pullback c (DualNumber A)).U1)),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 ∧
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 ∧
    N.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒱 c f) •
        N.presheaf.map (homOfLE inf_le_left).op e₀

theorem exists_isSystemN (N : (Limits.pullback c (specMap R (DualNumber A))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj N ≅ 𝟙_ _)) :
    ∃ f, IsSystemN c A 𝒱 N f := by

  obtain ⟨⟨e₀, he₀⟩, ⟨e₁, he₁⟩⟩ := F1_chartTrivial c A 𝒱 N hN h0

  obtain ⟨t, ht⟩ := (he₀ inf_le_left inf_le_left).2 (N.presheaf.map (homOfLE inf_le_right).op e₁)
  obtain ⟨t', ht'⟩ := (he₁ inf_le_right inf_le_right).2 (N.presheaf.map (homOfLE inf_le_left).op e₀)
  simp only at ht ht'
  have htt' : t' * t = 1 := by
    apply (he₀ inf_le_left inf_le_left).1
    simp only
    rw [mul_smul, ht, ht', one_smul]

  obtain ⟨d₀, d₁, hd₀, hd₁, hd⟩ :=
    Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul 𝒱 c (TrivSqZeroExt.fstHom R A A)
      N e₀ e₁ he₀ he₁ t ht.symm

  have hd' : ((Scheme.Modules.pullback (red c A 𝒱).hom).obj N).presheaf.map (homOfLE inf_le_left).op d₀ =
      (show Γ(XA, (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) from r01 c A 𝒱 t') •
        ((Scheme.Modules.pullback (red c A 𝒱).hom).obj N).presheaf.map (homOfLE inf_le_right).op d₁ := by
    rw [hd, smul_smul]
    change _ = (show Γ(XA, (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) from r01 c A 𝒱 t' * r01 c A 𝒱 t) • _
    rw [← map_mul, htt', map_one]
    exact (one_smul _ _).symm

  have eT : (Scheme.Modules.pullback (red c A 𝒱).hom).obj N ≅ 𝟙_ (Limits.pullback c (specMap R A)).Modules := h0.some
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Scheme.Modules.IsFrameOn.exists_isUnit_map_eq_mul_of_iso_tensorUnit hd₀ hd₁ _ hd' eT
  obtain ⟨a', haa'⟩ := ha.exists_right_inv
  obtain ⟨b', hbb'⟩ := hb.exists_right_inv

  change ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a = r01 c A 𝒱 t' * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b at hab

  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  obtain ⟨x, y, hts⟩ := exists_eq E01 (ι01 c A 𝒱) hE01 t
  have hx : r01 c A 𝒱 t = x := by rw [hts, r01_split]
  have hone : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b' * x * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a = 1 := by
    have h1 : x * r01 c A 𝒱 t' = 1 := by rw [← hx, ← map_mul, mul_comm, htt', map_one]
    rw [hab, mul_assoc, ← mul_assoc x, h1, one_mul, ← map_mul, mul_comm b', hbb', map_one]

  refine ⟨((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b' * y * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a,
    (show Γ(Xε, (𝒱.pullback c (DualNumber A)).U0) from ι0 c A 𝒱 a') • e₀,
    (show Γ(Xε, (𝒱.pullback c (DualNumber A)).U1) from ι1 c A 𝒱 b') • e₁,
    isFrameOn_smul he₀ ((IsUnit.of_mul_eq_one_right a haa').map (ι0 c A 𝒱)),
    isFrameOn_smul he₁ ((IsUnit.of_mul_eq_one_right b hbb').map (ι1 c A 𝒱)), ?_⟩
  rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, res_U0_eq, res_U1_eq, ← ht, smul_smul, smul_smul]
  congr 1

  change ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1 (ι1 c A 𝒱 b') * (show ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 from t) =
    oneAddEpsMul A 𝒱 c _ * ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0 (ι0 c A 𝒱 a')
  rw [← map1_eq, ← map0_eq, ← HomOver.map01_ρ1, ← HomOver.map01_ρ0, map01_eq, map01_eq, oneAddEpsMul_eq, hts]

  have hι : ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a') * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) = 1 := by
    rw [← map_mul, ← map_mul, mul_comm a', haa', map_one, map_one]
  calc ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b') * (ι01 c A 𝒱 x + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 y)
      = ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b') * (ι01 c A 𝒱 x + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 y) *
          (ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a')) := by rw [mul_comm (ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a)), hι, mul_one]
    _ = (ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b' * x * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) +
          algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b' * y * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a)) *
          ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a') := by simp only [map_mul]; ring
    _ = (ι01 c A 𝒱 1 + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 b' * y * ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a)) *
          ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a') := by rw [hone]

end Frames2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit.PicTanF"

open PicTanF in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒲 : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (hN : Scheme.Modules.IsInvertible N)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R A))).obj N ≅
      SheafOfModules.unit.{u} (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)).ringCatSheaf)) :
    ∃ (e₀ : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
      (g : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01),
      Scheme.Modules.IsFrameOn e₀ (𝒲.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn e₁ (𝒲.pullback c (DualNumber A)).U1 ∧
      N.presheaf.map (homOfLE inf_le_right).op e₁ =
        (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
            (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A 𝒲 c g) •
          N.presheaf.map (homOfLE inf_le_left).op e₀ := by
  obtain ⟨g, e₀, e₁, h₀, h₁, h⟩ := PicTanF.exists_isSystemN c A 𝒲 N hN h0
  exact ⟨e₀, e₁, g, h₀, h₁, h⟩

end S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit (solution)
