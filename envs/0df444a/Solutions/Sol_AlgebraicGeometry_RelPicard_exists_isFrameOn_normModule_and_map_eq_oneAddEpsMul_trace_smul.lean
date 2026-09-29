-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f02f0440-338e-56ae-8922-09dddf026a19

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
import Theorems.Thm_Algebra_norm_one_add_eps_tmul
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

namespace PicTanF

section RedOverlap

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

theorem exists_ringEquiv_dualNumber_overlap :
    ∃ θ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
      (∀ s, θ ((dualNumberThickening A 𝒱 c).map01 s) = TrivSqZeroExt.inl s) ∧
      θ (algebraMap (DualNumber A) _ DualNumber.eps) = DualNumber.eps ∧
      (∀ z, (θ z).fst = (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).map01 z) := by
  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  exact ⟨dualChartEquiv E01 (ι01 c A 𝒱) hE01, dualChartEquiv_ι E01 (ι01 c A 𝒱) hE01,
    dualChartEquiv_eps E01 (ι01 c A 𝒱) hE01,
    fst_dualChartEquiv E01 (ι01 c A 𝒱) hE01 (r01 c A 𝒱) (r01_ι01 c A 𝒱) (r01_eps c A 𝒱)⟩

end RedOverlap
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

namespace PicTanII

section Lam

variable (P Q : Type u) [CommRing P] [CommRing Q] [Algebra P Q]

noncomputable def lam : DualNumber P ⊗[P] Q →ₐ[P] DualNumber Q :=
  Algebra.TensorProduct.lift
    (DualNumber.lift ⟨(Algebra.ofId P (DualNumber Q), DualNumber.eps), DualNumber.eps_mul_eps,
      fun _ => Commute.all _ _⟩)
    (TrivSqZeroExt.inlAlgHom P Q Q)
    (fun _ _ => Commute.all _ _)

theorem lam_tmul (d : DualNumber P) (q : Q) :
    lam P Q (d ⊗ₜ[P] q) = TrivSqZeroExt.inl (d.fst • q) + TrivSqZeroExt.inr (d.snd • q) := by
  rw [lam, Algebra.TensorProduct.lift_tmul, DualNumber.lift_apply_apply]
  change ((algebraMap P (DualNumber Q) d.fst + algebraMap P (DualNumber Q) d.snd * DualNumber.eps) *
    TrivSqZeroExt.inl q) = _
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', Algebra.smul_def]

theorem lam_one_tmul (q : Q) : lam P Q ((1 : DualNumber P) ⊗ₜ[P] q) = TrivSqZeroExt.inl q := by
  rw [lam_tmul]; ext <;> simp

theorem lam_eps_tmul (q : Q) : lam P Q ((DualNumber.eps : DualNumber P) ⊗ₜ[P] q) = TrivSqZeroExt.inr q := by
  rw [lam_tmul]; ext <;> simp

noncomputable def mu (x : DualNumber Q) : DualNumber P ⊗[P] Q :=
  (1 : DualNumber P) ⊗ₜ[P] x.fst + (DualNumber.eps : DualNumber P) ⊗ₜ[P] x.snd

theorem mu_apply (x : DualNumber Q) :
    mu P Q x = (1 : DualNumber P) ⊗ₜ[P] x.fst + (DualNumber.eps : DualNumber P) ⊗ₜ[P] x.snd := rfl

theorem mu_add (x y : DualNumber Q) : mu P Q (x + y) = mu P Q x + mu P Q y := by
  simp only [mu_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
  abel

theorem lam_mu (x : DualNumber Q) : lam P Q (mu P Q x) = x := by
  rw [mu_apply, map_add, lam_one_tmul, lam_eps_tmul]
  ext <;> simp

theorem mu_lam (y : DualNumber P ⊗[P] Q) : mu P Q (lam P Q y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [mu_apply]
  | tmul d q =>
    rw [lam_tmul, mu_add, mu_apply, mu_apply]
    simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
      TensorProduct.tmul_zero, add_zero, zero_add]
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
  | add y y' hy hy' => rw [map_add, mu_add, hy, hy']

theorem lam_bijective : Function.Bijective (lam P Q) :=
  ⟨fun y y' h => by rw [← mu_lam P Q y, ← mu_lam P Q y', h], fun x => ⟨mu P Q x, lam_mu P Q x⟩⟩

noncomputable def kappa : DualNumber Q ≃+* DualNumber P ⊗[P] Q :=
  (RingEquiv.ofBijective (lam P Q) (lam_bijective P Q)).symm

theorem kappa_apply (x : DualNumber Q) :
    kappa P Q x = (1 : DualNumber P) ⊗ₜ[P] x.fst + (DualNumber.eps : DualNumber P) ⊗ₜ[P] x.snd := by
  apply (kappa P Q).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (lam_mu P Q x).symm

end Lam
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

section Main

variable {P Q Pε Qε : Type u} [CommRing P] [CommRing Q] [CommRing Pε] [CommRing Qε]
  [Algebra P Q] [Module.Free P Q] [Module.Finite P Q] [Algebra Pε Qε]

omit [Module.Free P Q] [Module.Finite P Q] in
theorem one_tmul_algebraMap (a : P) :
    (1 : DualNumber P) ⊗ₜ[P] algebraMap P Q a = (TrivSqZeroExt.inl a : DualNumber P) ⊗ₜ[P] (1 : Q) := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  congr 1
  ext <;> simp

omit [Module.Free P Q] [Module.Finite P Q] in
theorem eps_tmul_algebraMap (b : P) :
    (DualNumber.eps : DualNumber P) ⊗ₜ[P] algebraMap P Q b =
      (DualNumber.eps * TrivSqZeroExt.inl b : DualNumber P) ⊗ₜ[P] (1 : Q) := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  congr 1
  ext <;> simp

theorem norm_one_add_eps_mul_eq
    (ιP : P →+* Pε) (ιQ : Q →+* Qε) (eP : Pε) (eQ : Qε)
    (hι : ∀ p, algebraMap Pε Qε (ιP p) = ιQ (algebraMap P Q p)) (he : algebraMap Pε Qε eP = eQ)
    (θP : Pε ≃+* DualNumber P) (hθP : ∀ p, θP (ιP p) = TrivSqZeroExt.inl p) (hθPe : θP eP = DualNumber.eps)
    (θQ : Qε ≃+* DualNumber Q) (hθQ : ∀ q, θQ (ιQ q) = TrivSqZeroExt.inl q) (hθQe : θQ eQ = DualNumber.eps)
    (g : Q) :
    Algebra.norm Pε (1 + eQ * ιQ g) = 1 + eP * ιP (Algebra.trace P Q g) := by

  have hsplit : ∀ x : Pε, x = ιP (θP x).fst + eP * ιP (θP x).snd := fun x => by
    apply θP.injective
    rw [map_add, map_mul, hθP, hθP, hθPe]
    ext <;> simp
  let e₂ : Qε ≃+* DualNumber P ⊗[P] Q := θQ.trans (kappa P Q)
  have key : Algebra.norm Pε (1 + eQ * ιQ g) = θP.symm (Algebra.norm (DualNumber P) (e₂ (1 + eQ * ιQ g))) := by
    refine Algebra.norm_eq_of_equiv_equiv (A₂ := DualNumber P) (B₂ := DualNumber P ⊗[P] Q) θP e₂ ?_ (1 + eQ * ιQ g)
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change _ = kappa P Q (θQ (algebraMap Pε Qε x))
    have rhs : kappa P Q (θQ (algebraMap Pε Qε x)) =
        (1 : DualNumber P) ⊗ₜ[P] algebraMap P Q (θP x).fst +
          (DualNumber.eps : DualNumber P) ⊗ₜ[P] algebraMap P Q (θP x).snd := by
      conv_lhs => rw [hsplit x]
      rw [map_add, map_mul, hι, hι, he, map_add, map_mul, hθQ, hθQ, hθQe, kappa_apply]
      congr 2 <;> simp
    have eq1 : θP x = TrivSqZeroExt.inl (θP x).fst + DualNumber.eps * TrivSqZeroExt.inl (θP x).snd := by
      ext <;> simp
    rw [rhs, one_tmul_algebraMap, eps_tmul_algebraMap, ← TensorProduct.add_tmul, ← eq1]
    erw [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  have harg : e₂ (1 + eQ * ιQ g) = (1 : DualNumber P ⊗[P] Q) + (DualNumber.eps : DualNumber P) ⊗ₜ[P] g := by
    change kappa P Q (θQ (1 + eQ * ιQ g)) = _
    rw [map_add, map_one, map_mul, hθQe, hθQ, kappa_apply, Algebra.TensorProduct.one_def]
    congr 2 <;> simp
  rw [key, harg, Algebra.norm_one_add_eps_tmul P Q g]
  apply θP.injective
  rw [RingEquiv.apply_symm_apply, map_add, map_one, map_mul, hθPe, hθP]
  ext <;> simp

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

end PicTanII
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

namespace PicTanII

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
  {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover} {𝒲 : C'.TwoAffineOpenCover}

theorem appLE_congr {X Y : Scheme.{u}} {θ θ' : X ⟶ Y} (h : θ = θ') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ θ ⁻¹ᵁ U) (e' : V ≤ θ' ⁻¹ᵁ U) : θ.appLE U V e = θ'.appLE U V e' := by
  subst h; rfl

theorem map01_map01_comm
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    (hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom)
    (p : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    fε.map01 ((dualNumberThickening A 𝒱 c).map01 p) = (dualNumberThickening A 𝒲 c').map01 (f.map01 p) := by
  simp only [HomOver.map01_apply]
  change ((dualNumberThickening A 𝒱 c).hom.appLE _ _ _ ≫ fε.hom.appLE _ _ _).hom p =
    (f.hom.appLE _ _ _ ≫ (dualNumberThickening A 𝒲 c').hom.appLE _ _ _).hom p
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr hcomm]

theorem map01_algebraMap_eps
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A)))) :
    fε.map01 (algebraMap (DualNumber A) _ DualNumber.eps) = algebraMap (DualNumber A) _ DualNumber.eps := by
  have h1 := HomOver.appLE_algebraMap fε fε.inf_le (DualNumber.eps : DualNumber A)
  rw [RingHom.id_apply] at h1
  exact h1

theorem norm_oneAddEpsMul_eq
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    (hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom) :
    letI : Algebra ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 :=
      (f.hom.appLE ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒲.pullback c' A).U0 ⊓ (𝒲.pullback c' A).U1)
        f.inf_le).hom.toAlgebra
    letI : Algebra ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
        ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01 :=
      (fε.hom.appLE ((𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
        ((𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1) fε.inf_le).hom.toAlgebra
    ∀ [Module.Free ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01]
      [Module.Finite ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01]
      (g : ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01),
      Algebra.norm ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
          (oneAddEpsMul A 𝒲 c' g) =
        oneAddEpsMul A 𝒱 c (Algebra.trace ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
          ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 g) := by
  intro _i1 _i2 g
  letI : Algebra ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
      ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 :=
    (f.hom.appLE ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒲.pullback c' A).U0 ⊓ (𝒲.pullback c' A).U1)
      f.inf_le).hom.toAlgebra
  letI : Algebra ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
      ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01 :=
    (fε.hom.appLE ((𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
      ((𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1) fε.inf_le).hom.toAlgebra
  obtain ⟨θP, hθP, hθPe, -⟩ := PicTanF.exists_ringEquiv_dualNumber_overlap c A 𝒱
  obtain ⟨θQ, hθQ, hθQe, -⟩ := PicTanF.exists_ringEquiv_dualNumber_overlap c' A 𝒲
  have hι : ∀ p, algebraMap ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
      ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01
      ((dualNumberThickening A 𝒱 c).map01 p) =
      (dualNumberThickening A 𝒲 c').map01 (algebraMap ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 p) := by
    intro p
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    exact map01_map01_comm f fε hcomm p
  have he : algebraMap ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
      ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01
      (algebraMap (DualNumber A) _ DualNumber.eps) = algebraMap (DualNumber A) _ DualNumber.eps := by
    rw [RingHom.algebraMap_toAlgebra]
    exact map01_algebraMap_eps fε
  have core := norm_one_add_eps_mul_eq
    (P := ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01)
    (Q := ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01)
    (Pε := ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01)
    (Qε := ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01)
    (show ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 →+*
        ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 from
      ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le).hom)
    (show ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 →+*
        ((𝒲.pullback c' (DualNumber A)).cover (pullback.snd c' (specMap R (DualNumber A)))).A01 from
      ((dualNumberThickening A 𝒲 c').hom.appLE _ _ (dualNumberThickening A 𝒲 c').inf_le).hom)
    (algebraMap (DualNumber A) _ DualNumber.eps) (algebraMap (DualNumber A) _ DualNumber.eps)
    hι he θP (fun p => hθP p) hθPe θQ (fun q => hθQ q) hθQe g
  first
    | simpa [oneAddEpsMul] using core
    | (have h' := core; simp [oneAddEpsMul] at h' ⊢; exact h')
    | (have h' := core; simp [oneAddEpsMul] at h'; exact h')
    | exact core

end PicTanII
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

namespace PicTanN2

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry"

theorem seam_aux
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) (𝒰 : X.TwoAffineOpenCover) (W0 W1 : Y.Opens)
    (hW0 : W0 = π ⁻¹ᵁ 𝒰.U0) (hW1 : W1 = π ⁻¹ᵁ 𝒰.U1)
    (e₀ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U0))
    (he₀ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U0),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U1))
    (he₁ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₁ i))
    (L : Y.Modules) (s₀ : Γ(L, W0)) (s₁ : Γ(L, W1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ W0) (hs₁ : Scheme.Modules.IsFrameOn s₁ W1)
    (T : Γ(Y, W0 ⊓ W1))
    (hs : L.presheaf.map (homOfLE inf_le_right).op s₁ = T • L.presheaf.map (homOfLE inf_le_left).op s₀)
    (h : W0 ⊓ W1 ≤ π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) :
    letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, W0 ⊓ W1) := (π.appLE (𝒰.U0 ⊓ 𝒰.U1) (W0 ⊓ W1) h).hom.toAlgebra
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule π d L, 𝒰.U0)) (Ω₁ : Γ(Scheme.Modules.normModule π d L, 𝒰.U1)),
      Scheme.Modules.IsFrameOn Ω₀ 𝒰.U0 ∧ Scheme.Modules.IsFrameOn Ω₁ 𝒰.U1 ∧
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) T • (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by
  subst hW0
  subst hW1

  have happ : (π.appLE (𝒰.U0 ⊓ 𝒰.U1) (π ⁻¹ᵁ 𝒰.U0 ⊓ π ⁻¹ᵁ 𝒰.U1) h).hom = (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Ω₀, Ω₁, h₀, h₁, hΩ⟩ :=
    Scheme.Modules.exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage π d 𝒰 e₀ he₀ e₁ he₁
      L s₀ s₁ hs₀ hs₁ T hs
  refine ⟨Ω₀, Ω₁, h₀, h₁, ?_⟩
  rw [hΩ]
  congr 2
  exact congrArg (fun i => @Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ 𝒰.U0 ⊓ π ⁻¹ᵁ 𝒰.U1) _ _ i)
    (congrArg RingHom.toAlgebra happ.symm)

theorem exists_isFrameOn_normModule_map_eq_norm_smul_of_eq_preimage
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) (𝒰 : X.TwoAffineOpenCover) (𝒲 : Y.TwoAffineOpenCover)
    (hW0 : 𝒲.U0 = π ⁻¹ᵁ 𝒰.U0) (hW1 : 𝒲.U1 = π ⁻¹ᵁ 𝒰.U1)
    (e₀ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U0))
    (he₀ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U0),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U1))
    (he₁ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₁ i))
    (L : Y.Modules) (s₀ : Γ(L, 𝒲.U0)) (s₁ : Γ(L, 𝒲.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ 𝒲.U0) (hs₁ : Scheme.Modules.IsFrameOn s₁ 𝒲.U1)
    (T : Γ(Y, 𝒲.U0 ⊓ 𝒲.U1))
    (hs : L.presheaf.map (homOfLE inf_le_right).op s₁ = T • L.presheaf.map (homOfLE inf_le_left).op s₀)
    (h : 𝒲.U0 ⊓ 𝒲.U1 ≤ π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) :
    letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, 𝒲.U0 ⊓ 𝒲.U1) := (π.appLE (𝒰.U0 ⊓ 𝒰.U1) (𝒲.U0 ⊓ 𝒲.U1) h).hom.toAlgebra
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule π d L, 𝒰.U0)) (Ω₁ : Γ(Scheme.Modules.normModule π d L, 𝒰.U1)),
      Scheme.Modules.IsFrameOn Ω₀ 𝒰.U0 ∧ Scheme.Modules.IsFrameOn Ω₁ 𝒰.U1 ∧
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) T • (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op Ω₀ :=
  seam_aux π d 𝒰 𝒲.U0 𝒲.U1 hW0 hW1 e₀ he₀ e₁ he₁ L s₀ s₁ hs₀ hs₁ T hs h

end PicTanN2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul.PicTanF"

open PicTanII in
theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))

    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom f.hom)

    (hW0 : (𝒲.pullback c' A).U0 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U0)
    (hW1 : (𝒲.pullback c' A).U1 = f.hom ⁻¹ᵁ (𝒱.pullback c A).U1)
    (hW0ε : (𝒲.pullback c' (DualNumber A)).U0 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U0)
    (hW1ε : (𝒲.pullback c' (DualNumber A)).U1 = fε.hom ⁻¹ᵁ (𝒱.pullback c (DualNumber A)).U1)

    [IsFinite fε.hom] [Flat fε.hom] [LocallyOfFinitePresentation fε.hom]
    (d : ℕ) (hd : ∀ x, fε.hom.finrank x = d)

    (e₀ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U0))
    (he₀ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U0),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), (𝒱.pullback c (DualNumber A)).U1))
    (he₁ : ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ (𝒱.pullback c (DualNumber A)).U1),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
          Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e₁ i))

    (L : (Limits.pullback c' (specMap R (DualNumber A))).Modules)
    (s₀ : Γ(L, (𝒲.pullback c' (DualNumber A)).U0)) (s₁ : Γ(L, (𝒲.pullback c' (DualNumber A)).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (𝒲.pullback c' (DualNumber A)).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ (𝒲.pullback c' (DualNumber A)).U1)
    (g : ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01)
    (hs : L.presheaf.map (homOfLE inf_le_right).op s₁ =
      (show Γ(Limits.pullback c' (specMap R (DualNumber A)),
          (𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1)
        from oneAddEpsMul A 𝒲 c' g) • L.presheaf.map (homOfLE inf_le_left).op s₀) :
    letI : Algebra ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 :=
      (f.hom.appLE ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒲.pullback c' A).U0 ⊓ (𝒲.pullback c' A).U1)
        f.inf_le).hom.toAlgebra

    ∀ [Module.Free ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01]
      [Module.Finite ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01],
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U0))
      (Ω₁ : Γ(Scheme.Modules.normModule fε.hom d L, (𝒱.pullback c (DualNumber A)).U1)),
      Scheme.Modules.IsFrameOn Ω₀ (𝒱.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn Ω₁ (𝒱.pullback c (DualNumber A)).U1 ∧
      (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c
            (Algebra.trace ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
              ((𝒲.pullback c' A).cover (pullback.snd c' (specMap R A))).A01 g)) •
        (Scheme.Modules.normModule fε.hom d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by
  intro _i1 _i2
  have hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom := hsq.w
  obtain ⟨Ω₀, Ω₁, h₀, h₁, hΩ⟩ := PicTanN2.exists_isFrameOn_normModule_map_eq_norm_smul_of_eq_preimage fε.hom d
    (𝒱.pullback c (DualNumber A)) (𝒲.pullback c' (DualNumber A)) hW0ε hW1ε e₀ he₀ e₁ he₁ L s₀ s₁ hs₀ hs₁ _ hs fε.inf_le
  refine ⟨Ω₀, Ω₁, h₀, h₁, ?_⟩
  rw [hΩ]
  congr 1
  exact norm_oneAddEpsMul_eq f fε hcomm g

end S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul (solution)
