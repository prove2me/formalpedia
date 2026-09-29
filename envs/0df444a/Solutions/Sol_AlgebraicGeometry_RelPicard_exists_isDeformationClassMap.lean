-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isDeformationClassMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3a4f94c8-6dc6-5d00-999b-dfea554b5371

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped TensorProduct

namespace PicTanE

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

end PicTanE

namespace PicTanE

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

end PicTanE
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.PicTanE"

namespace PicTanE

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

theorem mk_eq_mk_of_isSystem (M : RigKerDualNumber.Carrier c ε A)
    {f f' : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01}
    (hf : IsSystem c ε A 𝒱 M f) (hf' : IsSystem c ε A 𝒱 M f') :
    (Submodule.Quotient.mk f : H1StructureSheaf c A 𝒱) = Submodule.Quotient.mk f' := by
  obtain ⟨e₀, e₁, h₀, h₁, hM⟩ := hf
  obtain ⟨e₀', e₁', h₀', h₁', hM'⟩ := hf'
  obtain ⟨v₀, w₀, hv₀, hw₀, hvw₀⟩ := exists_smul_eq_of_isFrameOn h₀ h₀'
  obtain ⟨v₁, w₁, hv₁, hw₁, hvw₁⟩ := exists_smul_eq_of_isFrameOn h₁ h₁'

  have star : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1 v₁ *
      oneAddEpsMul A 𝒱 c f =
      oneAddEpsMul A 𝒱 c f' * ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0 v₀ := by
    apply smul_left_cancel_of_isFrameOn h₀ inf_le_left inf_le_left

    rw [mul_smul, mul_smul]
    have e1 : M.1.L.presheaf.map (homOfLE (inf_le_right :
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op e₁' =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1 v₁) •
          M.1.L.presheaf.map (homOfLE (inf_le_right :
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op e₁ := by
      rw [← hv₁, Scheme.Modules.map_smul]; rfl
    have e0 : M.1.L.presheaf.map (homOfLE (inf_le_left :
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op e₀' =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0 v₀) •
          M.1.L.presheaf.map (homOfLE (inf_le_left :
            (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤ _)).op e₀ := by
      rw [← hv₀, Scheme.Modules.map_smul]; rfl
    have := hM'
    rw [e1, e0, hM] at this
    exact this

  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  obtain ⟨a₀, b₀, hv₀s⟩ := exists_eq E0 (ι0 c A 𝒱) hE0 v₀
  obtain ⟨a₀', b₀', hw₀s⟩ := exists_eq E0 (ι0 c A 𝒱) hE0 w₀
  obtain ⟨a₁, b₁, hv₁s⟩ := exists_eq E1 (ι1 c A 𝒱) hE1 v₁
  obtain ⟨a₁', b₁', hw₁s⟩ := exists_eq E1 (ι1 c A 𝒱) hE1 w₁
  have hu₀ : a₀ * a₀' = 1 := by
    have h := hvw₀
    rw [hv₀s, hw₀s, mul_eq (ι0 c A 𝒱)] at h
    have h1 : (1 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0) =
        ι0 c A 𝒱 1 + algebraMap (DualNumber A) _ DualNumber.eps * ι0 c A 𝒱 0 := by
      rw [map_one, map_zero, mul_zero, add_zero]
    rw [h1] at h
    exact (unique E0 (ι0 c A 𝒱) hE0 h).1
  have hu₁ : a₁ * a₁' = 1 := by
    have h := hvw₁
    rw [hv₁s, hw₁s, mul_eq (ι1 c A 𝒱)] at h
    have h1 : (1 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1) =
        ι1 c A 𝒱 1 + algebraMap (DualNumber A) _ DualNumber.eps * ι1 c A 𝒱 0 := by
      rw [map_one, map_zero, mul_zero, add_zero]
    rw [h1] at h
    exact (unique E1 (ι1 c A 𝒱) hE1 h).1

  rw [hv₀s, hv₁s, ρ0_split, ρ1_split, oneAddEpsMul_eq, oneAddEpsMul_eq, mul_eq (ι01 c A 𝒱),
    mul_eq (ι01 c A 𝒱)] at star
  obtain ⟨H1, H2⟩ := unique E01 (ι01 c A 𝒱) hE01 star
  simp only [mul_one, one_mul] at H1 H2

  have U0 := congrArg ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 hu₀
  have U1 := congrArg ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 hu₁
  rw [map_mul, map_one] at U0 U1
  refine (Submodule.Quotient.eq _).2 (LinearMap.mem_range.2 ⟨(-(a₀' * b₀), -(a₁' * b₁)), ?_⟩)
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r0_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul]
  simp only [map_neg, map_mul]
  have hQP : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a₀' =
      ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a₁' := by
    linear_combination (-(((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a₀')) * U1
      + (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a₁') * U0
      + (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a₀' *
          ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a₁') * H1
  rw [← hQP]
  linear_combination (-(((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a₀')) * H2
    + (f - f') * U0
    + (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a₀' * f) * H1

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.PicTanE"

end PicTanE
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.PicTanE"

namespace PicTanE

section Construction

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

theorem IsSystem.of_iso {M M' : RigKerDualNumber.Carrier c ε A} (φ : M.1.L ≅ M'.1.L)
    {f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01} (hf : IsSystem c ε A 𝒱 M f) :
    IsSystem c ε A 𝒱 M' f := by
  obtain ⟨e₀, e₁, h₀, h₁, hM⟩ := hf
  refine ⟨φ.hom.app _ e₀, φ.hom.app _ e₁, h₀.map_iso φ, h₁.map_iso φ, ?_⟩
  have nat : ∀ {U V : (Limits.pullback c (specMap R (DualNumber A))).Opens} (i : V ⟶ U) (s : Γ(M.1.L, U)),
      M'.1.L.presheaf.map i.op (φ.hom.app U s) = φ.hom.app V (M.1.L.presheaf.map i.op s) := by
    intro U V i s
    have := (φ.hom.mapPresheaf).naturality i.op
    exact (congrFun (congrArg (fun g => (ConcreteCategory.hom g : Γ(M.1.L, U) → Γ(M'.1.L, V))) this) s).symm
  rw [nat, nat, hM, Scheme.Modules.Hom.app_smul]

open Classical in

noncomputable def δ₀ (M : RigKerDualNumber.Carrier c ε A) : H1StructureSheaf c A 𝒱 :=
  if h : ∃ f, IsSystem c ε A 𝒱 M f then Submodule.Quotient.mk h.choose else 0

theorem δ₀_eq (M : RigKerDualNumber.Carrier c ε A) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01)
    (hf : IsSystem c ε A 𝒱 M f) : δ₀ c ε A 𝒱 M = Submodule.Quotient.mk f := by
  have h : ∃ f, IsSystem c ε A 𝒱 M f := ⟨f, hf⟩
  unfold δ₀
  rw [dif_pos h]
  exact mk_eq_mk_of_isSystem c ε A 𝒱 M h.choose_spec hf

theorem δ₀_congr (M M' : RigKerDualNumber.Carrier c ε A) (h : M ≈ M') : δ₀ c ε A 𝒱 M = δ₀ c ε A 𝒱 M' := by
  have h' : Nonempty (M.1.L ≅ M'.1.L) := h
  obtain ⟨φ⟩ := h'
  by_cases hM : ∃ f, IsSystem c ε A 𝒱 M f
  · obtain ⟨f, hf⟩ := hM
    rw [δ₀_eq c ε A 𝒱 M f hf, δ₀_eq c ε A 𝒱 M' f (hf.of_iso c ε A 𝒱 φ)]
  · have hM' : ¬ ∃ f, IsSystem c ε A 𝒱 M' f := fun ⟨f, hf⟩ => hM ⟨f, hf.of_iso c ε A 𝒱 φ.symm⟩
    unfold δ₀
    rw [dif_neg hM, dif_neg hM']

noncomputable def δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱 :=
  Quotient.lift (δ₀ c ε A 𝒱) (δ₀_congr c ε A 𝒱)

theorem isDeformationClassMap_δ : IsDeformationClassMap c ε A 𝒱 (δ c ε A 𝒱) :=
  fun M e₀ e₁ f h₀ h₁ hM => δ₀_eq c ε A 𝒱 M f ⟨e₀, e₁, h₀, h₁, hM⟩

end Construction
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.PicTanE"

end PicTanE
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap.PicTanE"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) :
    ∃ δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱, IsDeformationClassMap c ε A 𝒱 δ :=
  ⟨PicTanE.δ c ε A 𝒱, PicTanE.isDeformationClassMap_δ c ε A 𝒱⟩

end S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap (solution)
