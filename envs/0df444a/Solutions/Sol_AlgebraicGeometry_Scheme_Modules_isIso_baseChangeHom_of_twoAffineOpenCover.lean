-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2959f176-35dd-598a-8b91-4145aa8b946e

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry Opposite TopologicalSpace TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pushforward Scheme.Modules.pullback tilde.adjunction Scheme.Hom moduleSpecΓFunctor Spec Spec.map isIso_fromTildeΓ_iff Scheme.Modules.mapPresheaf_app Scheme pullbackSpecIso Scheme.Modules.fromTildeΓ Flat modulesSpecToSheaf Scheme.Modules.pullbackPushforwardAdjunction tilde.functor IsAffineOpen Scheme.Modules tilde Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.Modules.baseChangeHom tilde.pullbackSpecIso Scheme.Modules.IsInvertible Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.mapPresheaf_app Modules.fromTildeΓ Modules.pullbackPushforwardAdjunction Modules Opens ΓSpecIso Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.specMap Modules.baseChangeHom Modules.IsInvertible Modules.isIso_baseChangeHom_iff_of_isPullback"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom mapPresheaf_app fromTildeΓ pullbackPushforwardAdjunction map_smul baseChangeHom unit_app_app_comp_baseChangeHom_app IsInvertible isIso_fromTildeGamma_pushforward_of_locallyTrivial projective_sections_of_locallyTrivial exists_linearEquiv_sections_baseChange_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma isIso_baseChangeHom_iff_of_isPullback"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem isIso_of_isIso_moduleSpecΓFunctor_map {A : Type u} [CommRing A]
    {M N : (Spec (CommRingCat.of A)).Modules}
    (hM : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) M)) (hN : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) N))
    (f : M ⟶ N) (hf : IsIso ((moduleSpecΓFunctor (R := .of A)).map f)) : IsIso f := by

  have hnat : (tilde.functor (.of A)).map ((moduleSpecΓFunctor (R := .of A)).map f) ≫
      Scheme.Modules.fromTildeΓ (R := .of A) N = Scheme.Modules.fromTildeΓ (R := .of A) M ≫ f :=
    (tilde.adjunction (R := .of A)).counit.naturality f
  let e : M ≅ N := (@asIso _ _ _ _ _ hM).symm ≪≫ (tilde.functor (.of A)).mapIso (@asIso _ _ _ _ _ hf) ≪≫
    @asIso _ _ _ _ _ hN
  have he : e.hom = f := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv]
    exact (@IsIso.inv_comp_eq _ _ _ _ _ _ hM _ _).mpr hnat
  rw [← he]
  infer_instance

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "mapPresheaf app" end Hom
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_presheaf_map {X : Scheme.{u}} {F G : X.Modules} (η : F ⟶ G) {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)) :
    (η.app V).hom (F.presheaf.map i.op s) = G.presheaf.map i.op ((η.app U).hom s) := by
  have h := η.mapPresheaf.naturality i.op
  simp only [Scheme.Modules.mapPresheaf_app] at h
  simpa [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h s

section resM
variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev resM {W W' : X.Opens} (h : W' ≤ W) : Γ(M, W) → Γ(M, W') :=
  fun s => M.presheaf.map (homOfLE h).op s

variable {M}

lemma map_eq_resM {W W' : X.Opens} (i : W' ⟶ W) (s : Γ(M, W)) : M.presheaf.map i.op s = resM M i.le s := by
  rw [Subsingleton.elim i (homOfLE i.le)]

lemma resM_resM {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (s : Γ(M, W)) :
    resM M h' (resM M h s) = resM M (h'.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE h').op) s = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma resM_refl {W : X.Opens} (h : W ≤ W) (s : Γ(M, W)) : resM M h s = s := by
  change M.presheaf.map (homOfLE h).op s = s
  rw [Subsingleton.elim (homOfLE h) (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

lemma presheaf_map_map_eq (M : X.Modules) {U V W : X.Opens} (a : V ⟶ U) (b : W ⟶ V) (c : W ⟶ U)
    (s : Γ(M, U)) : M.presheaf.map b.op (M.presheaf.map a.op s) = M.presheaf.map c.op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (b ≫ a) c]

end resM

private theorem _root_.Module.Flat.prod_of_flat {R : Type u} [CommRing R] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have hsq : ∀ x, TensorProduct.prodRight R R Q M N (f.rTensor (M × N) x) =
      ((f.rTensor M).prodMap (f.rTensor N)) (TensorProduct.prodRight R R P M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p mn => simp [LinearMap.rTensor_tmul, LinearMap.prodMap_apply, TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have h := congrArg (TensorProduct.prodRight R R Q M N) hxy
  rw [hsq, hsq] at h
  have hinj : Function.Injective ((f.rTensor M).prodMap (f.rTensor N)) := h1.prodMap h2
  exact (TensorProduct.prodRight R R P M N).injective (hinj h)

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.Module.Flat.prod_of_flat" "Module.Flat.prod_of_flat"

section bridge
variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']

noncomputable def restrictScalarsSelfEquiv :
    A' ≃ₗ[A'] ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A')) :=
  LinearEquiv.refl A' A'

scoped instance : IsScalarTower A A'
    ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A')) :=
  ⟨fun a a' x => by
    change (a • a') • x = ((algebraMap A A') a) • (a' • x)
    rw [Algebra.smul_def, mul_smul]⟩

noncomputable def extendScalarsAlgebraMapEquiv (N : ModuleCat.{u} A) :
    (A' ⊗[A] N) ≃ₗ[A'] (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N :=
  TensorProduct.AlgebraTensorModule.congr (restrictScalarsSelfEquiv (A := A) A') (LinearEquiv.refl A N)

theorem extendScalarsAlgebraMapEquiv_tmul (N : ModuleCat.{u} A) (a' : A') (n : N) :
    extendScalarsAlgebraMapEquiv (A := A) A' N (a' ⊗ₜ n) =
      ((a' : ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A'))) ⊗ₜ[A] n :
        (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj N) := by
  rfl

end bridge

section main

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

noncomputable abbrev globalSectionsModule (F : X.Modules) : ModuleCat A :=
  ((modulesSpecToSheaf (R := .of A)).obj ((Scheme.Modules.pushforward π).obj F)).presheaf.obj (op ⊤)

noncomputable def globalSectionsEquiv (F : X.Modules) :
    letI := moduleSectionsOfHom π F ⊤
    globalSectionsModule π F ≃ₗ[A] Γ(F, ⊤) :=
  letI := moduleSectionsOfHom π F ⊤
  { toFun := fun s => (show Γ(F, ⊤) from s)
    invFun := fun s => (show globalSectionsModule π F from s)
    map_add' := fun _ _ => rfl
    map_smul' := fun a s => by
      show (show Γ(X, ⊤) from ((π.app ⊤).hom ((((Spec (CommRingCat.of A)).presheaf.map
          (homOfLE (le_top (a := ⊤))).op).hom) ((Scheme.ΓSpecIso (.of A)).inv.hom a)))) • (show Γ(F, ⊤) from s) =
        ((π.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) • (show Γ(F, ⊤) from s)
      congr 1
      have h1 : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤)) = 𝟙 _ :=
        Subsingleton.elim _ _
      have e1 : (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of A)).Opens)))).op = 𝟙 _ := by
        rw [h1, op_id, CategoryTheory.Functor.map_id]
      have e2 : π.appLE ⊤ ⊤ le_top = π.app ⊤ := Scheme.Hom.appLE_eq_app _
      rw [e2, e1]
      rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

noncomputable abbrev ΓMod (N : (Spec (CommRingCat.of A)).Modules) : ModuleCat A :=
  (moduleSpecΓFunctor (R := .of A)).obj N

variable (A' : Type u) [CommRing A'] [Algebra A A']

noncomputable abbrev φA : CommRingCat.of A ⟶ CommRingCat.of A' := CommRingCat.ofHom (algebraMap A A')

lemma specMap_eq : Scheme.TwoAffineOpenCover.specMap A A' = Spec.map (φA (A := A) A') := rfl

theorem exists_linearEquiv_tensor_ΓMod_pullback (N : (Spec (CommRingCat.of A)).Modules)
    (hN : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) N)) :
    ∃ σ : A' ⊗[A] (ΓMod N) ≃ₗ[A']
        ((moduleSpecΓFunctor (R := .of A')).obj ((pullback (Spec.map (φA (A := A) A'))).obj N)),
      ∀ m : ΓMod N, σ ((1 : A') ⊗ₜ[A] m) =
        ((((pullbackPushforwardAdjunction (Spec.map (φA (A := A) A'))).unit.app N).app ⊤).hom m :) := by
  have hiso := isIso_baseChange_sections_of_isIso_fromTildeGamma (φA (A := A) A') N hN
  let τ := @asIso _ _ _ _ _ hiso
  refine ⟨(extendScalarsAlgebraMapEquiv (A := A) A' (ΓMod N)).trans τ.toLinearEquiv, fun m => ?_⟩
  rw [LinearEquiv.trans_apply, extendScalarsAlgebraMapEquiv_tmul]
  refine Eq.trans (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply τ.hom m).symm ?_
  simp only [τ, asIso_hom, Equiv.apply_symm_apply]
  rfl

theorem exists_linearEquiv_ker_baseChange_cechDiff (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    (Function.Surjective ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).obj F)).cechDiff →
      Function.Surjective ((𝒱.sectionsOf π F).cechDiff.baseChange A')) ∧
    ∃ κ : LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A') ≃ₗ[A']
        LinearMap.ker ((𝒱.pullback π A').sectionsOf
          (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A A'))
          ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).obj F)).cechDiff,
      ∀ (x : (𝒱.sectionsOf π F).M0 × (𝒱.sectionsOf π F).M1)
        (hx : (1 : A') ⊗ₜ[A] x ∈ LinearMap.ker ((𝒱.sectionsOf π F).cechDiff.baseChange A')),
        (κ ⟨(1 : A') ⊗ₜ[A] x, hx⟩).1 =
          ((((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app 𝒱.U0).hom x.1,
           (((Scheme.Modules.pullbackPushforwardAdjunction
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A A'))).unit.app F).app 𝒱.U1).hom x.2) := by
  classical
  set S := 𝒱.sectionsOf π F with hS
  set fK := Limits.pullback.fst π (specMap A A') with hfK
  set FK : (Limits.pullback π (specMap A A')).Modules := (Scheme.Modules.pullback fK).obj F with hFK
  set SK := (𝒱.pullback π A').sectionsOf (Limits.pullback.snd π (specMap A A')) FK with hSK
  let η := (Scheme.Modules.pullbackPushforwardAdjunction fK).unit.app F
  letI := moduleSectionsOfHom π F 𝒱.U0
  letI := moduleSectionsOfHom π F 𝒱.U1
  letI := moduleSectionsOfHom π F (𝒱.U0 ⊓ 𝒱.U1)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U0)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ 𝒱.U1)
  letI := moduleSectionsOfHom (Limits.pullback.snd π (specMap A A')) FK (fK ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  obtain ⟨ε0, hε0⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U0
    𝒱.isAffineOpen_U0 A'
  obtain ⟨ε1, hε1⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U1
    𝒱.isAffineOpen_U1 A'
  obtain ⟨ε01, hε01⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv (𝒱.U0 ⊓ 𝒱.U1)
    𝒱.isAffineOpen_inf A'
  let e0 : A' ⊗[A] (S.M0 × S.M1) ≃ₗ[A'] (SK.M0 × SK.M1) :=
    (TensorProduct.prodRight A A' A' S.M0 S.M1).trans (ε0.prodCongr ε1)
  let e1 : A' ⊗[A] S.M01 ≃ₗ[A'] SK.M01 := ε01
  have hr0 : ∀ s : S.M0, SK.r0 (ε0 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r0 s)) := by
    intro s
    rw [hε0, hε01]
    exact (Hom.app_presheaf_map η (homOfLE inf_le_left) s).symm
  have hr1 : ∀ s : S.M1, SK.r1 (ε1 ((1 : A') ⊗ₜ[A] s)) = ε01 ((1 : A') ⊗ₜ[A] (S.r1 s)) := by
    intro s
    rw [hε1, hε01]
    exact (Hom.app_presheaf_map η (homOfLE inf_le_right) s).symm
  have he0 : ∀ (s0 : S.M0) (s1 : S.M1),
      e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = (ε0 ((1 : A') ⊗ₜ[A] s0), ε1 ((1 : A') ⊗ₜ[A] s1)) := by
    intro s0 s1
    simp only [e0, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
    rfl
  have hcomm : SK.cechDiff ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ S.cechDiff.baseChange A' := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul k x => ?_
    obtain ⟨s0, s1⟩ := x
    have hk : ∀ {N : Type u} [AddCommGroup N] [Module A N] (y : N),
        (k ⊗ₜ[A] y : A' ⊗[A] N) = k • ((1 : A') ⊗ₜ[A] y) := fun y => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hk, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
    congr 1
    have he1 : ∀ y, e1 y = ε01 y := fun _ => rfl
    rw [he0, he1, LinearMap.baseChange_tmul, TwoChartCech.Sections.cechDiff_apply,
      TwoChartCech.Sections.cechDiff_apply]
    dsimp only
    rw [TensorProduct.tmul_sub, hr0, hr1]
    exact (map_sub ε01 _ _).symm

  have hmem : ∀ y, y ∈ LinearMap.ker (S.cechDiff.baseChange A') ↔ e0 y ∈ LinearMap.ker SK.cechDiff := by
    intro y
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
      congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
    rw [h1]
    exact ⟨fun h => by rw [h, map_zero], fun h => e1.injective (by rw [h, map_zero])⟩
  let κ₀ : LinearMap.ker (S.cechDiff.baseChange A') →ₗ[A'] LinearMap.ker SK.cechDiff :=
    (e0.toLinearMap ∘ₗ (LinearMap.ker (S.cechDiff.baseChange A')).subtype).codRestrict _
      (fun y => (hmem y.1).mp y.2)
  have hκ₀ : Function.Bijective κ₀ := by
    refine ⟨fun y z h => Subtype.ext (e0.injective (congrArg Subtype.val h)), fun z => ?_⟩
    refine ⟨⟨e0.symm z.1, (hmem _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
    exact Subtype.ext (e0.apply_symm_apply z.1)
  refine ⟨fun hs => ?_, LinearEquiv.ofBijective κ₀ hκ₀, fun x hx => ?_⟩
  · have hd : ∀ y, S.cechDiff.baseChange A' y = e1.symm (SK.cechDiff (e0 y)) := fun y => by
      have h1 : SK.cechDiff (e0 y) = e1 (S.cechDiff.baseChange A' y) :=
        congrArg (fun φ : _ →ₗ[A'] _ => φ y) hcomm
      rw [h1, LinearEquiv.symm_apply_apply]
    intro z
    obtain ⟨w, hw⟩ := hs (e1 z)
    exact ⟨e0.symm w, by rw [hd, LinearEquiv.apply_symm_apply, hw, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨s0, s1⟩ := x
  rw [LinearEquiv.ofBijective_apply]
  change e0 ((1 : A') ⊗ₜ[A] (s0, s1)) = _
  rw [he0, hε0, hε1]
  rfl

set_option maxHeartbeats 3200000 in

theorem isIso_fromTildeΓ_pullback_pushforward (F : X.Modules)
    (hF : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) ((pushforward π).obj F))) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of A')
      ((pullback (Spec.map (φA (A := A) A'))).obj ((pushforward π).obj F))) := by
  rw [isIso_fromTildeΓ_iff]
  let H : ModuleCat A := ΓMod ((pushforward π).obj F)
  let e1 : tilde H ≅ (pushforward π).obj F := @asIso _ _ _ _ _ hF
  let e2 : (pullback (Spec.map (φA (A := A) A'))).obj (tilde H) ≅
      tilde ((ModuleCat.extendScalars (φA (A := A) A').hom).obj H) := tilde.pullbackSpecIso (φA (A := A) A') H
  refine ⟨(ModuleCat.extendScalars (φA (A := A) A').hom).obj H, ⟨?_⟩⟩
  exact e2.symm ≪≫ (pullback (Spec.map (φA (A := A) A'))).mapIso e1

set_option maxHeartbeats 6400000 in

theorem isIso_baseChangeHom_of_twoAffineOpenCover_aux
    [IsNoetherianRing A] [Flat π] (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    IsIso (Scheme.Modules.baseChangeHom
      (Limits.pullback.condition (f := π) (g := Scheme.TwoAffineOpenCover.specMap A A')) F) := by
  set ψ := Scheme.TwoAffineOpenCover.specMap A A' with hψ
  set fA := Limits.pullback.fst π ψ
  set sA := Limits.pullback.snd π ψ
  set FA := (Scheme.Modules.pullback fA).obj F

  have hsrc : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((pullback ψ).obj ((pushforward π).obj F))) :=
    isIso_fromTildeΓ_pullback_pushforward π A' F
      (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)

  have htrivA : ∀ x : (Limits.pullback π ψ : Scheme.{u}), ∃ (V : (Limits.pullback π ψ).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj FA ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :=
    ((⟨htriv⟩ : Scheme.Modules.IsInvertible F).pullback fA).exists_trivialization
  have htgt : IsIso (Scheme.Modules.fromTildeΓ (R := .of A') ((pushforward sA).obj FA)) :=
    isIso_fromTildeGamma_pushforward_of_locallyTrivial sA (𝒱.pullback π A') FA htrivA

  have key : IsIso ((moduleSpecΓFunctor (R := .of A')).map
      (Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F)) := by
    classical
    set β := Scheme.Modules.baseChangeHom (Limits.pullback.condition (f := π) (g := ψ)) F with hβ
    set S := 𝒱.sectionsOf π F with hS
    set SA := (𝒱.pullback π A').sectionsOf sA FA with hSA

    have flat_sections : ∀ (U : X.Opens), IsAffineOpen U →
        letI := moduleSectionsOfHom π F U; Module.Flat A Γ(F, U) := by
      intro U hU
      letI := algebraOfHom π U
      letI := moduleSectionsOfHom π F U
      haveI : IsScalarTower A Γ(X, U) Γ(F, U) := isScalarTower_sections π F U
      haveI : Module.Flat A Γ(X, U) := flat_sections_of_flat π U hU
      haveI : Module.Projective Γ(X, U) Γ(F, U) := projective_sections_of_locallyTrivial F htriv ⟨U, hU⟩
      exact Module.Flat.trans A Γ(X, U) Γ(F, U)
    haveI : Module.Flat A S.M0 := flat_sections 𝒱.U0 𝒱.isAffineOpen_U0
    haveI : Module.Flat A S.M1 := flat_sections 𝒱.U1 𝒱.isAffineOpen_U1
    haveI : Module.Flat A S.M01 := flat_sections (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
    haveI : Module.Flat A (S.M0 × S.M1) := Module.Flat.prod_of_flat S.M0 S.M1
    haveI : Module.Finite A (LinearMap.ker S.cechDiff) := hfin.1
    haveI : Module.Finite A (S.M01 ⧸ LinearMap.range S.cechDiff) := hfin.2

    have hsq : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (S.cechDiff.baseChange K) := by
      intro K _ _
      refine (exists_linearEquiv_ker_baseChange_cechDiff π K 𝒱 F htriv).1 ?_
      rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
      exact hfib K
    obtain ⟨-, hbc, -⟩ := TwoChartCech.Mumford.projective_ker_of_fibre_surjective S.cechDiff hsq
    have hb : Function.Bijective (TwoChartCech.kerBaseChangeHom S.cechDiff A') := hbc A'

    obtain ⟨-, κ, hκ⟩ := exists_linearEquiv_ker_baseChange_cechDiff π A' 𝒱 F htriv
    obtain ⟨σ, hσ⟩ := exists_linearEquiv_tensor_ΓMod_pullback A' ((pushforward π).obj F)
      (isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv)
    letI := moduleSectionsOfHom π F ⊤
    letI := moduleSectionsOfHom sA FA ⊤
    obtain ⟨eX, heX⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 π F
    obtain ⟨eP, heP⟩ := exists_linearEquiv_sectionsOf_H0 (𝒱.pullback π A') sA FA
    let gX := globalSectionsEquiv π F
    let gP := globalSectionsEquiv sA FA

    let Γβ : ΓMod ((pullback ψ).obj ((pushforward π).obj F)) →ₗ[A'] ΓMod ((pushforward sA).obj FA) :=
      ((moduleSpecΓFunctor (R := .of A')).map β).hom

    let L₁ : A' ⊗[A] (ΓMod ((pushforward π).obj F)) →ₗ[A'] LinearMap.ker SA.cechDiff :=
      eP.toLinearMap ∘ₗ gP.toLinearMap ∘ₗ Γβ ∘ₗ σ.toLinearMap
    let L₂ : A' ⊗[A] (ΓMod ((pushforward π).obj F)) →ₗ[A'] LinearMap.ker SA.cechDiff :=
      κ.toLinearMap ∘ₗ TwoChartCech.kerBaseChangeHom S.cechDiff A' ∘ₗ
        (LinearEquiv.baseChange A A' _ _ (gX.trans eX)).toLinearMap
    have hL : L₁ = L₂ := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul a' m => ?_
      have hk : (a' ⊗ₜ[A] m : A' ⊗[A] (ΓMod ((pushforward π).obj F))) = a' • ((1 : A') ⊗ₜ[A] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, _root_.map_smul, _root_.map_smul]
      congr 1
      apply Subtype.ext

      have hR : (L₂ ((1 : A') ⊗ₜ[A] m)).1 =
          ((((pullbackPushforwardAdjunction fA).unit.app F).app 𝒱.U0).hom
              (F.presheaf.map (homOfLE (le_top (a := 𝒱.U0))).op m),
           (((pullbackPushforwardAdjunction fA).unit.app F).app 𝒱.U1).hom
              (F.presheaf.map (homOfLE (le_top (a := 𝒱.U1))).op m)) := by
        have hx := heX (gX m)
        have hmem : (1 : A') ⊗ₜ[A] ((eX (gX m) : S.M0 × S.M1)) ∈ LinearMap.ker (S.cechDiff.baseChange A') := by
          rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, (LinearMap.mem_ker).mp (eX (gX m)).2,
            TensorProduct.tmul_zero]
        have hkbc : TwoChartCech.kerBaseChangeHom S.cechDiff A' ((1 : A') ⊗ₜ[A] (eX (gX m))) =
            ⟨(1 : A') ⊗ₜ[A] ((eX (gX m) : S.M0 × S.M1)), hmem⟩ := by
          apply Subtype.ext
          rw [TwoChartCech.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul]
          rfl
        simp only [L₂, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        erw [LinearEquiv.baseChange_tmul]
        rw [LinearEquiv.trans_apply, hkbc, hκ _ hmem]
        rw [hx]
        rfl
      have hLft : (L₁ ((1 : A') ⊗ₜ[A] m)).1 =
          ((((pullbackPushforwardAdjunction fA).unit.app F).app 𝒱.U0).hom
              (F.presheaf.map (homOfLE (le_top (a := 𝒱.U0))).op m),
           (((pullbackPushforwardAdjunction fA).unit.app F).app 𝒱.U1).hom
              (F.presheaf.map (homOfLE (le_top (a := 𝒱.U1))).op m)) := by
        simp only [L₁, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [hσ m]

        have h4 := unit_app_app_comp_baseChangeHom_app π ψ sA fA
          (Limits.pullback.condition (f := π) (g := ψ)) F ⊤
        have h4m := ConcreteCategory.congr_hom h4 m
        simp only [CategoryTheory.comp_apply] at h4m

        rw [heP]
        change (resM FA (le_top (a := fA ⁻¹ᵁ 𝒱.U0)) (Γβ _), resM FA (le_top (a := fA ⁻¹ᵁ 𝒱.U1)) (Γβ _)) = _
        have hΓβ : ∀ z, Γβ z = ((β.app ⊤).hom z :) := fun _ => rfl
        rw [hΓβ]
        erw [h4m]
        dsimp only [resM]
        erw [Hom.app_presheaf_map ((pullbackPushforwardAdjunction fA).unit.app F) (homOfLE (le_top (a := 𝒱.U0))) m,
          Hom.app_presheaf_map ((pullbackPushforwardAdjunction fA).unit.app F) (homOfLE (le_top (a := 𝒱.U1))) m]
        exact Prod.ext (presheaf_map_map_eq _ _ _ _ _) (presheaf_map_map_eq _ _ _ _ _)
      exact hLft.trans hR.symm

    have h2 : Function.Bijective L₂ :=
      κ.bijective.comp (hb.comp (LinearEquiv.baseChange A A' _ _ (gX.trans eX)).bijective)
    have hΓβ' : (Γβ : _ → _) = gP.symm ∘ eP.symm ∘ L₂ ∘ σ.symm := by
      funext x
      rw [← hL]
      simp only [L₁, Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
      rfl
    have hbij : Function.Bijective Γβ := by
      rw [hΓβ']
      exact gP.symm.bijective.comp (eP.symm.bijective.comp (h2.comp σ.symm.bijective))
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_isIso_moduleSpecΓFunctor_map hsrc htgt _ key

end main

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry"

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1)
    (A' : Type u) [CommRing A'] [Algebra A A'] {X' : Scheme.{u}} (π' : X' ⟶ Spec (.of A')) (g' : X' ⟶ X)
    (hcart : IsPullback g' π' π (Scheme.TwoAffineOpenCover.specMap A A')) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) :=
  (Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback hcart
    (IsPullback.of_hasPullback π (Scheme.TwoAffineOpenCover.specMap A A')) F).mpr
    (isIso_baseChangeHom_of_twoAffineOpenCover_aux π A' 𝒱 F htriv hfin hfib)

#print axioms solution

end S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover (solution)
