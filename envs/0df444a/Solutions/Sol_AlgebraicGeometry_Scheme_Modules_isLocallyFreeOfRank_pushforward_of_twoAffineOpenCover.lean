-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/86e7abcb-cb95-5c1f-a1e1-1c7d3504e04c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_tilde
import Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover.AlgebraicGeometry Opposite TopologicalSpace TensorProduct"

namespace TwoChartCech
p2m_export "TwoChartCech" "Sections Sections.cechDiff_apply Mumford.projective_ker_of_fibre_surjective"
p2m_open "TwoChartCech"

theorem surjective_baseChange_and_finrank_ker_of_comm
    {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    {C0' C1' : Type u} [AddCommGroup C0'] [Module K C0'] [AddCommGroup C1'] [Module K C1']
    (d : C0 →ₗ[A] C1) (d' : C0' →ₗ[K] C1')
    (e0 : K ⊗[A] C0 ≃ₗ[K] C0') (e1 : K ⊗[A] C1 ≃ₗ[K] C1')
    (h : d' ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ d.baseChange K) :
    (Function.Surjective d' → Function.Surjective (d.baseChange K)) ∧
      Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d') := by
  have hd : d.baseChange K = e1.symm.toLinearMap ∘ₗ d' ∘ₗ e0.toLinearMap := by
    rw [h]
    ext x
    simp
  refine ⟨fun hs => ?_, ?_⟩
  · rw [hd]
    exact e1.symm.surjective.comp (hs.comp e0.surjective)
  · have hk : LinearMap.ker (d.baseChange K) = (LinearMap.ker d').comap e0.toLinearMap := by
      rw [hd]
      ext x
      simp [LinearMap.mem_ker]
    rw [hk, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end TwoChartCech

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Spec Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.fromTildeΓ Flat modulesSpecToSheaf Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules tilde Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.mapPresheaf_app Modules.fromTildeΓ Modules.pullbackPushforwardAdjunction Modules Opens ΓSpecIso Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.specMap Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom mapPresheaf_app fromTildeΓ pullbackPushforwardAdjunction map_smul IsLocallyFreeOfRank isIso_fromTildeGamma_pushforward_of_locallyTrivial isLocallyFreeOfRank_tilde projective_sections_of_locallyTrivial IsLocallyFreeOfRank.of_iso exists_linearEquiv_sections_baseChange_of_locallyTrivial"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "mapPresheaf app" end Hom
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in
omit π in

lemma Hom.app_presheaf_map {F G : X.Modules} (η : F ⟶ G) {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)) :
    (η.app V).hom (F.presheaf.map i.op s) = G.presheaf.map i.op ((η.app U).hom s) := by
  have h := η.mapPresheaf.naturality i.op
  simp only [Scheme.Modules.mapPresheaf_app] at h
  simpa [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h s

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

omit π in

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

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover.Module.Flat.prod_of_flat" "Module.Flat.prod_of_flat"

theorem isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover_aux
    [IsNoetherianRing A] [Flat π] (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1) (n : ℕ)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (specMap A K))).obj F)).H1 ∧
      Module.finrank K ((𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (specMap A K))).obj F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by
  classical
  set S := 𝒱.sectionsOf π F with hS

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

  have hsq : ∀ (K : Type u) [Field K] [Algebra A K],
      Function.Surjective (S.cechDiff.baseChange K) ∧
        Module.finrank K (LinearMap.ker (S.cechDiff.baseChange K)) = n := by
    intro K _ _
    obtain ⟨hH1, hH0⟩ := hfib K

    set fK := pullback.fst π (specMap A K) with hfK
    set FK : (Limits.pullback π (specMap A K)).Modules := (Scheme.Modules.pullback fK).obj F with hFK
    set SK := (𝒱.pullback π K).sectionsOf (pullback.snd π (specMap A K)) FK with hSK
    let η := (Scheme.Modules.pullbackPushforwardAdjunction fK).unit.app F
    letI := moduleSectionsOfHom π F 𝒱.U0
    letI := moduleSectionsOfHom π F 𝒱.U1
    letI := moduleSectionsOfHom π F (𝒱.U0 ⊓ 𝒱.U1)
    letI := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ 𝒱.U0)
    letI := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ 𝒱.U1)
    letI := moduleSectionsOfHom (pullback.snd π (specMap A K)) FK (fK ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))

    obtain ⟨ε0, hε0⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U0
      𝒱.isAffineOpen_U0 K
    obtain ⟨ε1, hε1⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv 𝒱.U1
      𝒱.isAffineOpen_U1 K
    obtain ⟨ε01, hε01⟩ := exists_linearEquiv_sections_baseChange_of_locallyTrivial π F htriv (𝒱.U0 ⊓ 𝒱.U1)
      𝒱.isAffineOpen_inf K

    let e0 : K ⊗[A] (S.M0 × S.M1) ≃ₗ[K] (SK.M0 × SK.M1) :=
      (TensorProduct.prodRight A K K S.M0 S.M1).trans (ε0.prodCongr ε1)
    let e1 : K ⊗[A] S.M01 ≃ₗ[K] SK.M01 := ε01
    have hr0 : ∀ s : S.M0, SK.r0 (ε0 ((1 : K) ⊗ₜ[A] s)) = ε01 ((1 : K) ⊗ₜ[A] (S.r0 s)) := by
      intro s
      rw [hε0, hε01]
      exact (Hom.app_presheaf_map η (homOfLE inf_le_left) s).symm
    have hr1 : ∀ s : S.M1, SK.r1 (ε1 ((1 : K) ⊗ₜ[A] s)) = ε01 ((1 : K) ⊗ₜ[A] (S.r1 s)) := by
      intro s
      rw [hε1, hε01]
      exact (Hom.app_presheaf_map η (homOfLE inf_le_right) s).symm
    have hcomm : SK.cechDiff ∘ₗ e0.toLinearMap = e1.toLinearMap ∘ₗ S.cechDiff.baseChange K := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul k x => ?_
      obtain ⟨s0, s1⟩ := x
      have hk : ∀ {N : Type u} [AddCommGroup N] [Module A N] (y : N),
          (k ⊗ₜ[A] y : K ⊗[A] N) = k • ((1 : K) ⊗ₜ[A] y) := fun y => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [hk, _root_.map_smul, _root_.map_smul, _root_.map_smul, _root_.map_smul]
      congr 1
      have he0 : e0 ((1 : K) ⊗ₜ[A] (s0, s1)) = (ε0 ((1 : K) ⊗ₜ[A] s0), ε1 ((1 : K) ⊗ₜ[A] s1)) := by
        simp only [e0, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul]
        rfl
      have he1 : ∀ y, e1 y = ε01 y := fun _ => rfl
      rw [he0, he1, LinearMap.baseChange_tmul, TwoChartCech.Sections.cechDiff_apply,
        TwoChartCech.Sections.cechDiff_apply]
      dsimp only
      rw [TensorProduct.tmul_sub, hr0, hr1]
      exact (map_sub ε01 _ _).symm
    have key := TwoChartCech.surjective_baseChange_and_finrank_ker_of_comm S.cechDiff SK.cechDiff e0 e1 hcomm
    refine ⟨key.1 ?_, key.2.trans hH0⟩
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hH1

  obtain ⟨hproj, -, hrank⟩ := TwoChartCech.Mumford.projective_ker_of_fibre_surjective S.cechDiff
    (fun K _ _ => (hsq K).1)

  obtain ⟨e0, he0⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 π F
  let e : globalSectionsModule π F ≃ₗ[A] LinearMap.ker S.cechDiff := (globalSectionsEquiv π F).trans e0
  haveI : Module.Projective A (globalSectionsModule π F) := Module.Projective.of_equiv e.symm
  haveI : Module.Finite A (globalSectionsModule π F) := Module.Finite.equiv e.symm
  have hrk : ∀ (K : Type u) [Field K] [Algebra A K],
      Module.finrank K (K ⊗[A] globalSectionsModule π F) = n := by
    intro K _ _
    rw [(LinearEquiv.baseChange A K _ _ e).finrank_eq, hrank K, (hsq K).2]

  have hLF := isLocallyFreeOfRank_tilde (R := .of A) (globalSectionsModule π F) n hrk
  haveI := isIso_fromTildeGamma_pushforward_of_locallyTrivial π 𝒱 F htriv
  exact IsLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ (R := .of A)
    ((Scheme.Modules.pushforward π).obj F))) hLF

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1) (n : ℕ)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1 ∧
      Module.finrank K ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) :=
  isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover_aux π 𝒱 F htriv hfin n hfib

#print axioms solution

end S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover (solution)
