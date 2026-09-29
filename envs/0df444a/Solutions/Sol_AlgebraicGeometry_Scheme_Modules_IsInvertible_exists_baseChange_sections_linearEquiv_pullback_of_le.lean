-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/67a0c5a7-253d-5001-951f-67664ce9a386

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Opposite

namespace G1Brick

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (N : Y.Modules)

noncomputable def sec (V : X.Opens) : Γ(N, i ''ᵁ V) → Γ((Scheme.Modules.pullback i).obj N, V) :=
  fun x => ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app N).app V x

noncomputable def secInv (V : X.Opens) : Γ((Scheme.Modules.pullback i).obj N, V) → Γ(N, i ''ᵁ V) :=
  fun y => ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N).app V y

theorem secInv_sec (V : X.Opens) (x : Γ(N, i ''ᵁ V)) : secInv i N V (sec i N V x) = x := by
  show (((Scheme.Modules.restrictFunctorIsoPullback i).hom.app N).app V ≫
    ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N).app V) x = x
  rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  rfl

theorem sec_secInv (V : X.Opens) (y : Γ((Scheme.Modules.pullback i).obj N, V)) : sec i N V (secInv i N V y) = y := by
  show (((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N).app V ≫
    ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app N).app V) y = y
  rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

theorem sec_add (V : X.Opens) (x x' : Γ(N, i ''ᵁ V)) : sec i N V (x + x') = sec i N V x + sec i N V x' :=
  map_add (((Scheme.Modules.restrictFunctorIsoPullback i).hom.app N).app V).hom x x'

theorem secInv_add (V : X.Opens) (y y' : Γ((Scheme.Modules.pullback i).obj N, V)) :
    secInv i N V (y + y') = secInv i N V y + secInv i N V y' :=
  map_add (((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N).app V).hom y y'

theorem secInv_smul (V : X.Opens) (r : Γ(X, V)) (y : Γ((Scheme.Modules.pullback i).obj N, V)) :
    secInv i N V (r • y) = (i.appIso V).inv r • secInv i N V y :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N) r y

theorem map_secInv {V V' : X.Opens} (j : V ⟶ V') (y : Γ((Scheme.Modules.pullback i).obj N, V')) :
    N.presheaf.map (i.opensFunctor.map j).op (secInv i N V' y) =
      secInv i N V (((Scheme.Modules.pullback i).obj N).presheaf.map j.op y) := by
  have h := ((Scheme.Modules.restrictFunctorIsoPullback i).inv.app N).mapPresheaf.naturality j.op
  have h2 := ConcreteCategory.congr_hom h y
  simp only [CategoryTheory.comp_apply, Scheme.Modules.mapPresheaf_app] at h2
  exact h2.symm

theorem sec_restrict_eq_pullbackLocalSection (U : Y.Opens) (s : Γ(N, U)) :
    sec i N (i ⁻¹ᵁ U) (N.presheaf.map (homOfLE (i.image_preimage_le U)).op s) =
      Scheme.Modules.pullbackLocalSection i s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction i)
    (Scheme.Modules.pullbackPushforwardAdjunction i) N
  have h2 := congrArg (fun φ => Scheme.Modules.Hom.app φ U s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h2
  exact h2

theorem secInv_pullbackLocalSection (U : Y.Opens) (s : Γ(N, U)) :
    secInv i N (i ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection i s) =
      N.presheaf.map (homOfLE (i.image_preimage_le U)).op s := by
  rw [← sec_restrict_eq_pullbackLocalSection, secInv_sec]

theorem map_map_apply {Z : Scheme.{u}} (M : Z.Modules) {U V W : Z.Opens} (f : U ⟶ V) (g : V ⟶ W) (x : Γ(M, W)) :
    M.presheaf.map f.op (M.presheaf.map g.op x) = M.presheaf.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp]; rfl

end G1Brick

theorem solution
    {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (W : Z.Opens) (hW : IsAffineOpen W) (hWU : W ≤ p ⁻¹ᵁ U) :
    letI := (p.appLE U W hWU).hom.toAlgebra
    ∃ β : Γ(Z, W) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, W)] Γ((Scheme.Modules.pullback p).obj L, W),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) =
        ((Scheme.Modules.pullback p).obj L).presheaf.map (homOfLE hWU).op (Scheme.Modules.pullbackLocalSection p s) := by
  classical
  letI algZW : Algebra Γ(X, U) Γ(Z, W) := (p.appLE U W hWU).hom.toAlgebra
  haveI : IsAffine (W : Scheme.{u}) := hW

  have hmemW : ∀ x : (W : Scheme.{u}), W.ι.base x ∈ (W : Set Z) := by
    intro x
    have : W.ι.base x ∈ Set.range W.ι.base := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hV₀ : (W.ι ≫ p) ⁻¹ᵁ U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    show (W.ι ≫ p).base x ∈ (U : Set X)
    exact hWU (hmemW x)
  have hV : W.ι ''ᵁ ((W.ι ≫ p) ⁻¹ᵁ U) = W := by
    rw [hV₀]; exact Scheme.Opens.ι_image_top W
  have hpU' : IsAffineOpen ((W.ι ≫ p) ⁻¹ᵁ U) := by
    rw [hV₀]; exact isAffineOpen_top _

  obtain ⟨β₀, hβ₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback (W.ι ≫ p) hL U hU hpU'
  letI algB₀ : Algebra Γ(X, U) Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U) := ((W.ι ≫ p).app U).hom.toAlgebra

  have hleV : (W.ι ≫ p) ⁻¹ᵁ U ≤ W.ι ⁻¹ᵁ W := by rw [Scheme.Opens.ι_preimage_self]; exact le_top
  let ρh : Γ(Z, W) ⟶ Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U) := W.ι.appLE W ((W.ι ≫ p) ⁻¹ᵁ U) hleV
  have hρh : Z.presheaf.map (homOfLE hV.le).op ≫ (W.ι.appIso ((W.ι ≫ p) ⁻¹ᵁ U)).hom = ρh := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  have hρbij : Function.Bijective ρh := by
    rw [← hρh]
    haveI : IsIso (Z.presheaf.map (homOfLE hV.le).op) := by
      have : homOfLE hV.le = eqToHom hV := Subsingleton.elim _ _
      rw [this, eqToHom_op]; infer_instance
    exact ConcreteCategory.bijective_of_isIso _
  let ρ : Γ(Z, W) ≃+* Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U) := RingEquiv.ofBijective ρh.hom hρbij
  have hρ_alg : ∀ a : Γ(X, U), ρ (p.appLE U W hWU a) = (W.ι ≫ p).app U a := by
    intro a
    show (p.appLE U W hWU ≫ W.ι.appLE W ((W.ι ≫ p) ⁻¹ᵁ U) hleV) a = (W.ι ≫ p).app U a
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]

  have hρ_symm : ∀ c : Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U),
      Z.presheaf.map (homOfLE hV.ge).op ((W.ι.appIso ((W.ι ≫ p) ⁻¹ᵁ U)).inv c) = ρ.symm c := by
    intro c
    apply ρ.injective
    rw [RingEquiv.apply_symm_apply]
    show (((W.ι.appIso ((W.ι ≫ p) ⁻¹ᵁ U)).inv ≫ Z.presheaf.map (homOfLE hV.ge).op) ≫ ρh) c = c
    rw [← hρh, Category.assoc, ← Category.assoc (Z.presheaf.map _), ← Functor.map_comp, ← op_comp,
      show homOfLE hV.le ≫ homOfLE hV.ge = 𝟙 _ from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
    rfl

  let N : Z.Modules := (Scheme.Modules.pullback p).obj L
  let T : Γ((Scheme.Modules.pullback (W.ι ≫ p)).obj L, (W.ι ≫ p) ⁻¹ᵁ U) → Γ(N, W) := fun y =>
    N.presheaf.map (homOfLE hV.ge).op
      (G1Brick.secInv W.ι N ((W.ι ≫ p) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp W.ι p).inv.app L).app ((W.ι ≫ p) ⁻¹ᵁ U) y))

  have hTbij : Function.Bijective T := by
    refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_)
    · haveI : IsIso (N.presheaf.map (homOfLE hV.ge).op) := by
        have : homOfLE hV.ge = eqToHom hV.symm := Subsingleton.elim _ _
        rw [this, eqToHom_op]; infer_instance
      exact ConcreteCategory.bijective_of_isIso _
    · exact Function.bijective_iff_has_inverse.mpr
        ⟨G1Brick.sec W.ι N _, fun y => G1Brick.sec_secInv W.ι N _ y, fun x => G1Brick.secInv_sec W.ι N _ x⟩
    · exact ConcreteCategory.bijective_of_isIso _

  have hTadd : ∀ y y', T (y + y') = T y + T y' := by
    intro y y'
    simp only [T]
    rw [map_add]
    erw [G1Brick.secInv_add]
    rw [map_add]
  have hTsmul : ∀ (c : Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U)) (y), T (c • y) = ρ.symm c • T y := by
    intro c y
    simp only [T]
    rw [Scheme.Modules.Hom.app_smul]
    erw [G1Brick.secInv_smul]
    rw [Scheme.Modules.map_smul, hρ_symm]

  have hTpls : ∀ s : Γ(L, U), T (Scheme.Modules.pullbackLocalSection (W.ι ≫ p) s) =
      N.presheaf.map (homOfLE hWU).op (Scheme.Modules.pullbackLocalSection p s) := by
    intro s
    simp only [T]
    have h1 : ((Scheme.Modules.pullbackComp W.ι p).inv.app L).app ((W.ι ≫ p) ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection (W.ι ≫ p) s) =
        Scheme.Modules.pullbackLocalSection W.ι (Scheme.Modules.pullbackLocalSection p s) := by
      rw [← AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection W.ι p L U s]
      show (((Scheme.Modules.pullbackComp W.ι p).hom.app L).app _ ≫
        ((Scheme.Modules.pullbackComp W.ι p).inv.app L).app _) _ = _
      rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
      rfl
    rw [h1]
    erw [G1Brick.secInv_pullbackLocalSection W.ι N (p ⁻¹ᵁ U)]
    erw [G1Brick.map_map_apply]
    congr 2

  letI modN : Module Γ(X, U) Γ(N, W) := Module.compHom _ (p.appLE U W hWU).hom
  haveI : IsScalarTower Γ(X, U) Γ(Z, W) Γ(N, W) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let f : Γ(L, U) →ₗ[Γ(X, U)] Γ(N, W) :=
    { toFun := fun s => N.presheaf.map (homOfLE hWU).op (Scheme.Modules.pullbackLocalSection p s)
      map_add' := fun s s' => by rw [Scheme.Modules.pullbackLocalSection_add, map_add]
      map_smul' := fun a s => by
        rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.map_smul]
        rfl }
  let β : Γ(Z, W) ⊗[Γ(X, U)] Γ(L, U) →ₗ[Γ(Z, W)] Γ(N, W) := f.liftBaseChange Γ(Z, W)
  have hβ : ∀ (b : Γ(Z, W)) (s : Γ(L, U)), β (b ⊗ₜ s) =
      b • N.presheaf.map (homOfLE hWU).op (Scheme.Modules.pullbackLocalSection p s) :=
    fun b s => LinearMap.liftBaseChange_tmul _ _ _ _

  let ρₗ : Γ(Z, W) ≃ₗ[Γ(X, U)] Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U) :=
    { ρ with
      map_smul' := fun a b => by
        show ρ (p.appLE U W hWU a * b) = (W.ι ≫ p).app U a * ρ b
        rw [map_mul, hρ_alg] }
  let Φ : Γ(Z, W) ⊗[Γ(X, U)] Γ(L, U) → Γ(N, W) :=
    fun x => T (β₀ (TensorProduct.congr ρₗ (LinearEquiv.refl _ _) x))
  have hΦbij : Function.Bijective Φ :=
    hTbij.comp (β₀.bijective.comp (TensorProduct.congr ρₗ (LinearEquiv.refl _ _)).bijective)
  have hT0 : T 0 = 0 := by
    have h := hTadd 0 0
    rw [zero_add] at h
    exact (left_eq_add.mp h)
  have hβΦ : ∀ x, β x = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [Φ]; rw [map_zero, map_zero, map_zero, hT0]
    | tmul b s =>
      simp only [Φ]
      rw [hβ, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        show (ρₗ b) ⊗ₜ[Γ(X, U)] s = ρ b • ((1 : Γ(↑W, (W.ι ≫ p) ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U)] s) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl,
        map_smul, hβ₀, hTsmul, RingEquiv.symm_apply_apply]
      congr 1
      exact (hTpls s).symm
    | add x y hx hy => simp only [Φ] at hx hy ⊢; rw [map_add, hx, hy, map_add, map_add, hTadd]

  refine ⟨LinearEquiv.ofBijective β (by rw [show (β : _ → _) = Φ from funext hβΦ]; exact hΦbij), fun s => ?_⟩
  show β (1 ⊗ₜ s) = _
  rw [hβ, one_smul]

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le (solution)
