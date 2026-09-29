-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6d6f1b23-dab9-5de7-af65-0ab2f0795808

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ChiLC
p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero"

section IsoInv
variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

noncomputable def homOfModules {N N' : V.Modules} (φ : N ⟶ N') :
    OModulePresheaf.Hom (ofModules π N) (ofModules π N') where
  app U :=
    { toFun := fun x => (show Γ(N, U) ⟶ Γ(N', U) from φ.app U) x
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun r x => by
        show φ.app U ((r : R) • (show (ofModules π N).obj U from x)) = (r : R) • (show (ofModules π N').obj U from φ.app U x)
        rw [ofModules_algebraMap_smul, ofModules_algebraMap_smul]
        exact Scheme.Modules.Hom.app_smul φ _ _ }
  app_smul U a x := Scheme.Modules.Hom.app_smul φ a x
  naturality {U U'} h := by
    refine LinearMap.ext fun x => ?_
    show φ.app U ((ofModules π N).res h x) = (ofModules π N').res h (φ.app U' x)
    rw [ofModules_res_apply, ofModules_res_apply]
    have nat := φ.mapPresheaf.naturality (homOfLE h).op
    simp only [Scheme.Modules.mapPresheaf_app] at nat
    have := ConcreteCategory.congr_hom nat x
    simpa only [ConcreteCategory.comp_apply] using this

theorem homOfModules_app {N N' : V.Modules} (φ : N ⟶ N') (U : V.Opens) (x : (ofModules π N).obj U) :
    (homOfModules π φ).app U x = φ.app U x := rfl

variable [IsSeparated π] (K : V.OrderedAffineCover)

theorem cochainMap_comp_apply {N N' N'' : V.Modules} (φ : N ⟶ N') (ψ : N' ⟶ N'') (i : ℕ) (c : (ofModules π N).cochain K i) :
    ((homOfModules π ψ).toAffHom.cochainMap K i) (((homOfModules π φ).toAffHom.cochainMap K i) c) =
      ((homOfModules π (φ ≫ ψ)).toAffHom.cochainMap K i) c := by
  funext s
  simp only [AffHom.cochainMap_apply]
  show ψ.app _ (φ.app _ (c s)) = (φ ≫ ψ).app _ (c s)
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

theorem cochainMap_id_apply {N : V.Modules} (i : ℕ) (c : (ofModules π N).cochain K i) :
    ((homOfModules π (𝟙 N)).toAffHom.cochainMap K i) c = c := by
  funext s
  simp only [AffHom.cochainMap_apply]
  show (𝟙 N : N ⟶ N).app _ (c s) = c s
  rw [Scheme.Modules.Hom.id_app]
  rfl

theorem cechFinrank_ofModules_eq_of_iso {N N' : V.Modules} (e : N ≅ N') (n : ℕ) :
    (ofModules π N).cechFinrank K n = (ofModules π N').cechFinrank K n := by

  let F := (homOfModules π e.hom).toAffHom
  let G := (homOfModules π e.inv).toAffHom
  have hGF : ∀ (i : ℕ) (x : LinearMap.ker ((ofModules π N).d K i)), G.kerMap K i (F.kerMap K i x) = x := by
    intro i x
    apply Subtype.ext
    simp only [AffHom.kerMap_coe]
    rw [cochainMap_comp_apply, e.hom_inv_id, cochainMap_id_apply]
  have hFG : ∀ (i : ℕ) (x : LinearMap.ker ((ofModules π N').d K i)), F.kerMap K i (G.kerMap K i x) = x := by
    intro i x
    apply Subtype.ext
    simp only [AffHom.kerMap_coe]
    rw [cochainMap_comp_apply, e.inv_hom_id, cochainMap_id_apply]
  cases n with
  | zero =>
    rw [cechFinrank_zero, cechFinrank_zero]
    exact LinearEquiv.finrank_eq
      (LinearEquiv.ofLinear (F.kerMap K 0) (G.kerMap K 0) (LinearMap.ext fun x => hFG 0 x) (LinearMap.ext fun x => hGF 0 x))
  | succ i =>
    rw [cechFinrank_succ, cechFinrank_succ]
    refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear (F.HSuccMap K i) (G.HSuccMap K i) ?_ ?_)
    · refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H x => rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, hFG]; rfl
    · refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | H x => rw [LinearMap.comp_apply, AffHom.HSuccMap_mk, AffHom.HSuccMap_mk, hGF]; rfl

theorem eulerChar_ofModules_eq_of_iso {N N' : V.Modules} (e : N ≅ N') :
    (ofModules π N).eulerChar K = (ofModules π N').eulerChar K := by
  simp only [eulerChar_def, cechFinrank_ofModules_eq_of_iso π K e]

end IsoInv

theorem eulerChar_ofModules_congr {R : Type u} [CommRing R] {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π')
    (N : V.Modules) (K : V.OrderedAffineCover) :
    (OModulePresheaf.ofModules π N).eulerChar K = (OModulePresheaf.ofModules π' N).eulerChar K := by
  subst h; rfl

end ChiLC

namespace ChiLC
p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section BaseChangePath
variable {S : Type u} [CommRing S] {X : Scheme.{u}} (π : X ⟶ Spec (.of S)) [IsProper π]
  (M : X.Modules) (𝒰 : X.OrderedAffineCover)
  (T : Type u) [CommRing T] [Algebra S T]
  (k : Type u) [Field k] [Algebra S k] [Algebra T k] [IsScalarTower S T k]

theorem eulerChar_baseChange_eq_via (hM : Scheme.Modules.IsInvertible M) :
    (ofModules (pullback.snd π (specMap S k))
        ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M)).eulerChar (𝒰.baseChange π k) =
    (ofModules (pullback.snd (pullback.snd π (specMap S T)) (specMap T k))
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd π (specMap S T)) (specMap T k))).obj
          ((Scheme.Modules.pullback (pullback.fst π (specMap S T))).obj M))).eulerChar
      ((𝒰.baseChange π T).baseChange (pullback.snd π (specMap S T)) k) := by
  have hcomp : specMap T k ≫ specMap S T = specMap S k := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  haveI : IsProper (pullback.snd π (specMap S k)) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsProper (pullback.snd π (specMap S T)) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsProper (pullback.snd (pullback.snd π (specMap S T)) (specMap T k)) := MorphismProperty.pullback_snd _ _ inferInstance
  let Φ : pullback (pullback.snd π (specMap S T)) (specMap T k) ≅ pullback π (specMap S k) :=
    pullbackLeftPullbackSndIso π (specMap S T) (specMap T k) ≪≫ pullback.congrHom rfl hcomp
  have hΦsnd : Φ.hom ≫ pullback.snd π (specMap S k) = pullback.snd (pullback.snd π (specMap S T)) (specMap T k) := by
    simp only [Φ, Iso.trans_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hΦfst : Φ.hom ≫ pullback.fst π (specMap S k) =
      pullback.fst (pullback.snd π (specMap S T)) (specMap T k) ≫ pullback.fst π (specMap S T) := by
    simp only [Φ, Iso.trans_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_fst]
    rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M) := Scheme.Modules.IsInvertible.pullback _ hM
  have step1 : ∀ n, (ofModules (Φ.hom ≫ pullback.snd π (specMap S k))
        ((Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M))).cechFinrank
        ((𝒰.baseChange π T).baseChange (pullback.snd π (specMap S T)) k) n =
      (ofModules (pullback.snd π (specMap S k))
        ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M)).cechFinrank (𝒰.baseChange π k) n :=
    fun n => AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso
      (pullback.snd π (specMap S k)) Φ.hom _ hN _ _ n

  let e : (Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd π (specMap S T)) (specMap T k))).obj
        ((Scheme.Modules.pullback (pullback.fst π (specMap S T))).obj M) :=
    (Scheme.Modules.pullbackComp Φ.hom (pullback.fst π (specMap S k))).app M ≪≫
      (Scheme.Modules.pullbackCongr hΦfst).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd π (specMap S T)) (specMap T k))
        (pullback.fst π (specMap S T))).app M).symm
  calc _ = (ofModules (Φ.hom ≫ pullback.snd π (specMap S k))
        ((Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M))).eulerChar
        ((𝒰.baseChange π T).baseChange (pullback.snd π (specMap S T)) k) := by
          simp only [eulerChar_def, step1]; rfl
    _ = (ofModules (pullback.snd (pullback.snd π (specMap S T)) (specMap T k))
        ((Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M))).eulerChar
        ((𝒰.baseChange π T).baseChange (pullback.snd π (specMap S T)) k) := eulerChar_ofModules_congr hΦsnd _ _
    _ = _ := eulerChar_ofModules_eq_of_iso _ _ e

end BaseChangePath
end ChiLC

namespace ChiLC
p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero AlgebraicGeometry.Scheme.TwoAffineOpenCover"

section Key
variable {S : Type u} [CommRing S] [IsNoetherianRing S] {X : Scheme.{u}} (π : X ⟶ Spec (.of S))
  [IsProper π] [Flat π] (M : X.Modules) (𝒰 : X.OrderedAffineCover)

theorem exists_chi (hM : Scheme.Modules.IsInvertible M) (q : PrimeSpectrum S) :
    ∃ χq : ℤ, ∀ (k : Type u) [Field k] [Algebra S k], RingHom.ker (algebraMap S k) ≤ q.asIdeal →
      (ofModules (pullback.snd π (specMap S k))
        ((Scheme.Modules.pullback (pullback.fst π (specMap S k))).obj M)).eulerChar (𝒰.baseChange π k) = χq := by
  let T := Localization.AtPrime q.asIdeal
  haveI : IsProper (pullback.snd π (specMap S T)) := MorphismProperty.pullback_snd _ _ inferInstance
  obtain ⟨χ₀, hχ₀⟩ := AlgebraicGeometry.OModulePresheaf.exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
    (pullback.snd π (specMap S T)) ((Scheme.Modules.pullback (pullback.fst π (specMap S T))).obj M)
    (Scheme.Modules.IsInvertible.pullback _ hM).1 (𝒰.baseChange π T)
  refine ⟨χ₀, fun k _ _ hk => ?_⟩
  have hu : ∀ y : q.asIdeal.primeCompl, IsUnit (algebraMap S k y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h0 => y.2 (hk (by rwa [RingHom.mem_ker]))
  letI : Algebra T k := (IsLocalization.lift (M := q.asIdeal.primeCompl) hu).toAlgebra
  haveI : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := q.asIdeal.primeCompl) hu x).symm
  rw [eulerChar_baseChange_eq_via π M 𝒰 T k hM]
  exact hχ₀ k

end Key
end ChiLC

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero" in open ChiLC _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] {X : Scheme.{u}} (π : X ⟶ Spec (.of S))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (𝔭 : PrimeSpectrum S) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∃ χ₀ : ℤ, ∀ (k : Type u) [Field k] [Algebra S k], algebraMap S k g ≠ 0 →
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap S k))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap S k))).obj M)).eulerChar (𝒰.baseChange π k)
        = χ₀ := by
  classical
  have hM : Scheme.Modules.IsInvertible M := ⟨htriv⟩
  choose χ hχ using fun q : PrimeSpectrum S => exists_chi π M 𝒰 hM q

  have hspec : ∀ q q' : PrimeSpectrum S, q.asIdeal ≤ q'.asIdeal → χ q = χ q' := by
    intro q q' hqq'
    let k := q.asIdeal.ResidueField
    have h1 := hχ q k (by rw [Ideal.ker_algebraMap_residueField])
    have h2 := hχ q' k (by rw [Ideal.ker_algebraMap_residueField]; exact hqq')
    rw [← h1, h2]
  let Tset : Set (PrimeSpectrum S) := {q | χ q = χ 𝔭}
  have hT : IsClopen Tset := by
    apply TopologicalSpace.NoetherianSpace.isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization
    · intro x y hxy hx
      show χ y = χ 𝔭
      rw [← hspec x y ((PrimeSpectrum.le_iff_specializes x y).mpr hxy), hx]
    · intro x y hxy hx
      show χ y = χ 𝔭
      rw [hspec y x ((PrimeSpectrum.le_iff_specializes y x).mpr hxy), hx]
  obtain ⟨U, ⟨g, rfl⟩, h𝔭U, hUT⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show 𝔭 ∈ Tset from rfl) hT.isOpen
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g 𝔭).mp h𝔭U, χ 𝔭, ?_⟩
  intro k _ _ hg
  let q₀ : PrimeSpectrum S := ⟨RingHom.ker (algebraMap S k), RingHom.ker_isPrime _⟩
  have hq₀ : q₀ ∈ Tset := hUT ((PrimeSpectrum.mem_basicOpen g q₀).mpr (by simpa [q₀, RingHom.mem_ker] using hg))
  rw [hχ q₀ k le_rfl]
  exact hq₀

end S_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_notMem_forall_eulerChar_baseChange_eq_of_locallyTrivial (solution)
