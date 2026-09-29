-- Prove2me | solution 1 for AlgebraicGeometry.exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7f018840-c30f-56d8-819a-70d0e6d795a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GraphAlgAux

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

abbrev A (U : X.affineOpens) : Type u := X.presheaf.obj (op U.1)

section MkAffHom

variable {M N : OModulePresheaf f}

def linR (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) : M.obj U.1 →ₗ[R] N.obj U.1 where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U.1
    haveI := M.isScalarTower U.1
    haveI := N.isScalarTower U.1
    change g (r • x) = r • g x
    rw [← algebraMap_smul (A := A U) r x, g.map_smul, algebraMap_smul]

@[scoped simp] theorem linR_apply (U : X.affineOpens) (g : M.obj U.1 →ₗ[A U] N.obj U.1) (x : M.obj U.1) :
    linR U g x = g x := rfl

def mkAffHom (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1)
    (nat : ∀ (U U' : X.affineOpens) (h : U.1 ≤ U'.1) (x : M.obj U'.1), app U (M.res h x) = N.res h (app U' x)) :
    AffHom M N where
  app U := linR U (app U)
  app_smul U a x := (app U).map_smul a x
  naturality h := LinearMap.ext fun x => nat _ _ h x

@[scoped simp] theorem mkAffHom_app (app : ∀ U : X.affineOpens, M.obj U.1 →ₗ[A U] N.obj U.1) (nat) (U : X.affineOpens)
    (x : M.obj U.1) : (mkAffHom app nat).app U x = app U x := rfl

theorem affHom_ext (a b : AffHom M N) (h : ∀ (W : X.affineOpens) (x : M.obj W.1), a.app W x = b.app W x) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  have : a1 = b1 := funext fun W => LinearMap.ext (h W)
  subst this
  rfl

end MkAffHom

theorem unit_isCoherent : (unit f).IsCoherent := fun U => Module.Finite.self (A U)

theorem unit_isQuasicoherent : (unit f).IsQuasicoherent := by
  intro U r
  haveI := U.2.isLocalization_basicOpen r
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (show Γ(X, X.basicOpen r) from x)
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, y, ?_⟩
    change (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y =
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ n) * (show Γ(X, X.basicOpen r) from x)
    have e : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) = (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom := rfl
    have hn' : r ^ n = s.1 := hn
    rw [← e, hn', mul_comm]
    exact hs.symm
  · have hy' : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (show Γ(X, U.1) from y) = 0 := hy
    obtain ⟨⟨m, k, hk⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers r) Γ(X, X.basicOpen r) _).mp hy'
    refine ⟨k, ?_⟩
    have hk' : r ^ k = m := hk
    change r ^ k * (show Γ(X, U.1) from y) = 0
    rw [hk']
    exact hm

structure Sys {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R)
  hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1))))
  tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))
  htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n
  xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1))
  hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n)
  hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n
  Y : ℕ → Scheme.{u}
  g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)
  hg : ∀ n : ℕ, IsFinite (g n)
  yn : ∀ n : ℕ, Y n ⟶ Y (n + 1)
  hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)

variable [IsNoetherianRing R] {I : Ideal R} [IsAdicComplete I R] [IsProper f] (S : Sys I f)

namespace Sys

abbrev h (n : ℕ) : S.Y n ⟶ X := S.g n ≫ pullback.fst f (S.sR n)

abbrev B (n : ℕ) : OModulePresheaf f := pushforwardUnit f (S.h n)

abbrev BΓ (n : ℕ) (U : X.Opens) : Type u := (S.Y n).presheaf.obj (op ((S.h n) ⁻¹ᵁ U))

abbrev bapp (n : ℕ) (U : X.Opens) : Γ(X, U) →+* S.BΓ n U := ((S.h n).appLE U ((S.h n) ⁻¹ᵁ U) le_rfl).hom

theorem yn_comp_h (n : ℕ) : S.yn n ≫ S.h (n + 1) = S.h n := by
  change S.yn n ≫ S.g (n + 1) ≫ pullback.fst f (S.sR (n + 1)) = S.g n ≫ pullback.fst f (S.sR n)
  rw [← Category.assoc, (S.hY n).w, Category.assoc, S.hxn₁]

theorem pre_le (n : ℕ) (U : X.Opens) : (S.h n) ⁻¹ᵁ U ≤ (S.yn n) ⁻¹ᵁ ((S.h (n + 1)) ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, S.yn_comp_h]

abbrev ynapp (n : ℕ) (U : X.Opens) : S.BΓ (n + 1) U →+* S.BΓ n U :=
  ((S.yn n).appLE ((S.h (n + 1)) ⁻¹ᵁ U) ((S.h n) ⁻¹ᵁ U) (S.pre_le n U)).hom

scoped instance isFinite_g (n : ℕ) : IsFinite (S.g n) := S.hg n

theorem B_smul (n : ℕ) (U : X.Opens) (a : Γ(X, U)) (z : (S.B n).obj U) :
    (a • z : (S.B n).obj U) = (show (S.B n).obj U from S.bapp n U a * (show S.BΓ n U from z)) := rfl

theorem B_res (n : ℕ) {U U' : X.Opens} (hU : U ≤ U') (z : (S.B n).obj U') :
    ((S.B n).res hU z : S.BΓ n U) =
      ((S.Y n).presheaf.map (homOfLE ((Opens.map (S.h n).base).monotone hU)).op).hom (show S.BΓ n U' from z) := rfl

theorem B_coh_qc (n : ℕ) : (S.B n).IsCoherent ∧ (S.B n).IsQuasicoherent :=
  (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
    R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).1 n

theorem B_coh (n : ℕ) : (S.B n).IsCoherent := (S.B_coh_qc n).1
theorem B_qc (n : ℕ) : (S.B n).IsQuasicoherent := (S.B_coh_qc n).2

theorem exists_τ : ∃ τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n),
    (∀ (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1),
      (τ n).app U z = (show (S.B n).obj U.1 from S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z))) ∧
    (∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((τ n).app U)) ∧
    (∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1))) := by
  obtain ⟨τ, hτ, hs, hk⟩ :=
    (AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
      R I X f S.sR S.hsR S.tR S.htR S.xn S.hxn₁ S.hxn₂ S.Y S.g S.yn S.hY).2.2
  exact ⟨τ, hτ, hs, hk⟩

def τ : ∀ n : ℕ, AffHom (S.B (n + 1)) (S.B n) := S.exists_τ.choose

theorem τ_app (n : ℕ) (U : X.affineOpens) (z : (S.B (n + 1)).obj U.1) :
    ((S.τ n).app U z : S.BΓ n U.1) = S.ynapp n U.1 (show S.BΓ (n + 1) U.1 from z) :=
  S.exists_τ.choose_spec.1 n U z

theorem τ_surj (n : ℕ) (U : X.affineOpens) : Function.Surjective ((S.τ n).app U) :=
  S.exists_τ.choose_spec.2.1 n U

theorem τ_ker (n : ℕ) (U : X.affineOpens) :
    LinearMap.ker ((S.τ n).app U) = I ^ (n + 1) • (⊤ : Submodule R ((S.B (n + 1)).obj U.1)) :=
  S.exists_τ.choose_spec.2.2 n U

def u (n : ℕ) : AffHom (unit f) (S.B n) :=
  mkAffHom
    (fun U =>
      { toFun := fun a => show (S.B n).obj U.1 from S.bapp n U.1 (show A U from a)
        map_add' := fun a b => map_add _ _ _
        map_smul' := fun a b => by
          change S.bapp n U.1 (a * (show A U from b)) = a • (show (S.B n).obj U.1 from S.bapp n U.1 (show A U from b))
          rw [B_smul, map_mul] })
    (fun U U' hU a => by
      change S.bapp n U.1 ((X.presheaf.map (homOfLE hU).op).hom a) =
        (S.B n).res hU (show (S.B n).obj U'.1 from S.bapp n U'.1 a)
      rw [B_res, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map])

theorem u_app (n : ℕ) (U : X.affineOpens) (a : A U) :
    ((S.u n).app U (show (unit f).obj U.1 from a) : S.BΓ n U.1) = S.bapp n U.1 a := rfl

theorem ynapp_bapp (n : ℕ) (U : X.Opens) (a : Γ(X, U)) : S.ynapp n U (S.bapp (n + 1) U a) = S.bapp n U a := by
  change ((S.h (n + 1)).appLE U _ le_rfl ≫ (S.yn n).appLE _ _ (S.pre_le n U)).hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (k : S.Y n ⟶ X) (hk : k = S.h n) (e : (S.h n) ⁻¹ᵁ U ≤ k ⁻¹ᵁ U),
      (k.appLE U ((S.h n) ⁻¹ᵁ U) e).hom a = S.bapp n U a := by
    rintro k rfl e; rfl
  exact key _ (S.yn_comp_h n) _

theorem hτu (n : ℕ) : (S.τ n).comp (S.u (n + 1)) = S.u n :=
  affHom_ext _ _ fun U a => by
    rw [AffHom.comp_app]
    exact (S.τ_app n U _).trans (S.ynapp_bapp n U.1 a)

theorem k42 (F : OModulePresheaf f) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (ρ : ∀ n : ℕ, AffHom F (S.B n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens), LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (F.obj U.1)))
    (hτρ : ∀ n : ℕ, (S.τ n).comp (ρ (n + 1)) = ρ n)
    (M : OModulePresheaf f) (hMc : M.IsCoherent) (hMq : M.IsQuasicoherent)
    (ψ : ∀ n : ℕ, AffHom M (S.B n)) (hψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : AffHom M F, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : AffHom M F, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ :=
  AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper I f M F hMc hMq
    hFc hFq S.B S.τ ρ hρs hρk hτρ ψ hψ

end Sys
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

section IdealLemmas

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

theorem comap_map_of_isClosedImmersion {Z W : Scheme.{u}} (ι : Z ⟶ W) [IsClosedImmersion ι]
    (K : Z.IdealSheafData) : (K.map ι).comap ι = K := by
  have h1 : K.map ι = (K.subschemeι ≫ ι).ker := by
    rw [← Scheme.IdealSheafData.map_ker, ker_subschemeι]
  rw [h1, ← ker_fst_of_isClosedImmersion]
  have h2 : pullback.fst ι (K.subschemeι ≫ ι) = pullback.snd ι (K.subschemeι ≫ ι) ≫ K.subschemeι := by
    rw [← cancel_mono ι, Category.assoc, pullback.condition]
  rw [h2, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

theorem comap_sup_ker {Z W : Scheme.{u}} (ι : Z ⟶ W) (J : W.IdealSheafData) :
    (J ⊔ ι.ker).comap ι = J.comap ι := by
  have h : ι.ker.comap ι = ⊥ :=
    le_bot_iff.mp (by rw [← Scheme.IdealSheafData.map_bot]; exact comap_map_le _ _)
  rw [Scheme.IdealSheafData.comap_sup, h, sup_bot_eq]

end IdealLemmas
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys"

theorem appLE_ΓSpecIso_inv_eq_zero {Zn : Scheme.{u}} (𝔞 : Ideal R) (t : Zn ⟶ Spec (.of (R ⧸ 𝔞)))
    (W : Zn.Opens) (r : R) (hr : r ∈ 𝔞)
    (k : Zn ⟶ Spec (.of R)) (hk : k = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))
    (e : W ≤ k ⁻¹ᵁ ⊤) :
    (k.appLE ⊤ W e).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) = 0 := by
  subst hk
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top, CommRingCat.comp_apply]
  have : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (.of (R ⧸ 𝔞))).inv.hom (Ideal.Quotient.mk 𝔞 r) := by
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))).appTop).hom r = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]

end GraphAlgAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux.Sys P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj.GraphAlgAux"

open GraphAlgAux AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιP : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hιP : IsClosedImmersion ιP)
    (hιPp : ιP ≫ ProjSpace.π R N = p)
    (Jn : ∀ n : ℕ, (adicThickening p I n).IdealSheafData)
    (hJn : ∀ n : ℕ, (Jn (n + 1)).comap (adicThickeningTransition p I n) = Jn n) :
    ∃ J : P.IdealSheafData, ∀ n : ℕ, J.comap (adicThickeningι p I n) = Jn n := by
  haveI : IsProper p := by rw [← hιPp]; infer_instance

  have Hle : ∀ n : ℕ, Jn (n + 1) ≤ (Jn n).map (adicThickeningTransition p I n) := fun n =>
    le_map_iff_comap_le.mpr (hJn n).le
  let S : Sys I p :=
    { sR := fun n => adicThickeningBase I n
      hsR := fun n => rfl
      tR := fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))))
      htR := fun n => adicThickeningBase_succ_comp I n
      xn := fun n => adicThickeningTransition p I n
      hxn₁ := fun n => adicThickeningTransition_ι p I n
      hxn₂ := fun n => adicThickeningTransition_toBase p I n
      Y := fun n => (Jn n).subscheme
      g := fun n => (Jn n).subschemeι
      hg := fun n => (inferInstance : IsFinite (Jn n).subschemeι)
      yn := fun n => subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n)
      hY := fun n => (isPullback_of_isClosedImmersion (Jn n).subschemeι (Jn (n + 1)).subschemeι
        (subschemeMap (Jn n) (Jn (n + 1)) (adicThickeningTransition p I n) (Hle n))
        (adicThickeningTransition p I n) (by rw [subschemeMap_subschemeι])
        (by rw [ker_subschemeι, ker_subschemeι, hJn])).flip }

  haveI := hιP
  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
      I ιP hιPp S.B S.B_coh S.B_qc S.τ S.τ_surj S.τ_ker
  have hτψ : ∀ n : ℕ, (S.τ n).comp (ψ (n + 1)) = ψ n := fun n =>
    affHom_ext _ _ fun U x => by
      rw [AffHom.comp_app]
      exact congrFun (congrArg DFunLike.coe (hψc n U)) x

  obtain ⟨η, hη, -⟩ := S.k42 G hGc hGq ψ hψs hψk hτψ (unit p) unit_isCoherent unit_isQuasicoherent S.u S.hτu

  have hbapp : ∀ (n : ℕ) (U : P.affineOpens), Function.Surjective (S.bapp n U.1) := fun n U => by
    haveI : IsClosedImmersion (S.h n) :=
      (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
    have e : (S.h n).app U.1 = (S.h n).appLE U.1 _ le_rfl := Scheme.Hom.app_eq_appLE _
    have := (S.h n).app_surjective U.1 U.2
    rw [e] at this
    exact this
  have hηs : ∀ U : P.affineOpens, Function.Surjective (η.app U) := fun U =>
    AlgebraicGeometry.OModulePresheaf.AffHom.surjective_app_of_range_sup_smul_top_eq_top_of_le_jacobson
      I (IsAdicComplete.le_jacobson_bot I) unit_isQuasicoherent hGc hGq η (fun U => by
        refine eq_top_iff.mpr fun m _ => ?_
        obtain ⟨a, ha⟩ := hbapp 0 U ((ψ 0).app U m : S.BΓ 0 U.1)
        have h1 : (ψ 0).app U (η.app U (show (unit p).obj U.1 from a)) = (ψ 0).app U m := by
          have := congrArg (fun θ : AffHom (unit p) (S.B 0) => θ.app U (show (unit p).obj U.1 from a)) (hη 0)
          dsimp only at this
          rw [AffHom.comp_app] at this
          rw [this]
          exact ha
        have h2 : m - η.app U (show (unit p).obj U.1 from a) ∈ LinearMap.ker ((ψ 0).app U) := by
          rw [LinearMap.mem_ker, map_sub, h1, sub_self]
        rw [hψk 0 U, pow_one] at h2
        have : m = η.app U (show (unit p).obj U.1 from a) + (m - η.app U (show (unit p).obj U.1 from a)) := by
          abel
        rw [this]
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) h2) U

  have hnat : ∀ (U U' : P.affineOpens) (hU : U.1 ≤ U'.1) (a : Γ(P, U'.1)),
      η.app U (show (unit p).obj U.1 from (P.presheaf.map (homOfLE hU).op).hom a) =
        G.res hU (η.app U' (show (unit p).obj U'.1 from a)) := fun U U' hU a =>
    η.naturality_apply (U := U) (U' := U') hU _
  have hmul : ∀ (U : P.affineOpens) (a b : Γ(P, U.1)),
      η.app U (show (unit p).obj U.1 from a * b) = a • η.app U (show (unit p).obj U.1 from b) := fun U a b =>
    η.app_smul U a (show (unit p).obj U.1 from b)
  let Jideal : ∀ U : P.affineOpens, Ideal Γ(P, U.1) := fun U =>
    { carrier := {a | η.app U (show (unit p).obj U.1 from a) = 0}
      add_mem' := fun {a b} ha hb => by
        change η.app U (show (unit p).obj U.1 from a + b) = 0
        rw [show (show (unit p).obj U.1 from a + b) = (show (unit p).obj U.1 from a) + (show (unit p).obj U.1 from b)
          from rfl, map_add]
        rw [Set.mem_setOf_eq] at ha hb
        rw [ha, hb, add_zero]
      zero_mem' := map_zero (η.app U)
      smul_mem' := fun a b hb => by
        rw [Set.mem_setOf_eq] at hb ⊢
        rw [smul_eq_mul, hmul, hb, smul_zero] }
  have hJmem : ∀ (U : P.affineOpens) (a : Γ(P, U.1)),
      a ∈ Jideal U ↔ η.app U (show (unit p).obj U.1 from a) = 0 := fun U a => Iff.rfl
  have hJbasic : ∀ (U : P.affineOpens) (r : Γ(P, U.1)),
      (Jideal U).map (P.presheaf.map (homOfLE <| P.basicOpen_le r).op).hom = Jideal (P.affineBasicOpen r) := by
    intro U r
    haveI := U.2.isLocalization_basicOpen r
    have eρ : algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) = (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom := rfl
    apply le_antisymm
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
      rw [Ideal.mem_comap]
      refine (hJmem (P.affineBasicOpen r) _).mpr ?_
      rw [hJmem] at ha
      exact (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) a).trans (by rw [ha, map_zero])
    · intro x hx
      replace hx := (hJmem (P.affineBasicOpen r) x).mp hx
      obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) x
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
      simp only at hs hn

      have hy0 : η.app (P.affineBasicOpen r)
          (show (unit p).obj (P.basicOpen r) from algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) y) = 0 := by
        rw [← hs, mul_comm]
        exact (hmul (P.affineBasicOpen r) _ x).trans (by rw [hx, smul_zero])
      have hy1 : G.res (P.basicOpen_le r) (η.app U (show (unit p).obj U.1 from y)) = 0 :=
        (hnat (P.affineBasicOpen r) U (P.basicOpen_le r) y).symm.trans hy0
      obtain ⟨k, hk⟩ := (hGq U r).2 _ hy1

      have hmem : r ^ k * y ∈ Jideal U := by rw [hJmem, hmul]; exact hk
      have hunit : IsUnit (algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1)))) :=
        IsLocalization.map_units (M := Submonoid.powers r) _
          ⟨r ^ k * (s : Γ(P, U.1)), (Submonoid.mem_powers_iff _ _).mpr ⟨k + n, by rw [pow_add, hn]⟩⟩
      obtain ⟨v, hv⟩ := hunit.exists_left_inv
      have hx' : x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
        calc x = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * (s : Γ(P, U.1))) * x := by
                rw [hv, one_mul]
          _ = v * algebraMap Γ(P, U.1) Γ(P, P.basicOpen r) (r ^ k * y) := by
                rw [map_mul, map_mul, mul_assoc, mul_assoc, ← hs, mul_comm x]
      rw [hx', eρ]
      exact Ideal.mul_mem_left _ v (Ideal.mem_map_of_mem _ hmem)
  let J : P.IdealSheafData := ⟨Jideal, hJbasic, _, rfl⟩
  have hJideal : ∀ U : P.affineOpens, J.ideal U = Jideal U := fun U => rfl
  refine ⟨J, fun n => ?_⟩

  haveI : IsClosedImmersion (S.h n) :=
    (inferInstance : IsClosedImmersion ((Jn n).subschemeι ≫ adicThickeningι p I n))
  have step3 : J ⊔ (adicThickeningι p I n).ker = (Jn n).map (adicThickeningι p I n) := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, hJideal, Scheme.Hom.ker_apply, ideal_map_of_isAffineHom]

    have hJn : (Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩ =
        RingHom.ker ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom := by
      conv_lhs => rw [← ker_subschemeι (Jn n)]
      rw [Scheme.Hom.ker_apply]
    have hcomp : ∀ a : Γ(P, U.1), ((Jn n).subschemeι.app ((adicThickeningι p I n) ⁻¹ᵁ U.1)).hom
        (((adicThickeningι p I n).app U.1).hom a) = S.bapp n U.1 a := by
      intro a
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_app]
      change ((S.h n).app U.1).hom a = _
      rw [Scheme.Hom.app_eq_appLE]

    have hR : ∀ a : Γ(P, U.1), a ∈ ((Jn n).ideal ⟨_, U.2.preimage (adicThickeningι p I n)⟩).comap
        ((adicThickeningι p I n).app U.1).hom ↔
        η.app U (show (unit p).obj U.1 from a) ∈ I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)) := by
      intro a
      rw [Ideal.mem_comap, hJn, RingHom.mem_ker, hcomp, ← hψk n U, LinearMap.mem_ker]
      have := congrArg (fun θ : AffHom (unit p) (S.B n) => θ.app U (show (unit p).obj U.1 from a)) (hη n)
      dsimp only at this
      rw [AffHom.comp_app] at this
      rw [this]
      exact Iff.rfl
    apply le_antisymm
    · refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [hR]; rw [hJmem] at ha; rw [ha]; exact Submodule.zero_mem _
      · rw [Ideal.mem_comap, hJn, RingHom.mem_ker]
        rw [RingHom.mem_ker] at ha
        rw [ha, map_zero]
    · intro a ha
      rw [hR] at ha

      have hrange : (I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1))) =
          (I ^ (n + 1) • (⊤ : Submodule R ((unit p).obj U.1))).map (η.app U) := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hηs U)]
      rw [hrange] at ha
      obtain ⟨b, hb, hηb⟩ := ha
      have hab : (show Γ(P, U.1) from a) - (show Γ(P, U.1) from b) ∈ Jideal U := by
        rw [hJmem]
        change η.app U ((show (unit p).obj U.1 from a) - b) = 0
        rw [map_sub, hηb, sub_self]
      have hbker : (show Γ(P, U.1) from b) ∈ RingHom.ker ((adicThickeningι p I n).app U.1).hom := by
        refine Submodule.smul_induction_on hb (fun r hr c _ => ?_) (fun x y hx hy => ?_)
        · rw [RingHom.mem_ker]
          letI := Scheme.TwoAffineOpenCover.algebraOfHom p U.1
          letI := Scheme.TwoAffineOpenCover.algebraOfHom (adicThickeningι p I n ≫ p) ((adicThickeningι p I n) ⁻¹ᵁ U.1)
          change ((adicThickeningι p I n).app U.1).hom (algebraMap R Γ(P, U.1) r * (show Γ(P, U.1) from c)) = 0
          rw [map_mul, Scheme.Hom.app_eq_appLE, appLE_algebraMap]
          rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom,
            appLE_ΓSpecIso_inv_eq_zero (I ^ (n + 1)) (adicThickeningToBase p I n) _ r hr _
              (adicThickeningι_comp p I n), zero_mul]
        · exact Ideal.add_mem _ hx hy
      have : a = ((show Γ(P, U.1) from a) - (show Γ(P, U.1) from b)) + (show Γ(P, U.1) from b) := by
        change a = a - _ + _; abel
      rw [this]
      exact Submodule.add_mem_sup hab hbker
  calc J.comap (adicThickeningι p I n)
      = (J ⊔ (adicThickeningι p I n).ker).comap (adicThickeningι p I n) := (comap_sup_ker _ J).symm
    _ = ((Jn n).map (adicThickeningι p I n)).comap (adicThickeningι p I n) := by rw [step3]
    _ = Jn n := comap_map_of_isClosedImmersion _ _

end
end S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_exists_idealSheafData_forall_comap_adicThickening_eq_of_isAdicComplete_of_isClosedImmersion_proj (solution)
