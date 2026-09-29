-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/aa18520d-d7de-538e-ba7d-bfb5d535ce99

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
import Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout
import Theorems.Thm_AlgebraicGeometry_exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (r : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)) [IsClosedImmersion ι]
    (hι : ι ≫ ProjSpace.π R r = f)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n)) [∀ n : ℕ, IsFinite (g n)]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n)) :
    ∃ (Yf : Scheme.{u}) (G : Yf ⟶ X) (_ : IsFinite G)
      (e : ∀ n : ℕ, Limits.pullback G (Limits.pullback.fst f (sR n)) ≅ Y n),

      (∀ n : ℕ, (e n).hom ≫ g n = Limits.pullback.snd G (Limits.pullback.fst f (sR n))) ∧

      (∀ n : ℕ,
        Limits.pullback.map G (Limits.pullback.fst f (sR n)) G (Limits.pullback.fst f (sR (n + 1))) (𝟙 Yf) (xn n) (𝟙 X)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hxn₁]) ≫ (e (n + 1)).hom =
          (e n).hom ≫ yn n) := by
  classical

  obtain ⟨hcq, hkill, τ, hτ, hτs, hτk⟩ :=
    AlgebraicGeometry.OModulePresheaf.isCoherent_pushforwardUnit_and_exists_affHom_of_forall_isFinite_isPullback
      R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY

  obtain ⟨F, ψ, hFc, hFq, hψs, hψk, hψc⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
      I ι hι (fun n => OModulePresheaf.pushforwardUnit f (g n ≫ pullback.fst f (sR n)))
      (fun n => (hcq n).1) (fun n => (hcq n).2) τ hτs hτk
  have hψc' : ∀ (n : ℕ) (U : X.affineOpens) (x : F.obj U.1),
      (ψ n).app U x =
        ((yn n).appLE ((g (n + 1) ≫ pullback.fst f (sR (n + 1))) ⁻¹ᵁ U.1) ((g n ≫ pullback.fst f (sR n)) ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, ← Category.assoc, (hY n).w, Category.assoc, hxn₁])).hom
          ((ψ (n + 1)).app U x) := by
    intro n U x
    have h := congrArg (fun (L : _ →ₗ[R] _) => L x) (hψc n U)
    simp only [LinearMap.comp_apply] at h
    rw [← h]
    exact hτ n U _

  obtain ⟨A, α, Hco, e, hfin, hlin, hnat, hring⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper
      R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY F hFc hFq ψ hψs hψk hψc'
  choose r hr using hring

  set D := Scheme.AffineZariskiSite.relativeGluingData Hco with hD
  have hGfin : IsFinite D.toBase := AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData Hco hfin

  obtain ⟨φ, hφG, hφy, hφloc, hpo⟩ :=
    AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_and_isPushout_of_affHom_pushforwardUnit_of_coequifibered
      R I X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY F hFc hFq ψ hψs hψk hψc' A α Hco e hlin hnat r hr

  have hsRci : ∀ n : ℕ, IsClosedImmersion (sR n) := by
    intro n; rw [hsR n]
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hpb : ∀ n : ℕ, IsPullback (φ n) (g n) D.toBase (pullback.fst f (sR n)) := by
    intro n
    haveI := hsRci n
    haveI : IsAffineHom (pullback.fst f (sR n)) := inferInstance
    haveI : IsAffineHom (g n) := inferInstance
    exact AlgebraicGeometry.Scheme.AffineZariskiSite.isPullback_toBase_relativeGluingData_of_forall_isPushout
      Hco (pullback.fst f (sR n)) (g n) (φ n) (hφG n) (fun U => CommRingCat.ofHom (r n U)) (hφloc n) (hpo n)

  refine ⟨D.glued, D.toBase, hGfin, fun n => (hpb n).isoPullback.symm, ?_, ?_⟩
  · intro n
    simp only [Iso.symm_hom, IsPullback.isoPullback_inv_snd]
  · intro n
    rw [← cancel_mono (hpb (n + 1)).isoPullback.hom]
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, hφy,
        IsPullback.isoPullback_inv_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, (hY n).w,
        ← Category.assoc, IsPullback.isoPullback_inv_snd]

end S_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isClosedImmersion_proj_of_isAdicComplete (solution)
