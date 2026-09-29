-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8206858b-96e5-5663-ad2e-97cc6bd7b02e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by
  obtain ⟨G, α, β, ψ, hGc, hGq, hαβ, hβs, hψc, hψα, hψβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_affHom_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
      I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami
  exact AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq
    I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami G hGc hGq α β hαβ hβs ψ hψc hψα hψβ

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete (solution)
