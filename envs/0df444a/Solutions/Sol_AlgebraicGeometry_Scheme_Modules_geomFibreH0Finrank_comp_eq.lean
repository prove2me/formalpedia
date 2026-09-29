-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/58966542-05bf-51f6-a752-a1b99f4f3822

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace K63

open TensorProduct in

theorem finrank_H0_eq {k : Type u} [Field k] (G : CoherentBaseChange.TwoTermComplex.{u, u} k)
    (A : Type u) [Field A] [Algebra k A] :
    Module.finrank A (G.H0 A) = Module.finrank k (LinearMap.ker G.d) := by
  have hinj : Function.Injective ((LinearMap.ker G.d).subtype.baseChange A) := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (LinearMap.ker G.d).subtype
      (LinearMap.ker G.d).injective_subtype
    intro x y hxy
    exact this hxy
  have hexact : Function.Exact ((LinearMap.ker G.d).subtype.baseChange A) (G.d.baseChange A) := by
    have := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map G.d)
    intro y
    exact this y
  have hbij : Function.Bijective (G.kerBaseChangeHom A) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hinj
      have h := congrArg Subtype.val hxy
      simpa only [CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_apply_coe] using h
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (hexact y).mp hy
      exact ⟨x, Subtype.ext (by
        simpa only [CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_apply_coe] using hx)⟩
  rw [← (LinearEquiv.ofBijective (G.kerBaseChangeHom A) hbij).finrank_eq, Module.finrank_baseChange]

theorem geomFibreH0Finrank_field {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [IsProper g]
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (K : Type u) [Field K] (j : k →+* K) :
    Scheme.Modules.geomFibreH0Finrank g N K j =
      Scheme.Modules.geomFibreH0Finrank g N k (RingHom.id k) := by
  letI : Algebra k K := j.toAlgebra
  obtain ⟨G, ε₀, ε, -⟩ :=
    Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange g N hN.exists_trivialization
  letI instK := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (pullback.snd g (Scheme.TwoAffineOpenCover.specMap k K))
    ((Scheme.Modules.pullback (pullback.fst g (Scheme.TwoAffineOpenCover.specMap k K))).obj N) ⊤
  letI instk := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (pullback.snd g (Scheme.TwoAffineOpenCover.specMap k k))
    ((Scheme.Modules.pullback (pullback.fst g (Scheme.TwoAffineOpenCover.specMap k k))).obj N) ⊤
  have eK : Γ((Scheme.Modules.pullback (pullback.fst g (Scheme.TwoAffineOpenCover.specMap k K))).obj N, ⊤)
      ≃ₗ[K] G.H0 K := ε K
  have ek : Γ((Scheme.Modules.pullback (pullback.fst g (Scheme.TwoAffineOpenCover.specMap k k))).obj N, ⊤)
      ≃ₗ[k] G.H0 k := ε k
  have hK : Scheme.Modules.geomFibreH0Finrank g N K j = Module.finrank K (G.H0 K) := by
    unfold Scheme.Modules.geomFibreH0Finrank
    exact eK.finrank_eq
  have hk : Scheme.Modules.geomFibreH0Finrank g N k (RingHom.id k) = Module.finrank k (G.H0 k) := by
    unfold Scheme.Modules.geomFibreH0Finrank
    exact ek.finrank_eq
  rw [hK, hk, finrank_H0_eq G K, finrank_H0_eq G k]

end K63

open K63 in

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (k K : Type u) [Field k] [Field K] (sk : S →+* k) (j : k →+* K) :
    Scheme.Modules.geomFibreH0Finrank f M K (j.comp sk) = Scheme.Modules.geomFibreH0Finrank f M k sk := by
  have hc : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))
      (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) f (Spec.map (CommRingCat.ofHom sk)) :=
    IsPullback.of_hasPullback _ _
  have h1 := Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk f
    (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) (pullback.fst f (Spec.map (CommRingCat.ofHom sk))) hc
    M _ (Iso.refl _) K j
  have h2 := Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk f
    (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) (pullback.fst f (Spec.map (CommRingCat.ofHom sk))) hc
    M _ (Iso.refl _) k (RingHom.id k)
  rw [RingHom.id_comp] at h2
  rw [← h1, ← h2]
  exact K63.geomFibreH0Finrank_field _ _ (hM.pullback _) K j

end S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq (solution)
