-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cfba0479-881d-564b-99c0-040ba22f7218

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm CategoryTheory.MonoidalCategory"

namespace B0kBody

theorem nonempty_iso_of_nonempty_pullback_iso {X Y : Scheme.{0}} (e : X ⟶ Y) [IsIso e] (M M' : Y.Modules)
    (h : Nonempty ((Scheme.Modules.pullback e).obj M ≅ (Scheme.Modules.pullback e).obj M')) : Nonempty (M ≅ M') := by
  obtain ⟨φ⟩ := h
  have hid : inv e ≫ e = 𝟙 Y := IsIso.inv_hom_id e

  let c : ∀ N : Y.Modules, N ≅ (Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj N) := fun N =>
    ((Scheme.Modules.pullbackId Y).app N).symm ≪≫ ((Scheme.Modules.pullbackCongr hid).app N).symm ≪≫
      ((Scheme.Modules.pullbackComp (inv e) e).app N).symm
  exact ⟨c M ≪≫ (Scheme.Modules.pullback (inv e)).mapIso φ ≪≫ (c M').symm⟩

end B0kBody

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (y : L.AlgPoints hc k) :
    Polarisation.MemKernel f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap k k))) (RelativeGroupLaw.AlgPoints.toPoint y) ↔
      Nonempty ((Scheme.Modules.pullback (RiemannForm.translation f L (RelativeGroupLaw.AlgPoints.toPoint y))).obj 𝓛 ≅ 𝓛) := by
  set t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k)) with ht
  set x : SchemeHomOver t f := RelativeGroupLaw.AlgPoints.toPoint y with hx
  have ht1 : t = 𝟙 _ := RiemannForm.specMap_algebraMap_self
  haveI : IsIso t := by rw [ht1]; infer_instance

  have h1 : Polarisation.MemKernel f L 𝓛 t x ↔ L.IsInStabilizer 𝓛 t x :=
    (AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit k f L 𝓛 h𝓛 k t x).symm
  have h2 : L.IsInStabilizer 𝓛 t x ↔
      Nonempty ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛 ≅ (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) :=
    AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_field (pullback.snd f t) _ _
  rw [h1, h2]

  have h3 : L.mulRight t x = pullback.fst f t ≫ RiemannForm.translation f L x := by
    have nat := L.mul_natural f (pullback.snd f t ≫ t) (pullback.fst f t) pullback.condition
      RelativeGroupLaw.idPoint (constPt f x)
    have hP : schemeHomOverComp (pullback.fst f t) pullback.condition RelativeGroupLaw.idPoint = L.fstPoint t :=
      Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.fstPoint_coe]; exact Category.comp_id _)
    have hQ : schemeHomOverComp (pullback.fst f t) pullback.condition (constPt f x) = L.sndPoint t x := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.sndPoint_coe]
      change pullback.fst f t ≫ (f ≫ x.1) = pullback.snd f t ≫ x.1
      rw [← Category.assoc, pullback.condition, Category.assoc, congrArg (· ≫ x.1) ht1, Category.id_comp]
    rw [hP, hQ] at nat
    have h4 := congrArg Subtype.val nat
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h4
    exact h4.symm

  have c3 : (Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛 ≅
      (Scheme.Modules.pullback (pullback.fst f t)).obj
        ((Scheme.Modules.pullback (RiemannForm.translation f L x)).obj 𝓛) :=
    (Scheme.Modules.pullbackCongr h3).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f t) (RiemannForm.translation f L x)).app 𝓛).symm
  constructor
  · rintro ⟨φ⟩
    exact B0kBody.nonempty_iso_of_nonempty_pullback_iso (pullback.fst f t) _ _ ⟨c3.symm ≪≫ φ⟩
  · rintro ⟨ψ⟩
    exact ⟨c3 ≪≫ (Scheme.Modules.pullback (pullback.fst f t)).mapIso ψ⟩

end S_AlgebraicGeometry_Polarisation_memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_memKernel_iff_nonempty_pullback_translation_iso_of_isAlgClosed (solution)
