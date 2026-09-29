-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6382dc15-19f2-5a8c-8f00-9ae7c5f49501

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped TensorProduct

theorem solution
    (K K' : Type) [Field K] [Field K'] [Algebra K K']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsProper f] (f' : A' ⟶ Spec (CommRingCat.of K'))
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (𝒦 : A.OrderedAffineCover) (𝒦' : A'.OrderedAffineCover) :
    (OModulePresheaf.ofModules f' ((Scheme.Modules.pullback g).obj M)).eulerChar 𝒦' =
      (OModulePresheaf.ofModules f M).eulerChar 𝒦 := by

  let p := pullback.fst f (Scheme.TwoAffineOpenCover.specMap K K')
  let q := pullback.snd f (Scheme.TwoAffineOpenCover.specMap K K')
  let Φ : A' ⟶ pullback f (Scheme.TwoAffineOpenCover.specMap K K') := hg.isoPullback.hom
  have hΦp : Φ ≫ p = g := hg.isoPullback_hom_fst
  have hΦq : Φ ≫ q = f' := hg.isoPullback_hom_snd
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback p).obj M) := hM.pullback p

  have e : (Scheme.Modules.pullback Φ).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback g).obj M :=
    (Scheme.Modules.pullbackComp Φ p).app M ≪≫ (Scheme.Modules.pullbackCongr hΦp).app M

  have hdeg : ∀ n : ℕ,
      (OModulePresheaf.ofModules f' ((Scheme.Modules.pullback g).obj M)).cechFinrank 𝒦' n =
        (OModulePresheaf.ofModules f M).cechFinrank 𝒦 n := by
    intro n

    have h1 := OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso q Φ
      ((Scheme.Modules.pullback p).obj M) hN 𝒦' (𝒦.baseChange f K') n
    have h2 : (OModulePresheaf.ofModules (Φ ≫ q)
          ((Scheme.Modules.pullback Φ).obj ((Scheme.Modules.pullback p).obj M))).cechFinrank 𝒦' n =
        (OModulePresheaf.ofModules (Φ ≫ q) ((Scheme.Modules.pullback g).obj M)).cechFinrank 𝒦' n := by
      obtain ⟨⟨e0⟩, eS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso (Φ ≫ q) e 𝒦'
      cases n with
      | zero => simp only [OModulePresheaf.cechFinrank_zero]; exact e0.finrank_eq
      | succ i => obtain ⟨ei⟩ := eS i; simp only [OModulePresheaf.cechFinrank_succ]; exact ei.finrank_eq
    rw [← hΦq, ← h2, h1]

    obtain ⟨-, hflat⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒦 M
      hM.exists_trivialization K'
    obtain ⟨⟨E0⟩, ES⟩ := hflat inferInstance
    cases n with
    | zero =>
      rw [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero, E0.finrank_eq,
        Module.finrank_baseChange]
    | succ i =>
      obtain ⟨Ei⟩ := ES i
      rw [OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ, Ei.finrank_eq,
        Module.finrank_baseChange]

  obtain ⟨-, -, -, hK⟩ := OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    (OModulePresheaf.ofModules f M) 𝒦
  obtain ⟨-, -, -, hK'⟩ := OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    (OModulePresheaf.ofModules f' ((Scheme.Modules.pullback g).obj M)) 𝒦'
  rw [(hK' inferInstance).2 (max (Fintype.card 𝒦.ι) (Fintype.card 𝒦'.ι)) (le_max_right _ _),
    (hK inferInstance).2 (max (Fintype.card 𝒦.ι) (Fintype.card 𝒦'.ι)) (le_max_left _ _)]
  exact Finset.sum_congr rfl fun i _ => by rw [hdeg i]

end S_AlgebraicGeometry_OModulePresheaf_eulerChar_pullback_eq_eulerChar_of_isPullback_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_pullback_eq_eulerChar_of_isPullback_of_field (solution)
