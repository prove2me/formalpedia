-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_subsingleton_HSucc_restrict_of_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/195b28aa-4bde-5eef-8ee7-0873b2df6d3e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_orderedAffineCover_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔛 : X.OrderedAffineCover) (𝔙 : (V : Scheme.{u}).OrderedAffineCover)
    (𝔚 : ((U ⊓ V : X.Opens) : Scheme.{u}).OrderedAffineCover)
    (hX : (OModulePresheaf.ofModules π N).H0 𝔛 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛 i))
    (hW : (OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).H0 𝔚 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules ((U ⊓ V).ι ≫ π) (N.restrict (U ⊓ V).ι)).HSucc 𝔚 i)) :
    (OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).H0 𝔙 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).HSucc 𝔙 i) := by
  classical
  obtain ⟨𝔘⟩ := Scheme.nonempty_orderedAffineCover_of_sup_eq_top U V hUV 𝔛 𝔚
  obtain ⟨𝔛', eV, eU, hV, hU, hlt, hcov⟩ :=
    Scheme.exists_orderedAffineCover_orderEmbedding_of_sup_eq_top U V hUV 𝔙 𝔘
  obtain ⟨⟨e0⟩, he⟩ :=
    OModulePresheaf.nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated π N hN 𝔛 𝔛'
  have h0 : Subsingleton ((OModulePresheaf.ofModules π N).H0 𝔛) := by
    rw [hX.1]; infer_instance
  have h0' : Subsingleton ((OModulePresheaf.ofModules π N).H0 𝔛') := e0.symm.toEquiv.subsingleton
  have hX' : (OModulePresheaf.ofModules π N).H0 𝔛' = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛' i) := by
    refine ⟨(Submodule.eq_bot_iff _).mpr fun x hx => ?_, fun i => ?_⟩
    · have := Subsingleton.elim (⟨x, hx⟩ : (OModulePresheaf.ofModules π N).H0 𝔛') ⟨0, Submodule.zero_mem _⟩
      exact congrArg Subtype.val this
    · obtain ⟨e⟩ := he i
      haveI := hX.2 i
      exact e.symm.toEquiv.subsingleton
  have hD := OModulePresheaf.subsingleton_HTot_biCech_imageFamily_of_forall_subsingleton_HSucc
    π N hN U V 𝔙 𝔘 𝔚 hW
  exact OModulePresheaf.H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
    π N U V 𝔙 𝔘 𝔛' eV eU hV hU hlt hcov hX' hD

end S_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_subsingleton_HSucc_restrict_of_sup_eq_top (solution)
