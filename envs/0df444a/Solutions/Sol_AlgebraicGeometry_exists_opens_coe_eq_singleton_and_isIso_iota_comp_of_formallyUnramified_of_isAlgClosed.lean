-- Prove2me | solution 1 for AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/909e5841-8e27-5395-a3ba-370bb5d8b986

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [FormallyUnramified q] (x : H) :
    ∃ U : H.Opens, (U : Set H) = {x} ∧ IsIso (U.ι ≫ q) := by
  classical

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := H.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ

  let g : Spec Γ(H, V) ⟶ Spec (CommRingCat.of k) := hV.fromSpec ≫ q
  haveI hg1 : LocallyOfFiniteType g := inferInstance
  haveI hg2 : FormallyUnramified g := MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let φ : CommRingCat.of k ⟶ Γ(H, V) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; exact hg1
    exact HasRingHomProperty.Spec_iff.mp this
  have hur : φ.hom.FormallyUnramified := by
    have : FormallyUnramified (Spec.map φ) := by rw [hφ]; exact hg2
    exact HasRingHomProperty.Spec_iff.mp this

  algebraize [φ.hom]
  haveI : Algebra.FormallyUnramified k Γ(H, V) := hur
  haveI : Algebra.FiniteType k Γ(H, V) := hft
  have hfin : Module.Finite k Γ(H, V) := Algebra.FormallyUnramified.finite_of_free k Γ(H, V)
  haveI : IsFinite g := by
    rw [← hφ, IsFinite.SpecMap_iff]; exact hfin
  haveI : LocallyOfFinitePresentation g := by
    rw [← hφ]
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.FinitePresentation.of_finiteType.mp hft)
  haveI : Etale g := Etale.of_formallyUnramified_of_flat g

  let y : ↥(Spec Γ(H, V)) := hV.isoSpec.hom.base ⟨x, hxV⟩
  obtain ⟨U', hU', hiso⟩ := AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale g y

  refine ⟨hV.fromSpec ''ᵁ U', ?_, ?_⟩
  · rw [Scheme.Hom.coe_image, hU', Set.image_singleton]
    congr 1
    show (hV.isoSpec.hom ≫ hV.fromSpec).base ⟨x, hxV⟩ = x
    rw [← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rfl
  · have e : (hV.fromSpec ''ᵁ U').ι ≫ q = (hV.fromSpec.isoImage U').inv ≫ (U'.ι ≫ g) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
    rw [e]
    infer_instance

end S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed (solution)
