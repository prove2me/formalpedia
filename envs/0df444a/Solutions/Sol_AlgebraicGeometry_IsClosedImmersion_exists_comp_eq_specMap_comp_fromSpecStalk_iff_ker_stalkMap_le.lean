-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/72bcb91d-030c-5996-a993-ba3b35683193

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace P2Factor

theorem isLocalHom_mk {R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R) [Nontrivial (R ⧸ J)] :
    IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom :=
  IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

end P2Factor

theorem solution
    {A K : Scheme.{0}} (κ : K ⟶ A) [IsClosedImmersion κ] (y' : K)
    (J : Ideal (A.presheaf.stalk (κ.base y'))) :
    (∃ t : Spec (CommRingCat.of ((A.presheaf.stalk (κ.base y')) ⧸ J)) ⟶ K,
        t ≫ κ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ A.fromSpecStalk (κ.base y')) ↔
      RingHom.ker (κ.stalkMap y').hom ≤ J := by
  classical
  constructor
  ·
    rintro ⟨t, ht⟩
    by_cases hJ : J = ⊤
    · rw [hJ]; exact le_top
    haveI : Nontrivial ((A.presheaf.stalk (κ.base y')) ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    haveI : IsLocalRing ((A.presheaf.stalk (κ.base y')) ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := P2Factor.isLocalHom_mk J
    set cp := IsLocalRing.closedPoint ((A.presheaf.stalk (κ.base y')) ⧸ J) with hcp

    have h1 : κ.base (t.base cp) = κ.base y' := by
      have := congrArg (fun f : Spec (CommRingCat.of ((A.presheaf.stalk (κ.base y')) ⧸ J)) ⟶ A => f.base cp) ht
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
      rw [this]
      erw [Spec_closedPoint]
      exact Scheme.fromSpecStalk_closedPoint
    have h2 : t.base cp = y' := κ.isClosedEmbedding.injective h1

    intro r hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨U, hyU, s, rfl⟩ := A.presheaf.exists_germ_eq r

    have key : ∀ (g : Spec (CommRingCat.of ((A.presheaf.stalk (κ.base y')) ⧸ J)) ⟶ A)
        (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ A.fromSpecStalk (κ.base y') = g)
        (hU : g.base cp ∈ U),
        Scheme.stalkClosedPointTo g (A.presheaf.germ U (g.base cp) hU s) =
          Ideal.Quotient.mk J (A.presheaf.germ U (κ.base y') hyU s) := by
      intro g hg hU
      subst hg
      have e := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom (Ideal.Quotient.mk J)) U hU
      have e' := congrArg (fun φ => φ.hom s) e
      simp at e'
      exact e'
    have hU' : (t ≫ κ).base cp ∈ U := by
      show κ.base (t.base cp) ∈ U
      rw [h1]; exact hyU
    have k1 := key (t ≫ κ) ht.symm hU'
    rw [Scheme.stalkClosedPointTo_comp] at k1

    have hz : ∀ (z : K) (hz' : κ.base z ∈ U), z = y' →
        κ.stalkMap z (A.presheaf.germ U (κ.base z) hz' s) = 0 := by
      rintro z hz' rfl
      exact hr
    have k2 : κ.stalkMap (t.base cp) (A.presheaf.germ U ((t ≫ κ).base cp) hU' s) = 0 := hz _ hU' h2
    have : Ideal.Quotient.mk J (A.presheaf.germ U (κ.base y') hyU s) = 0 := by
      rw [← k1]
      show Scheme.stalkClosedPointTo t (κ.stalkMap (t.base cp) (A.presheaf.germ U ((t ≫ κ).base cp) hU' s)) = 0
      rw [k2, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  ·
    intro hle
    have hsurj : Function.Surjective (κ.stalkMap y').hom := κ.stalkMap_surjective y'
    let e := RingHom.quotientKerEquivOfSurjective hsurj
    let ψ : K.presheaf.stalk y' →+* (A.presheaf.stalk (κ.base y')) ⧸ J :=
      (Ideal.Quotient.factor hle).comp e.symm.toRingHom
    have hψ : ψ.comp (κ.stalkMap y').hom = Ideal.Quotient.mk J := by
      ext r
      simp only [ψ, e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.factor_mk]
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ K.fromSpecStalk y', ?_⟩
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
    congr 2
    ext r
    exact congrArg (fun φ : _ →+* _ => φ r) hψ

end S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_specMap_comp_fromSpecStalk_iff_ker_stalkMap_le (solution)
