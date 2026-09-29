-- Prove2me | solution 1 for AlgebraicGeometry.IsFinite.finite_hom_stalkMap_of_forall_base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4040c39a-1cb9-5ffd-af4f-4badb91bdeea

import Mathlib
import Theorems.Thm_RingHom_Finite_finite_localRingHom_of_forall_comap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Ws44SF

universe u

theorem finite_stalkMap_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Finite) (p : ↥(Spec S))
    (hp : ∀ p' : ↥(Spec S), (Spec.map φ).base p' = (Spec.map φ).base p → p' = p) :
    ((Spec.map φ).stalkMap p).hom.Finite := by
  rw [RingHom.finite_respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  refine RingHom.Finite.finite_localRingHom_of_forall_comap_eq φ.hom hφ p.asIdeal ?_
  intro Q hQ hcomap
  have h := hp ⟨Q, hQ⟩ (PrimeSpectrum.ext hcomap)
  exact congrArg PrimeSpectrum.asIdeal h

set_option backward.isDefEq.respectTransparency false in

theorem finite_stalkMap_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X ⟶ Y) [IsFinite g] (x : X)
    (hx : ∀ x' : X, g.base x' = g.base x → x' = x) : (g.stalkMap x).hom.Finite := by
  have hQ' := RingHom.finite_respectsIso
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ g ≫ Y.isoSpec.hom)
  haveI : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hφfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have key : ((Spec.map φ).stalkMap (X.isoSpec.hom.base x)).hom.Finite := by
    refine finite_stalkMap_SpecMap φ hφfin _ (fun p' hp' => ?_)
    rw [hφ] at hp'
    have h1 : Y.isoSpec.hom.base (g.base (X.isoSpec.inv.base p')) =
        Y.isoSpec.hom.base (g.base (X.isoSpec.inv.base (X.isoSpec.hom.base x))) := by
      have e1 : ∀ q, (X.isoSpec.inv ≫ g ≫ Y.isoSpec.hom).base q = Y.isoSpec.hom.base (g.base (X.isoSpec.inv.base q)) :=
        fun q => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      rw [← e1, ← e1]
      exact hp'
    have h2 : g.base (X.isoSpec.inv.base p') = g.base (X.isoSpec.inv.base (X.isoSpec.hom.base x)) := by
      have := congrArg (fun z => Y.isoSpec.inv.base z) h1
      simpa only [Scheme.hom_inv_apply] using this
    rw [Scheme.hom_inv_apply] at h2
    have h3 : X.isoSpec.inv.base p' = x := hx _ h2
    calc p' = X.isoSpec.hom.base (X.isoSpec.inv.base p') := (Scheme.inv_hom_apply _ _).symm
      _ = X.isoSpec.hom.base x := by rw [h3]
  rw [hφ, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, hQ'.cancel_right_isIso,
    CommRingCat.hom_comp, hQ'.cancel_left_isIso] at key
  have heq : X.isoSpec.inv.base (X.isoSpec.hom.base x) = x := Scheme.hom_inv_apply _ _
  rwa [hQ'.arrow_mk_iso_iff (g.arrowStalkMapIsoOfEq heq)] at key

end Ws44SF

theorem solution
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hx : ∀ x' : X, f.base x' = f.base x → x' = x) :
    (f.stalkMap x).hom.Finite := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hfx, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  haveI : IsAffine (f ⁻¹ᵁ U) := hV
  haveI : IsAffine U := hU
  let x₀ : ↥(f ⁻¹ᵁ U) := ⟨x, hfx⟩
  rw [← RingHom.finite_respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap f U x₀)]
  refine Ws44SF.finite_stalkMap_of_isAffine (f ∣_ U) x₀ (fun x' h => ?_)
  apply Subtype.ext
  apply hx
  have h' := congrArg Subtype.val h
  rwa [morphismRestrict_base_coe, morphismRestrict_base_coe] at h'

end S_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsFinite_finite_hom_stalkMap_of_forall_base_eq (solution)
