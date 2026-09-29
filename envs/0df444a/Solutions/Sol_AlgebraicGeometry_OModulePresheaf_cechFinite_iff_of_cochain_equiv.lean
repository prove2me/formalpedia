-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5da6ceca-58b2-5059-b8e9-0ef548b13c11

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf OModulePresheaf.cechFinite_iff"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "cochain d HSucc CechFinite cechFinite_iff"
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section CochainEquiv

variable {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
variable (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q)
variable (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x))

include he in
theorem d_comp_equiv (q : ℕ) :
    G.d K' q ∘ₗ (e q : F.cochain K q →ₗ[R] G.cochain K' q) = (e (q + 1) : _ →ₗ[R] _) ∘ₗ F.d K q :=
  LinearMap.ext fun x => (he q x).symm

include he in
theorem map_ker_d (q : ℕ) :
    Submodule.map (e q : F.cochain K q →ₗ[R] G.cochain K' q) (LinearMap.ker (F.d K q)) = LinearMap.ker (G.d K' q) := by
  rw [Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp, ← LinearEquiv.ker_comp (e (q + 1))]
  congr 1
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [he, LinearEquiv.apply_symm_apply]

def kerEquiv (q : ℕ) : LinearMap.ker (F.d K q) ≃ₗ[R] LinearMap.ker (G.d K' q) :=
  LinearEquiv.ofSubmodules (e q) _ _ (map_ker_d F G K K' e he q)

theorem kerEquiv_apply_coe (q : ℕ) (x : LinearMap.ker (F.d K q)) :
    (kerEquiv F G K K' e he q x).1 = e q x.1 := rfl

include he in
theorem map_comap_range (q : ℕ) :
    Submodule.map (kerEquiv F G K K' e he (q + 1) : _ →ₗ[R] _)
        ((LinearMap.range (F.d K q)).comap (LinearMap.ker (F.d K (q + 1))).subtype)
      = (LinearMap.range (G.d K' q)).comap (LinearMap.ker (G.d K' (q + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    exact ⟨e q z, by show G.d K' q (e q z) = e (q + 1) x.1; rw [← he, hz]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(kerEquiv F G K K' e he (q + 1)).symm y, ⟨(e q).symm z, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    apply (e (q + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hz]
    exact (congrArg Subtype.val ((kerEquiv F G K K' e he (q + 1)).apply_symm_apply y)).symm

def hSuccEquiv (q : ℕ) : F.HSucc K q ≃ₗ[R] G.HSucc K' q :=
  Submodule.Quotient.equiv _ _ (kerEquiv F G K K' e he (q + 1)) (map_comap_range F G K K' e he q)

include he in

theorem cechFinite_iff_of_cochainEquiv : F.CechFinite K ↔ G.CechFinite K' := by
  rw [OModulePresheaf.cechFinite_iff, OModulePresheaf.cechFinite_iff]
  refine ⟨fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩, fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩⟩
  · haveI := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0)
  · haveI := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q)
  · haveI := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0).symm
  · haveI := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q).symm

end CochainEquiv

end AlgebraicGeometry.OModulePresheaf

end

theorem solution
    {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q) (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x)) :
    F.CechFinite K ↔ G.CechFinite K' :=
  AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochainEquiv F G K K' e he

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv (solution)
