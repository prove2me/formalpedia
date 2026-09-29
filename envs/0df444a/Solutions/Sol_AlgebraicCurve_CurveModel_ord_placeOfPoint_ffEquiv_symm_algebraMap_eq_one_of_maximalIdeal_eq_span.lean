-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4eac5b0c-adf3-52c3-8e93-3d18a2c52ecb

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

theorem solution
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (x : closedPoints M.C) (g : M.C.presheaf.stalk x.1)
    (hg : IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) = Ideal.span {g}) :
    (M.placeOfPoint x).ord (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g)) = 1 := by
  set V := (M.placeOfPoint x).toValuationSubring with hV
  set θ : M.C.presheaf.stalk x.1 →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) with hθ_def
  have hθ : ∀ s, θ s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField s) := fun s => rfl
  have hθ_inj : Function.Injective θ :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField)
  have hrange : θ.range = V.toSubring := M.range_stalk_eq x
  have hmemV : ∀ s, θ s ∈ V := fun s => by
    have : θ s ∈ θ.range := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  set ψ : M.C.presheaf.stalk x.1 →+* V := θ.codRestrict V hmemV with hψ_def
  have hψ : ∀ s, ((ψ s : V) : L) = θ s := fun s => rfl
  have hψ_bij : Function.Bijective ψ := by
    refine ⟨fun a b hab => hθ_inj (by rw [← hψ, ← hψ, hab]), fun y => ?_⟩
    have hy : (y : L) ∈ θ.range := by rw [hrange]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext (by rw [hψ, hs])⟩
  set ε : M.C.presheaf.stalk x.1 ≃+* V := RingEquiv.ofBijective ψ hψ_bij with hε_def
  have hε : ∀ s, ((ε s : V) : L) = θ s := fun s => rfl

  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {ε g} := by
    have h1 : Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) = IsLocalRing.maximalIdeal V := by
      have hM : (Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))).IsMaximal :=
        Ideal.map_isMaximal_of_equiv ε
      exact IsLocalRing.eq_maximalIdeal hM
    rw [← h1, hg, Ideal.map_span, Set.image_singleton]
  have hg0 : (ε g : V) ≠ 0 := by
    intro h0
    have hbot : IsLocalRing.maximalIdeal V = ⊥ := by rw [hmax, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_a_field V hbot
  have hirr : Irreducible (ε g : V) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (ε g) hg0 hmax
  rw [← hθ, ← hε]
  exact (M.placeOfPoint x).ord_coe_irreducible hirr

end S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span (solution)
