-- Prove2me | solution 1 for AlgebraicGeometry.IdealSheafData.flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0c4dabb6-7d61-50bc-a297-d6d09a2ea1f7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 3200000

namespace SatFlat

theorem ringHom_flat_mk_comp {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type u} [CommRing A]
    (θ : O →+* A) (J : Ideal A) (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ s : A, θ ϖ * s ∈ J → s ∈ J) :
    ((Ideal.Quotient.mk J).comp θ).Flat := by
  classical
  letI : Algebra O (A ⧸ J) := ((Ideal.Quotient.mk J).comp θ).toAlgebra
  show Module.Flat O (A ⧸ J)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have hpow : ∀ (n : ℕ) (s : A), θ ϖ ^ n * s ∈ J → s ∈ J := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      have h1 : θ ϖ ^ k * (θ ϖ * s) ∈ J := by
        rw [show θ ϖ ^ k * (θ ϖ * s) = θ ϖ ^ (k + 1) * s by ring]; exact hs
      exact hsat ϖ hϖ s (ih _ h1)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro m hm
  rw [Submodule.mem_torsion_iff] at hm
  obtain ⟨⟨a, ha⟩, ham⟩ := hm
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m

  have h1 : Ideal.Quotient.mk J (θ ((u : O) * ϖ ^ n) * s) = 0 := by
    rw [map_mul (Ideal.Quotient.mk J)]
    exact ham
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1 ⊢
  have h2 : θ ϖ ^ n * s ∈ J := by
    have := J.mul_mem_left (θ (↑u⁻¹ : O)) h1
    rwa [← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow] at this
  exact hpow n s h2

end SatFlat

open SatFlat in

theorem solution
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of O)) (J : X.IdealSheafData)
    (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : X.affineOpens) (s : Γ(X, U)),
        X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
            (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ J.ideal U →
          s ∈ J.ideal U) :
    Flat (J.subschemeι ≫ q) := by

  classical

  rw [HasRingHomProperty.iff_of_source_openCover (P := @Flat) J.subschemeCover.openCover]
  intro U
  change X.affineOpens at U

  have hU : IsAffineOpen (U : X.Opens) := U.2
  set θ : O →+* Γ(X, U) := (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom with hθ
  have hmor : J.subschemeCover.openCover.f U ≫ J.subschemeι ≫ q =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (J.ideal U)).comp θ)) := by
    show J.subschemeCover.f U ≫ J.subschemeι ≫ q = _
    rw [← Category.assoc, J.subschemeCover_map_subschemeι U]
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) ≫ hU.isoSpec.inv) ≫ (U : X.Opens).ι ≫ q = _
    rw [Category.assoc, hU.isoSpec_inv_ι_assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [hmor]

  have key : ((Ideal.Quotient.mk (J.ideal U)).comp θ).Flat := by
    refine ringHom_flat_mk_comp θ (J.ideal U) (fun ϖ hϖ s hs => hsat ϖ hϖ U s ?_)
    have : θ ϖ = X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) := by
      rw [hθ, RingHom.comp_apply]
      show (q.appLE ⊤ U le_top).hom _ = _
      rw [Scheme.Hom.appLE]
      rfl
    rw [← this]; exact hs
  have := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom ((Ideal.Quotient.mk (J.ideal U)).comp θ))).mpr key
  exact HasRingHomProperty.appTop (P := @Flat) _ this

end S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_IdealSheafData_flat_subschemeInclusion_comp_of_forall_mul_mem_of_isDiscreteValuationRing (solution)
