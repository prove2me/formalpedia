-- Prove2me | solution 1 for AlgebraicGeometry.specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/abfe668d-17a4-5e5b-9d55-dc9405e8cadd

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq.AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift Surjective morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom IsAffineOpen.fromSpec_top IsAffineOpen.isoSpec_inv_ι IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsOpenImmersion isAffineOpen_top IsAffineOpen Scheme.Opens IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.TwoAffineOpenCover"
namespace P2mRedFixed
p2m_open "AlgebraicGeometry"

theorem _root_.P2MW.S_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq.solution
    {B B₁ : Type u} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₁ : X₁ ⟶ Spec (CommRingCat.of B₁)) (g : X₁ ⟶ X)
    (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (U : X.Opens) (hU : IsAffineOpen U)
    (α : (U : Scheme.{u}) ⟶ U) (hα : (g ∣_ U) ≫ α = g ∣_ U) :
    letI := algebraOfHom f U
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.fromSpec
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫
          hU.isoSpec.inv ≫ α ≫ U.ι := by
  letI := algebraOfHom f U

  have hfromf : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h1
    exact h1.symm

  have hρE : ∃ ρ : B₁ →+* (Γ(X, U) ⧸ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))),
      ρ.comp (algebraMap B B₁) =
        (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))).comp (algebraMap B Γ(X, U)) := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker (algebraMap B B₁))
      ((Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))).comp (algebraMap B Γ(X, U)))
      fun b hb => ?_).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hb
    · ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      have : (RingHom.quotientKerEquivOfSurjective hπ).symm (algebraMap B B₁ b) = Ideal.Quotient.mk _ b :=
        (RingHom.quotientKerEquivOfSurjective hπ).symm_apply_eq.mpr rfl
      rw [this, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  obtain ⟨ρ, hρ⟩ := hρE

  have hw : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫
      hU.fromSpec) ≫ f = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) := by
    rw [Category.assoc, hfromf, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hρ]
  have hε₀ := hg.lift_fst _ _ hw

  have hrange : Set.range (hg.lift _ _ hw).base ⊆ Set.range (g ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    show g.base ((hg.lift _ _ hw).base y) ∈ (U : Set X)
    have hy := congrArg (fun φ => φ.base y) hε₀
    simp only [Scheme.Hom.comp_apply] at hy
    rw [hy]
    exact hU.range_fromSpec.le ⟨_, rfl⟩
  have hε := IsOpenImmersion.lift_fac (g ⁻¹ᵁ U).ι (hg.lift _ _ hw) hrange
  have hεs : IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (hg.lift _ _ hw) hrange ≫ (g ∣_ U) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫
        hU.isoSpec.inv := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hε, hε₀, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι]

  calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.fromSpec
      = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫
          hU.isoSpec.inv) ≫ U.ι := by rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    _ = (IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (hg.lift _ _ hw) hrange ≫ ((g ∣_ U) ≫ α)) ≫ U.ι := by rw [hα, hεs]
    _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫
          hU.isoSpec.inv ≫ α ≫ U.ι := by rw [← Category.assoc _ (g ∣_ U) α, hεs]; simp only [Category.assoc]

end AlgebraicGeometry.P2mRedFixed

end S_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq (solution)
