-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_polynomial_isUnit_aeval_imp_etale_levelSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6ea21955-9c6f-51f5-8170-2c87de5fa29e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet
import Theorems.Thm_AlgebraicGeometry_isDomain_tensorProduct_sections_of_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (hε : ∀ x : C, x ∈ U₀ ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U₀)) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
        IsUnit (Polynomial.aeval s D) →
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Algebra.Etale S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀

  have hft : (c.appLE ⊤ U₀ le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) c inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨U₀, hU₀⟩ le_top
  have hft' : (algebraMap R Γ(C, U₀)).FiniteType := by
    show ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U₀ le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType R Γ(C, U₀) := hft'
  haveI : Algebra.FinitePresentation R Γ(C, U₀) := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  haveI : Nontrivial (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀)) := by
    obtain ⟨-, hfree, hrank⟩ := hls (IsLocalRing.ResidueField R) 0
    haveI := hfree
    haveI : Nontrivial (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀) ⧸ Ideal.span
        {(1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f - (0 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 : Γ(C, U₀))}) :=
      Module.nontrivial_of_finrank_pos (R := IsLocalRing.ResidueField R) (by rw [hrank]; omega)
    exact (Ideal.Quotient.mk_surjective (I := Ideal.span
        {(1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f - (0 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 : Γ(C, U₀))})).nontrivial
  haveI : IsDomain (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀)) :=
    AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U₀ hU₀
      (IsLocalRing.ResidueField R) inferInstance
  exact Algebra.exists_polynomial_isUnit_aeval_imp_etale_levelSet R Γ(C, U₀) f m hm hls

end S_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet (solution)
