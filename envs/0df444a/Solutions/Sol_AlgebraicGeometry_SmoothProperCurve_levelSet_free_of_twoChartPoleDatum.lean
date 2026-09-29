-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/df9bc545-a67e-51e5-bc8e-408f289c807d

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum
import Theorems.Thm_Algebra_levelSet_finite_free_finrank_of_flat_polynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have hflat := AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
    R c ε U V hU hV hUV hUε f g hf hg hfg
  have hrk : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m :=
    fun L _ _ x => AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum
      R c ε U V hU hV hUV hUε f g hf hg hfg m hfree hrank hfin hfinV L x
  exact Algebra.levelSet_finite_free_finrank_of_flat_polynomial R Γ(C, U) f m hfin hflat hrk

end S_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum (solution)
