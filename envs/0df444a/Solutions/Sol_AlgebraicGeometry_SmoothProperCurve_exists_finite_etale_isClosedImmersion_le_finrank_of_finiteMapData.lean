-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3f0e5f58-4d3c-5e30-b854-b828bfcd492c

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq
import Theorems.Thm_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_isClosedImmersion_levelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) (N : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀)
      (B : Type u) (_ : CommRing B) (_ : Algebra R₀ B) (_ : Module.Finite R₀ B) (_ : Algebra.Etale R₀ B)
      (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c R₀ = specMap R₀ B ∧ N ≤ Module.finrank R₀ B := by

  obtain ⟨𝔉, hNm, hgen⟩ := h𝔉 N
  obtain ⟨D, hD, hDet⟩ := hgen
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U

  obtain ⟨R₀, _, _, _, _, _, _, _, _, x, hx⟩ :=
    IsLocalRing.exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq R D.natDegree

  obtain ⟨i, hi⟩ := Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq D hD x hx

  obtain ⟨hfin, -, hrank⟩ := 𝔉.levelSet_free R₀ (x i)
  have het := hDet R₀ (x i) hi
  obtain ⟨ι, hιc, hιb⟩ := exists_isClosedImmersion_levelSet R c 𝔉.U 𝔉.isAffineOpen_U 𝔉.f R₀ (x i) hfin
  exact ⟨R₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (R₀ ⊗[R] Γ(C, 𝔉.U) ⧸ Ideal.span {(1 : R₀) ⊗ₜ[R] 𝔉.f - x i ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}), inferInstance, inferInstance, hfin, het, ι, hιc, hιb, by rw [hrank]; exact hNm⟩

end S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData (solution)
