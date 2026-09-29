-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_isAffineOpen_le_preimage_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c949fcae-a9e6-5162-bbc4-08311d10dc74

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset C)
    (hF : ∀ x ∈ F, c x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ U : C.Opens, IsAffineOpen U ∧ U ≤ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨π, h0, h1, -, -, -⟩ := 𝔉.exists_hom_proj_preimage_basicOpen_eq

  have hX : ∀ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) R) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
    fun i => ProjSpace.X_mem_one R 1 i
  have hcovP : (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R 1)
  haveI : IsAffineHom π := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    have hy : y ∈ (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) := by
      rw [hcovP]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ (hX i) one_pos, ?_⟩
    fin_cases i
    · simpa [h0] using 𝔉.isAffineOpen_U
    · simpa [h1] using 𝔉.isAffineOpen_V

  obtain ⟨W, hW, hFW⟩ := AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj (MvPolynomial.homogeneousSubmodule (Fin 2) R) π F

  haveI : IsAffine W := hW
  refine ⟨W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)), ?_, ?_, ?_⟩
  · exact (V.2.preimage (W.ι ≫ c)).image_of_isOpenImmersion W.ι
  · have : W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)) =
        W ⊓ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [this]; exact inf_le_right
  · intro x hx
    refine ⟨⟨x, hFW x hx⟩, ?_, rfl⟩
    show c (W.ι ⟨x, hFW x hx⟩) ∈ (V : (Spec (CommRingCat.of R)).Opens)
    simpa using hF x hx

end S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset (solution)
