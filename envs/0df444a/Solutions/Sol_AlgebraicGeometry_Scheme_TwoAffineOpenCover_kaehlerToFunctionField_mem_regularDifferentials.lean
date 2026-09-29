-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/03f691d2-cad9-58f3-afe2-37ae6540b2ea

import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Theorems.Thm_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace RegR2

theorem ne_top_of_isAffineOpen {X : Scheme.{u}} (hX : ¬ IsAffine X) {U : X.Opens} (hU : IsAffineOpen U) :
    U ≠ ⊤ := by
  rintro rfl
  apply hX
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso (Scheme.topIso X).inv

end RegR2

theorem solution
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1]
    (ω : (𝒱.kaehlerSections c).H0) :
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c 𝒱.U0 ω.val.1 ∈ regularDifferentials k X.functionField := by
  letI := (baseToFunctionField c).toAlgebra

  have h0ne : (𝒱.U0 : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty 𝒱.U0); exact ⟨x.1, x.2⟩
  have h1ne : (𝒱.U1 : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty 𝒱.U1); exact ⟨x.1, x.2⟩
  obtain ⟨x₀, hx₀⟩ := nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen h0ne h1ne
  have hx₀' : x₀ ∈ 𝒱.U0 ⊓ 𝒱.U1 := TopologicalSpace.Opens.mem_inf.mpr ⟨hx₀.1, hx₀.2⟩

  have hgerm : kaehlerToFunctionField c 𝒱.U0 ω.val.1 = kaehlerToFunctionField c 𝒱.U1 ω.val.2 := by
    refine @Scheme.TwoAffineOpenCover.kaehlerToFunctionField_fst_eq_snd_of_mem_H0 k _ X 𝒱 c _ _ _ ?_ ω
    exact ⟨⟨x₀, hx₀'⟩⟩
  rw [AlgebraicCurve.mem_regularDifferentials_iff]
  intro v
  have hX : ¬ IsAffine X := AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hU0 : 𝒱.U0 ≠ ⊤ := RegR2.ne_top_of_isAffineOpen hX 𝒱.isAffineOpen_U0
  have hU1 : 𝒱.U1 ≠ ⊤ := RegR2.ne_top_of_isAffineOpen hX 𝒱.isAffineOpen_U1
  obtain ⟨hunion, -, -⟩ :=
    AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hU0 hU1
  have hv : v ∈ AlgebraicCurve.placesOf c 𝒱.U0 ∪ AlgebraicCurve.placesOf c 𝒱.U1 := by
    rw [hunion]; exact Set.mem_univ v
  rcases hv with h0 | h1
  · exact AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf c 𝒱.U0 ω.val.1 v h0
  · obtain ⟨f, hf, h⟩ :=
      AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf c 𝒱.U1 ω.val.2 v h1
    refine ⟨f, hf, ?_⟩
    rw [hgerm]
    exact h

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials (solution)
