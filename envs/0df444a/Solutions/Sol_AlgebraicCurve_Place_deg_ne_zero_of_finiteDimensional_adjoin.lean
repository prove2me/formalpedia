-- Prove2me | solution 1 for AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4ea486c7-6c27-515b-8499-c3a84884c166

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_ne_zero
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) : v.deg ≠ 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) := transcendental_iff_injective.mp hx
  let lift : RatFunc K →ₐ[K] F :=
    RatFunc.liftAlgHom (Polynomial.aeval x) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  have hlift : ∀ p : Polynomial K, lift (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval x p := fun p => by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval x)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1
    rwa [map_one, div_one, map_one, div_one] at h
  letI : Algebra (RatFunc K) F := lift.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' (lift.comp_algebraMap).symm
  haveI hFD : FiniteDimensional (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp ‹FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F›
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c y _ hy =>
        have hrange : IntermediateField.adjoin K ({x} : Set F) ≤ lift.fieldRange := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y' rfl
          exact ⟨algebraMap (Polynomial K) (RatFunc K) Polynomial.X, (hlift _).trans (Polynomial.aeval_X _)⟩
        obtain ⟨c', hc'⟩ := hrange c.2
        have hcc : c • y = c' • y := by
          change (c : F) * y = lift.toRingHom c' * y
          rw [← hc']
        rw [hcc]
        exact Submodule.smul_mem _ c' hy
  have h1 := AlgebraicCurve.RationalFunctionField.deg_ne_zero (v.restrict (RatFunc K))
  have h2 := AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional (F := RatFunc K) v
  rw [← AlgebraicCurve.Place.deg_restrict_mul_inertiaDeg (F := RatFunc K)]
  exact mul_ne_zero h1 h2.ne'

end S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin (solution)
