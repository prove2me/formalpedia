-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/31e14e7f-5dbc-5cfa-a609-3f57d0edaee9

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hW : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W a = a)
    (hW' : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W' a = a)
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) :
    W = W' := by

  have hUv : ∀ v : Place (AlgebraicClosure ℚ) F₀, (W'⁻¹ * W) • v = v := fun v => by
    rw [mul_smul, h v, inv_smul_smul]

  have hWe : SemilinearAut.baseAut W = 1 := RingEquiv.ext hW
  have hW'e : SemilinearAut.baseAut W' = 1 := RingEquiv.ext hW'
  have hUbase : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut (W'⁻¹ * W) a = a := fun a => by
    rw [SemilinearAut.baseAut_mul, SemilinearAut.baseAut_inv, hWe, hW'e]
    rfl

  let σ : F₀ ≃ₐ[AlgebraicClosure ℚ] F₀ :=
    AlgEquiv.ofRingEquiv (f := SemilinearAut.toRingAut (W'⁻¹ * W)) (fun a => by
      rw [SemilinearAut.commutes, hUbase])
  have hσU : SemilinearAut.ofAlgAut σ = W'⁻¹ * W := by
    apply Subtype.ext
    apply Prod.ext
    · exact RingEquiv.ext (fun x => rfl)
    · exact RingEquiv.ext (fun a => (hUbase a).symm)

  have hσv : ∀ v : Place (AlgebraicClosure ℚ) F₀, σ • v = v := fun v => by
    have hv := hUv v
    rw [← hσU] at hv
    ext x
    have hx := congrArg (fun P : Place (AlgebraicClosure ℚ) F₀ => x ∈ P.toValuationSubring) hv
    simp only [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢

    have hinv : σ⁻¹ • x = (SemilinearAut.ofAlgAut σ)⁻¹ • x := by
      rw [← map_inv, SemilinearAut.ofAlgAut_smul, AlgEquiv.smul_def]
    rw [hinv]
    exact Eq.to_iff hx

  have hσ1 : σ = 1 := AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq σ hσv
  have hU1 : W'⁻¹ * W = 1 := by rw [← hσU, hσ1, map_one]
  exact (inv_mul_eq_one.mp hU1).symm

end S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq (solution)
