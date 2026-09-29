-- Prove2me | solution 1 for AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/042e1ebc-e00d-5f6a-8689-f39bb454c4d4

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.CanonicalLocalResidueDataK"
p2m_open "AlgebraicCurve"

namespace T1ResInv

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem differentialCoeff_add'' [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem res_uniformizer_inv (R : v.CanonicalLocalResidueDataK) : R.res v.uniformizer⁻¹ = 1 := by
  have hmem : v.uniformizer * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
    rw [mul_inv_cancel₀ v.uniformizer_ne_zero]; exact one_mem _
  rw [R.res_simplePole _ hmem]
  have h1 : (⟨v.uniformizer * v.uniformizer⁻¹, hmem⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

end T1ResInv

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one.AlgebraicCurve AlgebraicCurve.T1ResInv in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {t : F} (ht : v.ord t = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F t) * t⁻¹) = 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at ht
    exact zero_ne_one ht
  have hπv0 : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  set w : F := t * (v.uniformizer)⁻¹ with hw_def
  have hw0 : w ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hπv0)
  have hword : v.ord w = 0 := by
    rw [hw_def, v.ord_mul ht0 (inv_ne_zero hπv0), v.ord_inv, ht, v.ord_uniformizer]
    ring
  have hwmem : w ∈ v.toValuationSubring := mem_of_ord_nonneg v hw0 hword.ge
  have hwinvmem : w⁻¹ ∈ v.toValuationSubring := by
    refine mem_of_ord_nonneg v (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword]
    omega
  have ht_eq : t = v.uniformizer * w := by
    rw [hw_def, mul_comm t (v.uniformizer)⁻¹, ← mul_assoc, mul_inv_cancel₀ hπv0, one_mul]
  have hD : KaehlerDifferential.D K F t
      = v.uniformizer • KaehlerDifferential.D K F w
        + w • KaehlerDifferential.D K F v.uniformizer := by
    conv_lhs => rw [ht_eq]
    exact Derivation.leibniz _ _ _
  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K F t)
      = v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) + w := by
    rw [hD, differentialCoeff_add'' v, v.differentialCoeff_smul, v.differentialCoeff_smul,
      show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
      v.differentialCoeff_dCoord, mul_one]
  have hsplit : v.differentialCoeff (KaehlerDifferential.D K F t) * t⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹ + (v.uniformizer)⁻¹ := by
    rw [hcoeff, ht_eq, mul_inv]
    field_simp
  rw [hsplit, map_add, res_uniformizer_inv v R,
    R.res_of_mem _ (mul_mem (hint w hwmem) hwinvmem), zero_add]

end S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one (solution)
