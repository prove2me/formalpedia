-- Prove2me | solution 1 for AlgebraicCurve.ConstantReduction.pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/446ecf71-8273-5767-bc31-00da022daed7

import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (𝓡 : ConstantReduction A F Fbar)
    (T : Divisor L F →+ Divisor L F)
    (hT0 : ∀ D : Divisor L F, D ∈ Divisor.degZero (K := L) (F := F) → T D ∈ Divisor.degZero (K := L) (F := F))
    (TJ : Pic0 L F → Pic0 L F)
    (hTJ : ∀ D : Divisor.degZero (K := L) (F := F), TJ (Pic0.mk D) = Pic0.mk ⟨T (D : Divisor L F), hT0 D D.2⟩)
    (g : SemilinearAut (IsLocalRing.ResidueField ↥A) Fbar) (ℓ : ℕ)
    (hplace : ∀ P : Place L F, Finsupp.mapDomain 𝓡.placeMap (T (Finsupp.single P 1)) =
      Finsupp.single (g • 𝓡.placeMap P) 1 + ℓ • Finsupp.single (g⁻¹ • 𝓡.placeMap P) 1) :
    ∀ c : Pic0 L F, 𝓡.pic0Map (TJ c) = g • 𝓡.pic0Map c + ℓ • (g⁻¹ • 𝓡.pic0Map c) := by
  classical

  have key : 𝓡.divMap.comp T =
      (DistribSMul.toAddMonoidHom (Divisor (IsLocalRing.ResidueField ↥A) Fbar) g).comp 𝓡.divMap +
        ℓ • ((DistribSMul.toAddMonoidHom (Divisor (IsLocalRing.ResidueField ↥A) Fbar) g⁻¹).comp 𝓡.divMap) := by
    apply Finsupp.addHom_ext
    intro P n
    have hs : Finsupp.single P n = n • Finsupp.single P (1 : ℤ) := by rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul, map_zsmul]
    congr 1
    show 𝓡.divMap (T (Finsupp.single P 1)) =
      g • 𝓡.divMap (Finsupp.single P 1) + ℓ • (g⁻¹ • 𝓡.divMap (Finsupp.single P 1))
    rw [𝓡.divMap_apply, 𝓡.divMap_apply, Finsupp.mapDomain_single, hplace P, SemilinearAut.smul_single,
      SemilinearAut.smul_single]
  have hdiv : ∀ D : Divisor L F, Finsupp.mapDomain 𝓡.placeMap (T D) =
      g • Finsupp.mapDomain 𝓡.placeMap D + ℓ • (g⁻¹ • Finsupp.mapDomain 𝓡.placeMap D) := by
    intro D
    have := congrArg (fun f : Divisor L F →+ Divisor (IsLocalRing.ResidueField ↥A) Fbar => f D) key
    exact this

  intro c
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [hTJ, 𝓡.pic0Map_mk, 𝓡.pic0Map_mk, SemilinearAut.pic0_smul_mk, SemilinearAut.pic0_smul_mk]
  have hD : (𝓡.degZeroMap ⟨T (D : Divisor L F), hT0 D D.2⟩ : Divisor.degZero (K := IsLocalRing.ResidueField ↥A) (F := Fbar)) =
      SemilinearAut.degZeroSMulHom g (𝓡.degZeroMap D) + ℓ • SemilinearAut.degZeroSMulHom g⁻¹ (𝓡.degZeroMap D) := by
    apply Subtype.ext
    simp only [𝓡.coe_degZeroMap, SemilinearAut.coe_degZeroSMulHom, AddSubgroup.coe_add, AddSubgroup.coe_nsmul]
    exact hdiv D
  rw [hD]
  show QuotientAddGroup.mk' _ _ = QuotientAddGroup.mk' _ _ + ℓ • QuotientAddGroup.mk' _ _
  rw [map_add, map_nsmul]

end S_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single
end P2MW
export P2MW.S_AlgebraicCurve_ConstantReduction_pic0Map_apply_eq_smul_add_smul_of_forall_mapDomain_placeMap_single (solution)
