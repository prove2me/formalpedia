-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6f1031c3-d7f6-54bc-88c5-79e9caf932e1

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius.AlgebraicCurve"

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel Place FiniteAlong SemilinearAut SemilinearAut.smul_toValuationSubring CurveModel.exists_finite_flat_hom_of_algHom"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "placeOfPoint C ffEquiv smooth exists_finite_flat_hom_of_algHom"
namespace PlaceTransportFrob
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

theorem mem_of_pow_mem {L : Type v} [Field L] (O : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n ∈ O) : x ∈ O := by
  rcases O.mem_or_inv_mem x with h | h
  · exact h
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact O.zero_mem
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have : x = x ^ (m + 1) * (x⁻¹) ^ m := by
        rw [pow_succ, mul_assoc, mul_comm x, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow, one_mul]
      rw [this]
      exact O.toSubring.mul_mem hx (O.toSubring.pow_mem h m)

theorem restrictAlong_frobenius_eq_smul {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
    {L : Type v} [Field L] [Algebra K L] (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p) (hΦi : Φ.toRingHom.IsIntegral)
    (v : Place K L) : v.restrictAlong Φ hΦi = g • v := by
  ext f
  change Φ f ∈ v.toValuationSubring ↔ f ∈ (g • v).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hΦ]
  exact ⟨fun h => mem_of_pow_mem _ (Fact.out : p.Prime).ne_zero h, fun h => v.toValuationSubring.toSubring.pow_mem h p⟩

end AlgebraicCurve.CurveModel.PlaceTransportFrob

theorem solution
    {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p) (hfin : FiniteAlong K Φ)
    (θ : M.C ⟶ M.C)
    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (Φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (y : closedPoints M.C) :
    ∃ h : θ.base y.1 ∈ closedPoints M.C, M.placeOfPoint ⟨θ.base y.1, h⟩ = g • M.placeOfPoint y := by

  have hΦi : Φ.toRingHom.IsIntegral := fun f => by
    refine ⟨Polynomial.X ^ p - Polynomial.C (g • f), Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hΦ, inv_smul_smul, sub_self]

  obtain ⟨π, -, -, -, -, -, hπgen, hπclosed, hπuniq⟩ :=
    AlgebraicCurve.CurveModel.exists_finite_flat_hom_of_algHom M M Φ hΦi hfin
  have hθπ : θ = π := hπuniq θ (by rw [hθgen, hπgen])
  subst hθπ
  obtain ⟨h, hplace⟩ := hπclosed y
  exact ⟨h, hplace.trans (AlgebraicCurve.CurveModel.PlaceTransportFrob.restrictAlong_frobenius_eq_smul p g Φ hΦ hΦi _)⟩

end S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_placeOfPoint_eq_smul_of_fromSpecStalk_comp_eq_frobenius (solution)
