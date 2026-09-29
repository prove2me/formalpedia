-- Prove2me | solution 1 for AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5cc813c5-c8c5-5d27-93aa-4e3921b98922

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u v

open AlgebraicCurve IntermediateField

namespace QForm1

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem ord_map_eq (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) (v : Place K F) (f : F) :
    v.ord (σ f) = v.ord f := by
  have := Place.ord_smul σ v f
  rwa [h v] at this

variable [IsAlgClosed K]

theorem exists_map_eq_algebraMap_mul (j : F) (hj : Transcendental K j) [FiniteDimensional K⟮j⟯ F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) {f : F} (hf : f ≠ 0) :
    ∃ c : K, σ f = algebraMap K F c * f := by
  have hσf : σ f ≠ 0 := fun h0 => hf (σ.injective (by rw [h0, map_zero]))
  have hu : ∀ v : Place K F, v.ord (σ f * f⁻¹) = 0 := fun v => by
    rw [Place.ord_mul v hσf (inv_ne_zero hf), Place.ord_inv, ord_map_eq σ h v f, add_neg_cancel]
  obtain ⟨c, hc⟩ :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (K := K) j hj hu
  exact ⟨c, by rw [hc, inv_mul_cancel_right₀ hf]⟩

theorem algEquiv_eq_one_of_forall_smul_place_eq (j : F) (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) : σ = 1 := by
  apply AlgEquiv.ext
  intro f
  rw [AlgEquiv.one_apply]
  by_cases hfK : f ∈ (algebraMap K F).range
  · obtain ⟨a, rfl⟩ := hfK
    exact σ.commutes a
  · have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfK ⟨0, map_zero _⟩
    have hf1 : f + 1 ≠ 0 := by
      intro h1
      apply hfK
      refine ⟨-1, ?_⟩
      rw [map_neg, map_one]
      exact (eq_neg_of_add_eq_zero_left h1).symm
    obtain ⟨c, hc⟩ := exists_map_eq_algebraMap_mul j hj σ h hf0
    obtain ⟨d, hd⟩ := exists_map_eq_algebraMap_mul j hj σ h hf1

    have key : (algebraMap K F d - algebraMap K F c) * f = 1 - algebraMap K F d := by
      have e := hd
      rw [map_add, map_one, hc] at e
      linear_combination (-1 : F) * e
    by_cases hdc : d = c
    · subst hdc
      have h1 : algebraMap K F d = 1 := by
        have e0 : (1 : F) - algebraMap K F d = 0 := by rw [← key, sub_self, zero_mul]
        exact (sub_eq_zero.1 e0).symm
      rw [hc, h1, one_mul]
    · exfalso
      apply hfK
      have hne : algebraMap K F d - algebraMap K F c ≠ 0 := by
        rw [sub_ne_zero]
        exact fun he => hdc ((algebraMap K F).injective he)
      refine ⟨(1 - d) / (d - c), ?_⟩
      rw [map_div₀, map_sub, map_sub, map_one, div_eq_iff hne, mul_comm]
      exact key.symm

theorem algebra_transcendental_of_nontrivial_kaehler [Nontrivial (Ω[F⁄K])] :
    Algebra.Transcendental K F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  haveI : Subsingleton (Ω[F⁄K]) := inferInstance
  exact false_of_nontrivial_of_subsingleton (Ω[F⁄K])

end QForm1

open QForm1 in
theorem solution
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) : σ = 1 := by
  haveI : Algebra.Transcendental K F := algebra_transcendental_of_nontrivial_kaehler
  obtain ⟨t, ht, hfin, -⟩ :=
    exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (K := K) (F := F)
      IsCurveOver.finrank_kaehler
  haveI := hfin
  exact algEquiv_eq_one_of_forall_smul_place_eq t ht σ h

end S_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq
end P2MW
export P2MW.S_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq (solution)
