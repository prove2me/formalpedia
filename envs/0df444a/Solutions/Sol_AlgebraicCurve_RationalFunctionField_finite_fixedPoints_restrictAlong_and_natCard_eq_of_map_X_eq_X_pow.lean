-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2c67e6e3-ec86-55d3-9a56-b33ded961820

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.restrictAlong Place Place.ofHeightOneSpectrum_toValuationSubring"
p2m_open "AlgebraicCurve"

namespace RatFuncFrobFix

p2m_open "AlgebraicCurve.RationalFunctionField"

variable {K : Type*} [Field K]

theorem mem_placeOfPoint_iff (a : K) (f : RatFunc K) :
    f ∈ (placeOfPoint K a).toValuationSubring ↔
      (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)).valuation (RatFunc K) f ≤ 1 := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum, Place.ofHeightOneSpectrum_toValuationSubring,
    Valuation.mem_valuationSubring_iff]

theorem algebraMap_mem_placeOfPoint (a : K) (P : K[X]) :
    algebraMap K[X] (RatFunc K) P ∈ (placeOfPoint K a).toValuationSubring := by
  rw [mem_placeOfPoint_iff]
  exact HeightOneSpectrum.valuation_le_one _ _

theorem X_mem_placeOfPoint (a : K) : (RatFunc.X : RatFunc K) ∈ (placeOfPoint K a).toValuationSubring := by
  rw [← RatFunc.algebraMap_X]
  exact algebraMap_mem_placeOfPoint a _

theorem inv_algebraMap_mem_placeOfPoint_iff (a : K) {P : K[X]} (hP : P ≠ 0) :
    (algebraMap K[X] (RatFunc K) P)⁻¹ ∈ (placeOfPoint K a).toValuationSubring ↔ ¬ P.IsRoot a := by
  rw [mem_placeOfPoint_iff, map_inv₀]
  have hP' : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hP
  have hpos : 0 < (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)).valuation (RatFunc K)
      (algebraMap K[X] (RatFunc K) P) := by
    rw [Valuation.pos_iff]
    exact hP'
  rw [inv_le_one₀ hpos, ← not_lt, HeightOneSpectrum.valuation_lt_one_iff_mem,
    heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]

theorem inv_X_pow_sub_C_mem_placeOfPoint_iff (a c : K) {n : ℕ} (hn : 0 < n) :
    ((RatFunc.X : RatFunc K) ^ n - RatFunc.C c)⁻¹ ∈ (placeOfPoint K a).toValuationSubring ↔
      c ≠ a ^ n := by
  have hP : (X ^ n - C c : K[X]) ≠ 0 := by
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [natDegree_X_pow_sub_C]
    exact hn
  have : (RatFunc.X : RatFunc K) ^ n - RatFunc.C c = algebraMap K[X] (RatFunc K) (X ^ n - C c) := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [this, inv_algebraMap_mem_placeOfPoint_iff a hP]
  simp [sub_eq_zero, eq_comm]

theorem X_pow_not_mem_placeInfty [DecidableEq (RatFunc K)] {n : ℕ} (hn : 0 < n) :
    (RatFunc.X : RatFunc K) ^ n ∉ (placeInfty K).toValuationSubring := by
  rw [placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff, map_pow,
    RatFunc.inftyValuation.X, not_le, ← WithZero.exp_nsmul, nsmul_one]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  exact_mod_cast hn

theorem X_not_mem_placeInfty [DecidableEq (RatFunc K)] :
    (RatFunc.X : RatFunc K) ∉ (placeInfty K).toValuationSubring := by
  simpa using X_pow_not_mem_placeInfty (K := K) (n := 1) one_pos

section Frob

variable (q : ℕ) (φ : RatFunc K →ₐ[K] RatFunc K) (hφi : φ.toRingHom.IsIntegral)
  (hφ : φ RatFunc.X = RatFunc.X ^ q)

include hφ in
theorem map_inv_X_sub_C (c : K) :
    φ ((RatFunc.X : RatFunc K) - RatFunc.C c)⁻¹ = ((RatFunc.X : RatFunc K) ^ q - RatFunc.C c)⁻¹ := by
  rw [map_inv₀, map_sub, hφ, ← RatFunc.algebraMap_eq_C, AlgHom.commutes]

theorem mem_restrictAlong_iff (w : Place K (RatFunc K)) (f : RatFunc K) :
    f ∈ (w.restrictAlong φ hφi).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

variable [IsAlgClosed K]

include hφ

theorem restrictAlong_placeOfPoint (hq : 0 < q) (a : K) :
    (placeOfPoint K a).restrictAlong φ hφi = placeOfPoint K (a ^ q) := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K ((placeOfPoint K a).restrictAlong φ hφi) with
    ⟨b, hb⟩ | hinf
  · rw [hb]
    congr 1
    by_contra hne
    have h1 : ((RatFunc.X : RatFunc K) - RatFunc.C b)⁻¹ ∉ (placeOfPoint K b).toValuationSubring := by
      have := inv_X_pow_sub_C_mem_placeOfPoint_iff (K := K) b b (n := 1) one_pos
      rw [pow_one] at this
      rw [this]
      exact fun h => h (pow_one b).symm
    apply h1
    rw [← hb, mem_restrictAlong_iff φ hφi, map_inv_X_sub_C q φ hφ,
      inv_X_pow_sub_C_mem_placeOfPoint_iff a b hq]
    exact hne
  · exfalso
    have hX : (RatFunc.X : RatFunc K) ∈ ((placeOfPoint K a).restrictAlong φ hφi).toValuationSubring := by
      rw [mem_restrictAlong_iff φ hφi, hφ]
      have : (RatFunc.X : RatFunc K) ^ q = algebraMap K[X] (RatFunc K) (X ^ q) := by
        rw [map_pow, RatFunc.algebraMap_X]
      rw [this]
      exact algebraMap_mem_placeOfPoint a _
    rw [hinf] at hX
    exact X_not_mem_placeInfty hX

theorem restrictAlong_placeInfty [DecidableEq (RatFunc K)] (hq : 0 < q) :
    (placeInfty K).restrictAlong φ hφi = placeInfty K := by
  rcases eq_placeOfPoint_or_eq_placeInfty K ((placeInfty K).restrictAlong φ hφi) with ⟨b, hb⟩ | hinf
  · exfalso
    have hX : (RatFunc.X : RatFunc K) ∈ ((placeInfty K).restrictAlong φ hφi).toValuationSubring := by
      rw [hb]
      exact X_mem_placeOfPoint b
    rw [mem_restrictAlong_iff φ hφi, hφ] at hX
    exact X_pow_not_mem_placeInfty hq hX
  · exact hinf

theorem fixedPoints_eq [DecidableEq (RatFunc K)] (hq : 0 < q) :
    Function.fixedPoints (Place.restrictAlong φ hφi) =
      placeOfPoint K '' {a : K | a ^ q = a} ∪ {placeInfty K} := by
  ext w
  rw [Function.mem_fixedPoints_iff, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · intro hw
    rcases eq_placeOfPoint_or_eq_placeInfty K w with ⟨a, rfl⟩ | rfl
    · left
      refine ⟨a, ?_, rfl⟩
      rw [restrictAlong_placeOfPoint q φ hφi hφ hq] at hw
      exact placeOfPoint_injective K hw
    · right
      rfl
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · rw [restrictAlong_placeOfPoint q φ hφi hφ hq, Set.mem_setOf_eq.mp ha]
    · exact restrictAlong_placeInfty q φ hφi hφ hq

end Frob

theorem setOf_pow_eq_eq_rootSet [IsAlgClosed K] {q : ℕ} (hq : 1 < q) :
    {a : K | a ^ q = a} = ((X ^ q - X : K[X]).rootSet K : Set K) := by
  ext a
  have hne : (X ^ q - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  rw [Set.mem_setOf_eq, mem_rootSet_of_ne hne]
  simp [sub_eq_zero]

theorem ncard_setOf_pow_eq [IsAlgClosed K] {q : ℕ} (hq : 1 < q) (hqK : (q : K) = 0) :
    {a : K | a ^ q = a}.ncard = q := by
  classical
  have hsep : (X ^ q - X : K[X]).Separable := by
    obtain ⟨p, hp⟩ := CharP.exists K
    have hdvd : p ∣ q := (CharP.cast_eq_zero_iff K p q).mp hqK
    exact galois_poly_separable p q hdvd
  rw [setOf_pow_eq_eq_rootSet hq, rootSet_def, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (nodup_roots hsep.map)]
  have hid : (X ^ q - X : K[X]).map (algebraMap K K) = X ^ q - X := by
    rw [Algebra.algebraMap_self, Polynomial.map_id]
  rw [hid, ← (IsAlgClosed.splits (X ^ q - X : K[X])).natDegree_eq_card_roots]
  exact FiniteField.X_pow_card_sub_X_natDegree_eq K hq

theorem finite_setOf_pow_eq [IsAlgClosed K] {q : ℕ} (hq : 1 < q) : {a : K | a ^ q = a}.Finite := by
  rw [setOf_pow_eq_eq_rootSet hq]
  exact (rootSet_finite _ _)

end RatFuncFrobFix

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow.AlgebraicCurve AlgebraicCurve.RationalFunctionField AlgebraicCurve.RatFuncFrobFix in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (q : ℕ) (hq : 1 < q) (hqK : (q : K) = 0)
    (φ : RatFunc K →ₐ[K] RatFunc K) (hφi : φ.toRingHom.IsIntegral)
    (hφ : φ RatFunc.X = RatFunc.X ^ q) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)) = q + 1 := by
  classical
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hfix := fixedPoints_eq q φ hφi hφ hq0
  have hfinR : {a : K | a ^ q = a}.Finite := finite_setOf_pow_eq hq
  have hfin : (Function.fixedPoints (Place.restrictAlong φ hφi)).Finite := by
    rw [hfix]
    exact (hfinR.image _).union (Set.finite_singleton _)
  refine ⟨hfin, ?_⟩
  rw [Nat.card_coe_set_eq, hfix, Set.ncard_union_eq ?_ (hfinR.image _) (Set.finite_singleton _),
    Set.ncard_image_of_injective _ (placeOfPoint_injective K), Set.ncard_singleton,
    ncard_setOf_pow_eq hq hqK]
  rw [Set.disjoint_singleton_right]
  rintro ⟨a, -, ha⟩
  exact placeOfPoint_ne_placeInfty K a ha

end
end S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_finite_fixedPoints_restrictAlong_and_natCard_eq_of_map_X_eq_X_pow (solution)
