-- Prove2me | solution 1 for AlgebraicCurve.card_effectiveDivisors_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e66d4152-3206-56ea-b5ec-5511d5513ce1

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_deg_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum.AlgebraicCurve Finset"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.finiteResidue Place Divisor Divisor.degree Divisor.degree_single Place.finite_setOf_deg_eq"
namespace CardEffectiveDivisorsSol
p2m_open "AlgebraicCurve"

theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) {S : Finset (Place K F)} (hS : D.support ⊆ S) :
    Divisor.degree D = ∑ v ∈ S, D v * (v.deg : ℤ) := by
  have h : Divisor.degree D = D.sum (fun w c => c * (w.deg : ℤ)) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [h]
  exact Finsupp.sum_of_support_subset D hS (fun w c => c * (w.deg : ℤ)) (fun v _ => zero_mul _)

theorem apply_mul_deg_le_degree {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) (hD : ∀ v, 0 ≤ D v) (v : Place K F) :
    D v * (v.deg : ℤ) ≤ Divisor.degree D := by
  classical
  rw [degree_eq_sum D (Finset.subset_insert v D.support)]
  exact Finset.single_le_sum (s := insert v D.support) (f := fun w => D w * (w.deg : ℤ))
    (fun w _ => mul_nonneg (hD w) (by positivity)) (Finset.mem_insert_self v _)

theorem deg_le_of_mem_support {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) (hD : ∀ v, 0 ≤ D v) {m : ℕ} (hdeg : Divisor.degree D = (m : ℤ))
    {v : Place K F} (hv : v ∈ D.support) : v.deg ≤ m := by
  have h1 : 1 ≤ D v := by
    have := Finsupp.mem_support_iff.mp hv
    have := hD v
    omega
  have h2 := apply_mul_deg_le_degree D hD v
  rw [hdeg] at h2
  have h3 : (v.deg : ℤ) ≤ D v * (v.deg : ℤ) := le_mul_of_one_le_left (by positivity) h1
  exact_mod_cast h3.trans h2

theorem card_eff_sub_eq_card_filter {K F : Type*} [Field K] [Field F] [Algebra K F]
    (n m : ℕ) (v : Place K F) (hm : m * v.deg ≤ n) (En Em : Finset (Divisor K F))
    (hEn : ∀ D, D ∈ En ↔ 0 ≤ D ∧ Divisor.degree D = (n : ℤ))
    (hEm : ∀ D, D ∈ Em ↔ 0 ≤ D ∧ Divisor.degree D = ((n - m * v.deg : ℕ) : ℤ)) :
    Em.card = (En.filter fun D => (m : ℤ) ≤ D v).card := by
  classical
  have hcast : ((n - m * v.deg : ℕ) : ℤ) = (n : ℤ) - (m : ℤ) * (v.deg : ℤ) := by
    rw [Nat.cast_sub hm, Nat.cast_mul]
  have hsingle : ∀ w, 0 ≤ (Finsupp.single v (m : ℤ)) w := fun w => by
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  refine Finset.card_nbij' (fun D => D + Finsupp.single v (m : ℤ))
    (fun D => D - Finsupp.single v (m : ℤ)) ?_ ?_ ?_ ?_
  · intro D hD
    rw [Finset.mem_coe, hEm] at hD
    obtain ⟨hD0, hDdeg⟩ := hD
    rw [Finsupp.le_def] at hD0
    rw [Finset.mem_coe, Finset.mem_filter, hEn, Finsupp.le_def]
    refine ⟨⟨fun w => ?_, ?_⟩, ?_⟩
    · have h1 := hD0 w
      have h2 := hsingle w
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply] at h1 ⊢
      linarith
    · rw [map_add, hDdeg, Divisor.degree_single, hcast]
      ring
    · have h1 := hD0 v
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same] at h1 ⊢
      linarith
  · intro D hD
    rw [Finset.mem_coe, Finset.mem_filter, hEn, Finsupp.le_def] at hD
    obtain ⟨⟨hD0, hDdeg⟩, hmv⟩ := hD
    rw [Finset.mem_coe, hEm, Finsupp.le_def]
    refine ⟨fun w => ?_, ?_⟩
    · have h1 := hD0 w
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 ⊢
      rw [Finsupp.single_apply]
      split_ifs with hw
      · subst hw
        linarith
      · linarith
    · rw [map_sub, hDdeg, Divisor.degree_single, hcast]
  · intro D _
    simp
  · intro D _
    simp

section Finite

variable {K F : Type*} [Field K] [Finite K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

omit [Finite K] [Algebra.EssFiniteType K F] in
theorem one_le_deg (v : Place K F) : 1 ≤ v.deg := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  have : 0 < v.deg := Module.finrank_pos (R := K) (M := v.ResidueField)
  exact this

theorem finite_setOf_deg_le (n : ℕ) : {v : Place K F | v.deg ≤ n}.Finite := by
  refine (Set.Finite.biUnion (Finset.range (n + 1)).finite_toSet
    (fun d _ => AlgebraicCurve.Place.finite_setOf_deg_eq K F d)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
  exact ⟨v.deg, by omega, rfl⟩

theorem finite_eff (m : ℕ) :
    {D : Divisor K F | 0 ≤ D ∧ Divisor.degree D = (m : ℤ)}.Finite := by
  classical
  set T : Finset (Place K F) := (finite_setOf_deg_le (K := K) (F := F) m).toFinset with hTdef
  have hmemT : ∀ v, v ∈ T ↔ v.deg ≤ m := fun v => by simp [hTdef]
  let S : Set (Divisor K F) := {D | 0 ≤ D ∧ Divisor.degree D = (m : ℤ)}
  have hS : ∀ D ∈ S, (∀ w, 0 ≤ D w ∧ D w ≤ m) ∧ D.support ⊆ T := by
    intro D hD
    obtain ⟨hD0, hDdeg⟩ := hD
    have hnn : ∀ w, 0 ≤ D w := fun w => by simpa using (Finsupp.le_def.mp hD0) w
    refine ⟨fun w => ⟨hnn w, ?_⟩, fun w hw => (hmemT w).2 (deg_le_of_mem_support D hnn hDdeg hw)⟩
    have h1 := apply_mul_deg_le_degree D hnn w
    rw [hDdeg] at h1
    have h2 : D w ≤ D w * (w.deg : ℤ) :=
      le_mul_of_one_le_right (hnn w) (by exact_mod_cast one_le_deg w)
    exact h2.trans h1
  let ι : S → (T → Set.Icc (0 : ℤ) m) := fun D w => ⟨D.1 w, (hS D.1 D.2).1 w⟩
  have hι : Function.Injective ι := by
    rintro ⟨D, hD⟩ ⟨D', hD'⟩ h
    ext w
    by_cases hw : w ∈ T
    · have := congrArg (fun g => ((g ⟨w, hw⟩ : Set.Icc (0 : ℤ) m) : ℤ)) h
      simpa [ι] using this
    · have h1 : D w = 0 := by
        by_contra hne
        exact hw ((hS D hD).2 (Finsupp.mem_support_iff.mpr hne))
      have h2 : D' w = 0 := by
        by_contra hne
        exact hw ((hS D' hD').2 (Finsupp.mem_support_iff.mpr hne))
      simp [h1, h2]
  haveI : Finite (Set.Icc (0 : ℤ) m) := Set.finite_Icc _ _
  exact Set.finite_coe_iff.mp (Finite.of_injective ι hι)

theorem main (n : ℕ) :
    n * Nat.card {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = (n : ℤ)} =
      ∑ r ∈ Finset.Icc 1 n,
        (∑ d ∈ Nat.divisors r, d * Nat.card {v : Place K F | v.deg = d}) *
          Nat.card {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = ((n - r : ℕ) : ℤ)} := by
  classical

  set A : ℕ → ℕ := fun m =>
    Nat.card {D : Divisor K F // 0 ≤ D ∧ Divisor.degree D = (m : ℤ)} with hAdef
  set B : ℕ → ℕ := fun d => Nat.card {v : Place K F | v.deg = d} with hBdef
  show n * A n = ∑ r ∈ Icc 1 n, (∑ d ∈ Nat.divisors r, d * B d) * A (n - r)

  have hfinE : ∀ m : ℕ, {D : Divisor K F | 0 ≤ D ∧ Divisor.degree D = (m : ℤ)}.Finite :=
    fun m => finite_eff m
  set Ef : ℕ → Finset (Divisor K F) := fun m => (hfinE m).toFinset with hEfdef
  have hmemEf : ∀ m D, D ∈ Ef m ↔ 0 ≤ D ∧ Divisor.degree D = (m : ℤ) := fun m D => by
    simp [hEfdef]
  have hA : ∀ m, A m = (Ef m).card := fun m => by
    simp only [hAdef, hEfdef]
    exact Nat.card_eq_card_finite_toFinset (hfinE m)

  have hfinT := finite_setOf_deg_le (K := K) (F := F) n
  set T : Finset (Place K F) := hfinT.toFinset with hTdef
  have hmemT : ∀ v, v ∈ T ↔ v.deg ≤ n := fun v => by simp [hTdef]
  have hB : ∀ d, d ≤ n → B d = (T.filter fun v => v.deg = d).card := by
    intro d hd
    have hfin := AlgebraicCurve.Place.finite_setOf_deg_eq K F d
    have h1 : B d = Nat.card ↥{v : Place K F | v.deg = d} := rfl
    rw [h1, Nat.card_eq_card_finite_toFinset hfin]
    congr 1
    ext v
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, hmemT]
    constructor
    · intro h
      exact ⟨h ▸ hd, h⟩
    · exact And.right
  have hdegpos : ∀ v : Place K F, 1 ≤ v.deg := one_le_deg

  have hEn_nonneg : ∀ D ∈ Ef n, ∀ w, 0 ≤ D w := fun D hD w => by
    simpa using (Finsupp.le_def.mp ((hmemEf n D).1 hD).1) w
  have hEn_supp : ∀ D ∈ Ef n, D.support ⊆ T := fun D hD w hw =>
    (hmemT w).2 (deg_le_of_mem_support D (hEn_nonneg D hD) ((hmemEf n D).1 hD).2 hw)
  have hEn_sum : ∀ D ∈ Ef n, ∑ v ∈ T, (D v).toNat * v.deg = n := by
    intro D hD
    have h := degree_eq_sum D (hEn_supp D hD)
    rw [((hmemEf n D).1 hD).2] at h
    have hnn := hEn_nonneg D hD
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Int.toNat_of_nonneg (hnn v)]
  have hEn_coef : ∀ D ∈ Ef n, ∀ v, (D v).toNat * v.deg ≤ n := by
    intro D hD v
    have hnn := hEn_nonneg D hD
    have h := apply_mul_deg_le_degree D hnn v
    rw [((hmemEf n D).1 hD).2] at h
    have : ((D v).toNat : ℤ) * v.deg ≤ n := by rwa [Int.toNat_of_nonneg (hnn v)]
    exact_mod_cast this

  have hLHS : n * A n = ∑ D ∈ Ef n, ∑ v ∈ T, (D v).toNat * v.deg := by
    rw [hA, Finset.sum_congr rfl (fun D hD => hEn_sum D hD), Finset.sum_const, smul_eq_mul,
      mul_comm]

  have hR1 : ∀ r ∈ Icc 1 n,
      ∑ d ∈ Nat.divisors r, d * B d = ∑ v ∈ T.filter (fun v => v.deg ∣ r), v.deg := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr0 : r ≠ 0 := by omega
    have hmaps : ∀ v ∈ T.filter (fun v => v.deg ∣ r), v.deg ∈ Nat.divisors r := fun v hv =>
      Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hv).2, hr0⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun v => v.deg)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    have hdn : d ≤ n := (Nat.le_of_dvd (by omega) hdr).trans hr.2
    have hset : (T.filter (fun v => v.deg ∣ r)).filter (fun v => v.deg = d)
        = T.filter (fun v => v.deg = d) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, h3 ▸ hdr⟩, h3⟩
    rw [hB d hdn, hset, Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2),
      Finset.sum_const, smul_eq_mul, mul_comm]

  have hR2 : ∑ r ∈ Icc 1 n, (∑ d ∈ Nat.divisors r, d * B d) * A (n - r)
      = ∑ v ∈ T, ∑ r ∈ (Icc 1 n).filter (fun r => v.deg ∣ r), v.deg * A (n - r) := by
    calc ∑ r ∈ Icc 1 n, (∑ d ∈ Nat.divisors r, d * B d) * A (n - r)
        = ∑ r ∈ Icc 1 n, ∑ v ∈ T, (if v.deg ∣ r then v.deg * A (n - r) else 0) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [hR1 r hr, Finset.sum_mul, Finset.sum_filter]
      _ = ∑ v ∈ T, ∑ r ∈ Icc 1 n, (if v.deg ∣ r then v.deg * A (n - r) else 0) :=
          Finset.sum_comm
      _ = ∑ v ∈ T, ∑ r ∈ (Icc 1 n).filter (fun r => v.deg ∣ r), v.deg * A (n - r) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_filter]

  have hR3 : ∀ v ∈ T, ∑ r ∈ (Icc 1 n).filter (fun r => v.deg ∣ r), v.deg * A (n - r)
      = ∑ D ∈ Ef n, (D v).toNat * v.deg := by
    intro v _
    have he1 : 1 ≤ v.deg := hdegpos v
    have he0 : 0 < v.deg := he1

    have himg : (Icc 1 n).filter (fun r => v.deg ∣ r)
        = (Icc 1 (n / v.deg)).image (fun m => m * v.deg) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hr1, hrn⟩, ⟨c, rfl⟩⟩
        refine ⟨c, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos c with h | h
          · subst h
            simp at hr1
          · exact h
        · rw [Nat.le_div_iff_mul_le he0, mul_comm]
          exact hrn
      · rintro ⟨m, ⟨hm1, hmn⟩, rfl⟩
        rw [Nat.le_div_iff_mul_le he0] at hmn
        exact ⟨⟨le_trans hm1 (Nat.le_mul_of_pos_right m he0), hmn⟩, dvd_mul_left v.deg m⟩
    have hinj : Set.InjOn (fun m => m * v.deg) ↑(Icc 1 (n / v.deg)) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right he0 hab
    rw [himg, Finset.sum_image hinj]

    have hb : ∀ m ∈ Icc 1 (n / v.deg),
        A (n - m * v.deg) = ((Ef n).filter fun D => (m : ℤ) ≤ D v).card := by
      intro m hm
      rw [Finset.mem_Icc, Nat.le_div_iff_mul_le he0] at hm
      rw [hA]
      exact card_eff_sub_eq_card_filter n m v hm.2 (Ef n) (Ef (n - m * v.deg)) (hmemEf n)
        (hmemEf (n - m * v.deg))
    rw [Finset.sum_congr rfl (fun m hm => by rw [hb m hm]), ← Finset.mul_sum]

    have hc : ∑ m ∈ Icc 1 (n / v.deg), ((Ef n).filter fun D => (m : ℤ) ≤ D v).card
        = ∑ D ∈ Ef n, (D v).toNat := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun D hD => ?_
      rw [← Finset.card_filter]
      have hDv : (D v).toNat ≤ n / v.deg := by
        rw [Nat.le_div_iff_mul_le he0]
        exact hEn_coef D hD v
      obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (hEn_nonneg D hD v)
      rw [hc, Int.toNat_natCast] at hDv ⊢
      have hI : (Icc 1 (n / v.deg)).filter (fun m : ℕ => (m : ℤ) ≤ (c : ℤ)) = (Icc 1 c : Finset ℕ) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.cast_le]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2.trans hDv⟩, h2⟩
      rw [hI, Nat.card_Icc]
      omega
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    ring

  rw [hLHS, hR2, Finset.sum_congr rfl hR3, Finset.sum_comm]

end Finite

end AlgebraicCurve.CardEffectiveDivisorsSol

theorem solution
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F] [Algebra.EssFiniteType k F] (n : ℕ) :
    n * Nat.card {D : AlgebraicCurve.Divisor k F //
        0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)} =
      ∑ r ∈ Finset.Icc 1 n,
        (∑ d ∈ Nat.divisors r, d * Nat.card {v : AlgebraicCurve.Place k F | v.deg = d}) *
          Nat.card {D : AlgebraicCurve.Divisor k F //
            0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = ((n - r : ℕ) : ℤ)} :=
  AlgebraicCurve.CardEffectiveDivisorsSol.main n

end S_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
end P2MW
export P2MW.S_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum (solution)
