-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:41:30.914634+00:00
-- url     : https://prove2.me/theorems/73060d31-2337-51bf-af9c-9092134c7aa4
-- title:
--   PTwin Eq Bundle
-- statement:
--   Definitions and structural lemmas for PTwin Eq Bundle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_and_invertible_of_frame_f159bf763875
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
theorem div_mem_chartRing_of_mem (I : Kleiman.Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1)
    (j : Fin (N + 1)) : x j / x i ∈ Kleiman.chartRing S x I :=
  ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩
def pairChart {i j : Fin (N + 1)} (hi : x i ≠ 0) (hj : x j ≠ 0) : Kleiman.Chart x :=
  ⟨{i, j}, Finset.insert_nonempty i {j}, by
    intro l hl
    rcases Finset.mem_insert.1 hl with h | h
    · rw [h]; exact (Kleiman.mem_support x).2 hi
    · rw [Finset.mem_singleton.1 h]; exact (Kleiman.mem_support x).2 hj⟩
theorem exists_pow_mul_mem_of_pair {i j : Fin (N + 1)} (hi : x i ≠ 0) (hj : x j ≠ 0) {v : Ω}
    (hv : v ∈ Kleiman.chartRing S x (pairChart hi hj)) :
    ∃ m : ℕ, (x i / x j) ^ m * v ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x j := by
  rw [← chartRingI.equiv] at hv
  have hij : x i / x j ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  induction hv using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, k, rfl⟩ := hy
    change l ∈ ({i, j} : Finset (Fin (N + 1))) at hl
    rcases Finset.mem_insert.1 hl with h | h
    · subst h
      refine ⟨1, ?_⟩
      have : x l / x j * (x k / x l) = x k / x j := by field_simp
      rw [pow_one, this]
      exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k
    · rw [Finset.mem_singleton.1 h]
      exact ⟨0, by rw [pow_zero, one_mul]; exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j k⟩
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn
theorem exists_sum_mul_eq {A : Subalgebra S Ω} {P P' : Submodule A Ω} {z : Ω} (hz : z ∈ P * P') :
    ∃ (k : ℕ) (q q' : Fin k → Ω), (∀ l, q l ∈ P) ∧ (∀ l, q' l ∈ P') ∧ ∑ l, q l * q' l = z := by
  refine Submodule.mul_induction_on hz
    (fun p hp p' hp' => ⟨1, fun _ => p, fun _ => p', fun _ => hp, fun _ => hp', by simp⟩) ?_
  intro u v hu hv
  obtain ⟨k, q, q', hq, hq', rfl⟩ := hu
  obtain ⟨k', r, r', hr, hr', rfl⟩ := hv
  refine ⟨k + k', Fin.append q r, Fin.append q' r', fun l => ?_, fun l => ?_, ?_⟩
  · induction l using Fin.addCases with
    | left l => simpa using hq l
    | right l => simpa using hr l
  · induction l using Fin.addCases with
    | left l => simpa using hq' l
    | right l => simpa using hr' l
  · rw [Fin.sum_univ_add]
    simp
section First
variable (Q : Kleiman.LineBundle S x)
theorem ofFirst_stable (i : Fin (N + 1)) (a : Ω) (ha : a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) (e : Ω)
    (he : e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i) : a • e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i := by
  by_cases h : x i ≠ 0
  · rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem] at he ⊢
    rw [chartRing.equiv S x h] at ha
    exact (Q.sub _).smul_mem (⟨a, ha⟩ : Kleiman.chartRing S x _) he
  · have h0 : toIndefiniteRowSideFullHecke Q.toSubSystem i = ⊥ := dif_neg h
    rw [h0, Submodule.mem_bot] at he ⊢
    rw [he, smul_zero]
theorem ofFirst_overlap (i j : Fin (N + 1)) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : Ω)
    (he : e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ toIndefiniteRowSideFullHecke Q.toSubSystem j := by
  rw [chartModule_of_ne_zero _ hi, Submodule.restrictScalars_mem] at he
  have hiI : (Kleiman.singleChart hi).1 ⊆ (pairChart hi hj).1 := by
    change ({i} : Finset (Fin (N + 1))) ⊆ {i, j}
    simp
  have hjI : (Kleiman.singleChart hj).1 ⊆ (pairChart hi hj).1 := by
    change ({j} : Finset (Fin (N + 1))) ⊆ {i, j}
    simp
  obtain ⟨a, ⟨u, hu⟩, hae⟩ := (Q.mem_iff _ _ hjI e).1 (Q.mono _ _ hiI e he)
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_pair hi hj (↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)).2
  rw [chartRing.equiv S x hj] at hm
  refine ⟨m, ?_⟩
  have hinv : ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul u)
    rw [hu] at this
    exact this
  have key : (x i / x j) ^ m • e =
      (⟨_, hm⟩ : Kleiman.chartRing S x (Kleiman.singleChart hj)) • ((a : Ω) • e) := by
    rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    change (x i / x j) ^ m * e =
      (x i / x j) ^ m * ((↑u⁻¹ : Kleiman.chartRing S x (pairChart hi hj)) : Ω) * ((a : Ω) * e)
    rw [show ∀ w : Ω, (x i / x j) ^ m * w * ((a : Ω) * e) = (x i / x j) ^ m * (w * a) * e from
      fun w => by ring, hinv, mul_one]
  rw [chartModule_of_ne_zero _ hj, Submodule.restrictScalars_mem, key]
  exact Submodule.smul_mem _ _ hae
theorem ofFirst_frame (i : Fin (N + 1)) (h : x i ≠ 0) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧
      (∀ l, c l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
        ∀ e, (∃ n : ℕ, f l ^ n • e ∈ (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup) ↔
          ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i) ∧
            e = ∑ q, a q • b q := by
  obtain ⟨Q'', hQ⟩ := Q.invertible (Kleiman.singleChart h)
  have h1 : (1 : Ω) ∈ Q.sub (Kleiman.singleChart h) * Q'' := hQ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
  obtain ⟨k, q, q', hq, hq', hsum⟩ := exists_sum_mul_eq h1
  have hprod : ∀ {p p' : Ω}, p ∈ Q.sub (Kleiman.singleChart h) → p' ∈ Q'' →
      p * p' ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i := by
    intro p p' hp hp'
    have := Submodule.mul_mem_mul hp hp'
    rw [hQ, Submodule.mem_one] at this
    obtain ⟨a, ha⟩ := this
    rw [chartRing.equiv S x h, ← ha]
    exact a.2
  have hmem : ∀ e, e ∈ (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup ↔ e ∈ Q.sub (Kleiman.singleChart h) := by
    intro e
    rw [Submodule.mem_toAddSubgroup, chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]
  refine ⟨k, fun l => q l * q' l, fun _ => 1, fun l => hprod (hq l) (hq' l), fun _ => one_mem _,
    by simpa using hsum, fun l => ?_⟩
  by_cases hq0 : q l = 0
  · refine ⟨fun _ => 1, ?_, ?_, fun e => ⟨fun _ => ⟨fun _ => e, fun _ => ⟨1, by simp [hq0]⟩, by simp⟩,
      fun _ => ⟨1, by simp [hq0]⟩⟩⟩
    · rw [linearIndependent_unique_iff]
      exact one_ne_zero
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 isUnit_one
  · refine ⟨fun _ => q l, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [linearIndependent_unique_iff]
      exact hq0
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 hq0)
    · rintro ⟨n, hn⟩
      rw [hmem] at hn
      refine ⟨fun _ => e / q l, fun _ => ⟨n + 1, ?_⟩, ?_⟩
      · have : (q l * q' l) ^ (n + 1) * (e / q l) = ((q l * q' l) ^ n • e) * q' l := by
          rw [smul_eq_mul]
          field_simp
          ring
        rw [this]
        exact hprod hn (hq' l)
      · rw [Fin.sum_univ_one, smul_eq_mul]
        field_simp
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨n, hn⟩ := ha 0
      rw [chartRing.equiv S x h] at hn
      refine ⟨n, ?_⟩
      rw [hmem, Fin.sum_univ_one]
      have : (q l * q' l) ^ n • (a 0 • q l) =
          (⟨_, hn⟩ : Kleiman.chartRing S x (Kleiman.singleChart h)) • q l := by
        rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (hq l)
def ofFirst : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x where
  lat i := (toIndefiniteRowSideFullHecke Q.toSubSystem i).toAddSubgroup
  stable i a ha e he := ofFirst_stable Q i a ha e he
  frame i h := ofFirst_frame Q i h
  overlap i j hi hj e he := ofFirst_overlap Q i j hi hj e he
end First
section Second
variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)
def latSub {i : Fin (N + 1)} (h : x i ≠ 0) :
    Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω where
  carrier := Q'.lat i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a e he := Q'.stable i a (by rw [chartRing.equiv S x h]; exact a.2) e he
theorem coe_latSub {i : Fin (N + 1)} (h : x i ≠ 0) : (latSub Q' h : Set Ω) = (Q'.lat i : Set Ω) := rfl
def subOf (I : Kleiman.Chart x) : Submodule (Kleiman.chartRing S x I) Ω :=
  Submodule.span _ (⋃ i ∈ I.1, (Q'.lat i : Set Ω))
theorem subOf_eq {I : Kleiman.Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) :
    subOf Q' I = Submodule.span _ (Q'.lat i : Set Ω) := by
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  apply le_antisymm
  · rw [subOf, Submodule.span_le]
    intro e he
    obtain ⟨j, hj, he⟩ := Set.mem_iUnion₂.1 he
    have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hj)
    obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi e he
    have hr : (x i / x j) ^ m ∈ Kleiman.chartRing S x I := pow_mem (div_mem_chartRing_of_mem I hj i) m
    have hc : x i / x j * (x j / x i) = 1 := by field_simp
    have key : e = (⟨_, hr⟩ : Kleiman.chartRing S x I) • ((x j / x i) ^ m • e) := by
      rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, hc, one_pow, one_mul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  · exact Submodule.span_mono fun e he => Set.mem_iUnion₂.2 ⟨i, hi, he⟩
theorem subOf_mono (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) (hy : y ∈ subOf Q' I) :
    y ∈ subOf Q' J := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 hz
    exact Submodule.subset_span (Set.mem_iUnion₂.2 ⟨i, h hi, hz⟩)
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul a z _ hz => exact Submodule.smul_mem _ (Kleiman.chartIncl h a) hz
theorem subOf_mem_iff (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ subOf Q' J ↔
      ∃ a : Kleiman.chartRing S x I, IsUnit (Kleiman.chartIncl h a) ∧ (a : Ω) • y ∈ subOf Q' I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, hj, hz⟩ := Set.mem_iUnion₂.1 hz
      have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (J.2.2 hj)
      obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi z hz
      refine ⟨⟨(x j / x i) ^ m, pow_mem (div_mem_chartRing_of_mem I hi j) m⟩, ?_, ?_⟩
      · rw [isUnit_iff_exists_inv]
        refine ⟨⟨(x i / x j) ^ m, pow_mem (div_mem_chartRing_of_mem J hj i) m⟩, Subtype.ext ?_⟩
        change (x j / x i) ^ m * (x i / x j) ^ m = 1
        have hc : x j / x i * (x i / x j) = 1 := by field_simp
        rw [← mul_pow, hc, one_pow]
      · rw [subOf_eq Q' hi]
        exact Submodule.subset_span hm
    | zero => exact ⟨1, by simp, by rw [smul_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, hau⟩ := hu
      obtain ⟨b, hb, hbv⟩ := hv
      refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
      have : ((a * b : Kleiman.chartRing S x I) : Ω) • (u + v) = b • ((a : Ω) • u) + a • ((b : Ω) • v) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ b hau) (Submodule.smul_mem _ a hbv)
    | smul c z _ hz =>
      obtain ⟨a, ha, haz⟩ := hz
      obtain ⟨a', ha', hc⟩ := Kleiman.exists_isUnit_mul_mem h c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have : ((a' * a : Kleiman.chartRing S x I) : Ω) • (c • z) =
          (⟨(a' : Ω) * c, hc⟩ : Kleiman.chartRing S x I) • ((a : Ω) • z) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ haz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hay' := subOf_mono Q' I J h _ hay
    have hinv : ((↑u⁻¹ : Kleiman.chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ hay'
theorem latSub_fg_invertible {i : Fin (N + 1)} (h : x i ≠ 0) :
    (latSub Q' h).FG ∧ ∃ L' : Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω,
      latSub Q' h * L' = 1 := by
  obtain ⟨k, f, c, hf, hc, hs, hb⟩ := Q'.frame i h
  have hA : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart h) :=
    chartRing.equiv S x h
  simp only [hA] at hf hc hb
  choose b hbli _ hiff using hb
  refine fg_and_invertible_of_frame _ f c (latSub Q' h) (fun l => b l 0) hf hc hs
    (fun l => linearIndependent_unique_iff.1 (hbli l)) (fun l e => ?_)
  have := hiff l e
  simp only [Fin.sum_univ_one, smul_eq_mul] at this
  constructor
  · intro hn
    obtain ⟨a, ha, he⟩ := this.1 hn
    exact ⟨a 0, ha 0, he⟩
  · rintro ⟨a, ha, he⟩
    exact this.2 ⟨fun _ => a, fun _ => ha, he⟩
theorem subOf_fg (I : Kleiman.Chart x) : (subOf Q' I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  rw [subOf_eq Q' hi]
  exact fg_span_of_le hle (latSub_fg_invertible Q' hxi).1
theorem subOf_invertible (I : Kleiman.Chart x) :
    ∃ L' : Submodule (Kleiman.chartRing S x I) Ω, subOf Q' I * L' = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  obtain ⟨L', hL'⟩ := (latSub_fg_invertible Q' hxi).2
  have key := mul_span_eq_one_of_le (B := Kleiman.chartRing S x I) hle hL'
  rw [coe_latSub] at key
  refine ⟨Submodule.span (Kleiman.chartRing S x I) (L' : Set Ω), ?_⟩
  rw [subOf_eq Q' hi]
  exact key
def ofSecond : Kleiman.LineBundle S x where
  sub := subOf Q'
  mono := subOf_mono Q'
  mem_iff := subOf_mem_iff Q'
  fg I := subOf_fg Q' I
  invertible I := subOf_invertible Q' I
end Second
end
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


