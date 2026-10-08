-- Prove2me | solution 1 for ArtinPrimitiveRoots.controlled_predecessors
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:17.103982+00:00
-- url     : https://prove2.me/submissions/67edb21d-3764-4d1d-be56-ff59d9e06758
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_harmonic_mass
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_rough_density
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution
import Theorems.Thm_ArtinPrimitiveRoots_bin_cost
import Theorems.Thm_ArtinPrimitiveRoots_balanced_cost
import Theorems.Thm_ArtinPrimitiveRoots_initial_lower

namespace ArtinPrimitiveRoots.P21controlled_predecessors

open Real Filter Topology MeasureTheory

theorem exists_bump : ∃ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ tsupport Ψ ⊆ Set.Ioo 1 2 ∧
    (∀ y, 0 ≤ Ψ y) ∧ (∀ y, Ψ y ≤ 1) ∧ 0 < ∫ y, Ψ y := by
  let f : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 10, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨f, f.contDiff, ?_, fun y => f.nonneg, fun y => f.le_one, f.integral_pos⟩
  rw [f.tsupport_eq]
  intro y hy
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
  have h : f.rOut = 1 / 4 := rfl
  rw [h] at hy
  constructor <;> linarith [hy.1, hy.2]

theorem singularSeries_pos (M : ℕ) : 0 < singularSeries M := by
  unfold singularSeries
  have hp3 : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (3 : ℝ) ≤ p.1 := fun p => by
    exact_mod_cast p.2.2
  have hg : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
    apply Summable.neg
    have hs : Summable (fun n : ℕ => 9 / 4 * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
    have hs' := hs.comp_injective (Subtype.val_injective (p := fun p : ℕ => p.Prime ∧ 2 < p))
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs'
    · have := hp3 p
      positivity
    · have h3 := hp3 p
      simp only [Function.comp]
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, 0 < 1 + -(1 / ((p.1 : ℝ) - 1) ^ 2) := by
    intro p
    have h3 := hp3 p
    have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    linarith
  have hprod : 0 < ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2) := by
    have := Real.rexp_tsum_eq_tprod hpos (Real.summable_log_one_add_of_summable hg)
    simp only [← sub_eq_add_neg] at this
    rw [← this]
    exact Real.exp_pos _
  apply mul_pos (mul_pos two_pos hprod)
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
  apply inv_pos.mpr
  have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma prod_ordProj_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (h : ℕ) :
    (∏ p ∈ s, p ^ h.factorization p) ∣ h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq]
    have hq' : q.Prime := hs q (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (Nat.ordProj_dvd h q) ih'
    apply Nat.Coprime.prod_right
    intro p hp
    have hp' : p.Prime := hs p (Finset.mem_insert_of_mem hp)
    exact Nat.coprime_pow_primes _ _ hq' hp' (fun e => hq (e ▸ hp))

lemma groupPrimes_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∀ p ∈ groupPrimes x a, p.Prime := by
  intro p hp
  simp only [groupPrimes, primeGroup, Finset.mem_biUnion, Finset.mem_filter] at hp
  obtain ⟨i, -, -, h, -⟩ := hp
  exact h

lemma groupPart_dvd (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : groupPart x a h ∣ h :=
  prod_ordProj_dvd _ (groupPrimes_prime x a) h

lemma groupPart_pos (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 < groupPart x a h := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (groupPrimes_prime x a p hp).pos _

lemma mem_groupPrimes_of_mem_primeFactors (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h ℓ : ℕ)
    (hℓ : ℓ ∈ (groupPart x a h).primeFactors) : ℓ ∈ groupPrimes x a := by
  rw [Nat.mem_primeFactors] at hℓ
  obtain ⟨hℓp, hdvd, -⟩ := hℓ
  unfold groupPart at hdvd
  obtain ⟨p, hp, hdp⟩ := (Prime.dvd_finsetProd_iff hℓp.prime _).mp hdvd
  have hp' := groupPrimes_prime x a p hp
  have := (Nat.prime_dvd_prime_iff_eq hℓp hp').mp (hℓp.dvd_of_dvd_pow hdp)
  rw [this]; exact hp

lemma groupReciprocalSum_nonneg (x a : ℝ) : 0 ≤ groupReciprocalSum x a := by
  unfold groupReciprocalSum
  apply Finset.sum_nonneg
  intro p _
  positivity

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply Finset.prod_nonneg
  intro i _
  exact div_nonneg (Nat.cast_nonneg _) (groupReciprocalSum_nonneg _ _)

lemma two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [pow_succ]; omega

lemma mark_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ)
    (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) : mark (1 / 2) x a h ≤ 2 ^ K := by
  unfold mark markOmega
  set ω : Fin K → ℕ := fun i => groupOmega x (a i) h with hω
  have hnat : 2 ^ K * ∏ i, ω i ≤ 2 ^ (∑ i, ω i) := by
    have h1 : ∏ i, (2 * ω i) ≤ ∏ i, 2 ^ ω i :=
      Finset.prod_le_prod' (fun i _ => two_mul_le_two_pow (ω i))
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at h1
    simpa using h1
  have hreal : (2 : ℝ) ^ K * ∏ i, (ω i : ℝ) ≤ 2 ^ (∑ i, ω i) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  have hz : ((1 : ℝ) / 2) ^ ((∑ i, ω i : ℕ) - (K : ℤ)) = 2 ^ K / 2 ^ (∑ i, ω i) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
    field_simp
  have hprod : ∏ i, (ω i : ℝ) / groupReciprocalSum x (a i) ≤ ∏ i, (ω i : ℝ) * 2 := by
    apply Finset.prod_le_prod
    · intro i _; exact div_nonneg (Nat.cast_nonneg _) (groupReciprocalSum_nonneg _ _)
    · intro i _
      rw [div_le_iff₀ (by linarith [hV i])]
      have := hV i
      have h0 : (0 : ℝ) ≤ ω i := Nat.cast_nonneg _
      nlinarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [hz]
  have hpos : (0 : ℝ) < 2 ^ (∑ i, ω i) := by positivity
  calc (2 : ℝ) ^ K / 2 ^ (∑ i, ω i) * ∏ i, (ω i : ℝ) / groupReciprocalSum x (a i)
      ≤ 2 ^ K / 2 ^ (∑ i, ω i) * ((∏ i, (ω i : ℝ)) * 2 ^ K) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (2 ^ K * ∏ i, (ω i : ℝ)) / 2 ^ (∑ i, ω i) * 2 ^ K := by ring
    _ ≤ 1 * 2 ^ K := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one hpos]; exact hreal
    _ = 2 ^ K := one_mul _

lemma predecessorIndicator_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    0 ≤ predecessorIndicator x a c h := by
  unfold predecessorIndicator; split_ifs <;> norm_num

lemma predecessorIndicator_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) :
    predecessorIndicator x a c h ≤ 1 := by
  unfold predecessorIndicator; split_ifs <;> norm_num

lemma constructionWeight_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ)
    {K : ℕ} (a : Fin K → ℝ) (d : ℕ) : 0 ≤ constructionWeight M c u Ψ x a d := by
  unfold constructionWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (hΨ0 _) (predecessorIndicator_nonneg _ _ _ _))
      (mark_nonneg _ _ _)
  · exact le_rfl

lemma constructionWeight_le (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y)
    (hΨ1 : ∀ y, Ψ y ≤ 1) (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) (d : ℕ) :
    constructionWeight M c u Ψ x a d ≤ 2 ^ K := by
  unfold constructionWeight
  split_ifs
  · have h1 := predecessorIndicator_le_one x a c (d - 1)
    have h2 := mark_le x a (d - 1) hV
    have h3 := hΨ1 (d / x)
    have h4 := hΨ0 (d / x)
    have h5 := predecessorIndicator_nonneg x a c (d - 1)
    have h6 := mark_nonneg x a (d - 1)
    calc Ψ (d / x) * predecessorIndicator x a c (d - 1) * mark (1 / 2) x a (d - 1)
        ≤ 1 * 1 * 2 ^ K := by
          apply mul_le_mul (mul_le_mul h3 h1 h5 zero_le_one) h2 h6 (by norm_num)
      _ = 2 ^ K := by ring
  · positivity

lemma constructionWeight_support (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ)
    (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ)
    (hd : constructionWeight M c u Ψ x a d ≠ 0) :
    2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M] ∧ x < d ∧ (d : ℝ) < 2 * x ∧
      ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ (d - 1) / groupPart x a (d - 1) = c * Q := by
  unfold constructionWeight at hd
  split_ifs at hd with h
  · refine ⟨h.1, h.2, ?_⟩
    have hΨ : Ψ (d / x) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hF : predecessorIndicator x a c (d - 1) ≠ 0 := fun e => hd (by rw [e]; ring)
    have hmem := hΨs (subset_tsupport _ hΨ)
    rw [Set.mem_Ioo, lt_div_iff₀ hx, div_lt_iff₀ hx] at hmem
    refine ⟨by linarith [hmem.1], by linarith [hmem.2], ?_⟩
    unfold predecessorIndicator at hF
    split_ifs at hF with hQ
    · exact hQ
    · exact absurd rfl hF
  · exact absurd rfl hd

lemma eventually_groupReciprocalSum (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 / 2 ≤ groupReciprocalSum x a := by
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 / 2 : ℝ) < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have h1 := hm.eventually (eventually_gt_nhds hlog)
  have hX : Tendsto (fun x : ℝ => exp (log x ^ a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop)
  filter_upwards [hX.eventually h1] with x hx
  refine le_trans hx.le ?_
  unfold groupReciprocalSum primeGroup
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2.1, ?_⟩
    · have : exp (log x ^ a) ^ (2 : ℝ) = exp (2 * log x ^ a) := by
        rw [← Real.exp_mul, mul_comm]
      rw [← this]; exact hp.1
    · have := hp.2.2
      rw [Real.rpow_one] at this
      exact this.le
  · intro p _ _
    positivity

lemma eventually_groupReciprocalSum_all {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in atTop, ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i) :=
  Filter.eventually_all.mpr fun i => eventually_groupReciprocalSum (a i) (ha i)

lemma weight_eq_zero_of_ge (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (d : ℕ) (hd : ⌈2 * x⌉₊ ≤ d) :
    constructionWeight M c u Ψ x a d = 0 := by
  by_contra hne
  have := (constructionWeight_support M c u Ψ hΨs x hx a d hne).2.2.2.1
  have h2 : (⌈2 * x⌉₊ : ℝ) ≤ d := by exact_mod_cast hd
  have h3 := Nat.le_ceil (2 * x)
  linarith

lemma summable_weight (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun d : ℕ => if P d then constructionWeight M c u Ψ x a d else 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊)
  intro d hd
  simp only [Finset.mem_range, not_lt] at hd
  rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx a d hd]
  simp

lemma tsum_weight_eq_sum (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    ∑' d : ℕ, (if P d then constructionWeight M c u Ψ x a d else 0) =
      ∑ d ∈ Finset.range ⌈2 * x⌉₊, (if P d then constructionWeight M c u Ψ x a d else 0) := by
  apply tsum_eq_sum
  intro d hd
  simp only [Finset.mem_range, not_lt] at hd
  rw [weight_eq_zero_of_ge M c u Ψ hΨs x hx a d hd]
  simp

lemma totalMass_nonneg (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : 0 ≤ totalMass M c u Ψ x a :=
  tsum_nonneg fun d => constructionWeight_nonneg M c u Ψ hΨ0 x a d

open Classical in
theorem count_from_mass (M c : ℕ) (u : ℤ) (hM : 0 < M)
    (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨ0 : ∀ y, 0 ≤ Ψ y)
    (K : ℕ) (hK : 1 ≤ K) (a : Fin K → ℝ) (ha' : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) :
    ∃ B : ℝ, 0 < B ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∑' d : ℕ, (if d.Prime then constructionWeight M c u Ψ x a d else 0) ≤
        B * (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
          ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
            ∀ ℓ ∈ r.primeFactors, Real.exp (Real.log x ^ (0.1 : ℝ)) < ℓ ∧
              (ℓ : ℝ) < Real.exp (Real.log x ^ (0.3 : ℝ))} : ℝ) := by
  have hev := (eventually_groupReciprocalSum_all a (fun i => by linarith [(ha' i).1])).and
    ((Real.tendsto_log_atTop.eventually_gt_atTop 1).and
      ((((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.1)).comp
        Real.tendsto_log_atTop).eventually_gt_atTop 2).and (eventually_gt_atTop 0)))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨2 ^ K, by positivity, x₀, fun x hx => ?_⟩
  obtain ⟨hV, hL, hL01, hxpos⟩ := hx₀ x hx
  simp only [Function.comp] at hL01
  set S := {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
          ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
            ∀ ℓ ∈ r.primeFactors, Real.exp (Real.log x ^ (0.1 : ℝ)) < ℓ ∧
              (ℓ : ℝ) < Real.exp (Real.log x ^ (0.3 : ℝ))} with hSdef
  set N := ⌈2 * x⌉₊ with hN
  set f : ℕ → ℝ := fun d => if d.Prime then constructionWeight M c u Ψ x a d else 0 with hf
  have hf0 : ∀ d ∉ Finset.range N, f d = 0 := by
    intro d hd
    simp only [Finset.mem_range, not_lt] at hd
    simp only [hf]
    split_ifs
    · by_contra hne
      have := (constructionWeight_support M c u Ψ hΨs x hxpos a d hne).2.2.2.1
      have h2 : (N : ℝ) ≤ d := by exact_mod_cast hd
      have h3 := Nat.le_ceil (2 * x)
      linarith
    · rfl
  rw [tsum_eq_sum hf0]
  set F := (Finset.range N).filter (fun d => d.Prime ∧ constructionWeight M c u Ψ x a d ≠ 0)
  have h1 : ∑ d ∈ Finset.range N, f d = ∑ d ∈ F, f d := by
    rw [Finset.sum_filter_of_ne]
    intro d _ hd
    simp only [hf] at hd
    split_ifs at hd with hp
    · exact ⟨hp, hd⟩
    · exact absurd rfl hd
  have h2 : ∑ d ∈ F, f d ≤ ∑ d ∈ F, (2 : ℝ) ^ K := by
    apply Finset.sum_le_sum
    intro d _
    simp only [hf]
    split_ifs
    · exact constructionWeight_le M c u Ψ hΨ0 hΨ1 x a hV d
    · positivity
  have hsub : (F : Set ℕ) ⊆ S := by
    intro d hd
    simp only [F, Finset.coe_filter, Set.mem_ofPred_eq] at hd
    obtain ⟨-, hp, hw⟩ := hd
    obtain ⟨hd2, hdu, hxd, hd2x, Q, hQ, hQx, hdiv⟩ :=
      constructionWeight_support M c u Ψ hΨs x hxpos a d hw
    refine ⟨hp, hxd, hd2x, hdu, groupPart x a (d - 1), Q, ?_, hQ, hQx,
      groupPart_pos x a (d - 1), ?_⟩
    · have := Nat.div_mul_cancel (groupPart_dvd x a (d - 1))
      rw [hdiv] at this
      exact this.symm.trans (by ring)
    · intro ℓ hℓ
      have hg := mem_groupPrimes_of_mem_primeFactors x a (d - 1) ℓ hℓ
      simp only [groupPrimes, primeGroup, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_range, Finset.mem_univ, true_and] at hg
      obtain ⟨i, hle, -, hge⟩ := hg
      have hai := ha' i
      have hL0 : 0 < log x := by linarith
      constructor
      · refine lt_of_lt_of_le ?_ hge
        apply Real.exp_lt_exp.mpr
        exact Real.rpow_lt_rpow_of_exponent_lt hL (by linarith [hai.1])
      · have hle' : (ℓ : ℝ) ≤ exp (2 * log x ^ a i) := by
          have := Nat.le_of_lt_succ hle
          exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
        refine lt_of_le_of_lt hle' (Real.exp_lt_exp.mpr ?_)
        have h03 : log x ^ (0.3 : ℝ) = log x ^ ((0.3 : ℝ) - a i) * log x ^ a i := by
          rw [← Real.rpow_add hL0]; ring_nf
        have hge2 : 2 < log x ^ ((0.3 : ℝ) - a i) := by
          refine lt_of_lt_of_le hL01 ?_
          exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith [hai.2])
        rw [h03]
        have : 0 < log x ^ a i := Real.rpow_pos_of_pos hL0 _
        nlinarith
  have hSfin : S.Finite := by
    apply (Finset.range N).finite_toSet.subset
    intro p hp
    simp only [hSdef, Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_range, Set.mem_Iio]
    have := Nat.le_ceil (2 * x)
    have h' : (p : ℝ) < N := by linarith [hp.2.2.1]
    exact_mod_cast h'
  have hcard : (F.card : ℝ) ≤ Nat.card S := by
    have := Nat.card_mono hSfin hsub
    simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this
    exact_mod_cast this
  rw [h1]
  refine le_trans h2 ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left hcard (by positivity)

/-- The integration region of `D_{γ,j}` with `n = j - 1` variables. -/
def regionD (n : ℕ) (γ w : ℝ) : Set (Fin n → ℝ) :=
  {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}

/-- The integrand of `D_{γ,j}`. -/
noncomputable def integrandD (n : ℕ) (w : ℝ) (t : Fin n → ℝ) : ℝ :=
  (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹

lemma regionD_closed (n : ℕ) (γ w : ℝ) : IsClosed (regionD n γ w) := by
  unfold regionD
  rw [Set.setOf_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

lemma measurable_integrandD (n : ℕ) (w : ℝ) : Measurable (integrandD n w) := by
  unfold integrandD
  apply Measurable.mul
  · exact (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).inv
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma regionD_empty (n : ℕ) (γ w : ℝ) (h : w < (n + 1) * γ) : regionD n γ w = ∅ := by
  ext t
  simp only [regionD, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro ht
  have : ∑ _i : Fin n, γ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

lemma sum_hyperplane_null (n : ℕ) (hn : 0 < n) (c : ℝ) :
    volume {t : Fin n → ℝ | ∑ i, t i = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ t, L t = ∑ i, t i := fun t => by
    simp [L, LinearMap.sum_apply]
  let i₀ : Fin n := ⟨0, hn⟩
  let p : Fin n → ℝ := Pi.single i₀ c
  have hp : ∑ i, p i = c := by simp [p]
  let s : AffineSubspace ℝ (Fin n → ℝ) := AffineSubspace.mk' p (LinearMap.ker L)
  have hsub : {t : Fin n → ℝ | ∑ i, t i = c} ⊆ s := by
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    show t ∈ s
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hL, hL, ht, hp, sub_self]
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : p + Pi.single i₀ 1 ∈ s := by rw [htop]; exact AffineSubspace.mem_top _ _ _
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hL, hL] at hmem
    simp [p, Finset.sum_add_distrib] at hmem
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume s hne)

/-- Continuity of `∫_{regionD n γ w} integrandD n w`. -/
lemma continuousAt_integralD (n : ℕ) (hn : 0 < n) (γ₀ w₀ : ℝ) (hγ₀ : 0 < γ₀) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => ∫ t in regionD n p.1 p.2, integrandD n p.2 t) (γ₀, w₀) := by
  have hmeas : ∀ γ w, MeasurableSet (regionD n γ w) := fun γ w =>
    (regionD_closed n γ w).measurableSet
  simp_rw [← integral_indicator (hmeas _ _)]
  set C : ℝ := (2 / γ₀) ^ (n + 1) with hC
  set box : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (γ₀ / 2) (2 * w₀)) with hbox
  have hboxm : MeasurableSet box := (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  have hnbhd : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 ∧ p.2 < 2 * w₀ := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 < 2 * w₀ :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds (by linarith))
    exact h1.and h2
  apply continuousAt_of_dominated (bound := box.indicator (fun _ => C))
  · exact Eventually.of_forall fun p =>
      ((measurable_integrandD n p.2).indicator (hmeas _ _)).aestronglyMeasurable
  · filter_upwards [hnbhd] with p hp
    refine Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ regionD n p.1 p.2
    · rw [Set.indicator_of_mem ht]
      obtain ⟨ht1, ht2⟩ := ht
      have htpos : ∀ i, γ₀ / 2 < t i := fun i => lt_of_lt_of_le hp.1 (ht1 i)
      have htle : ∀ i, t i ≤ 2 * w₀ := by
        intro i
        have : t i ≤ ∑ j, t j :=
          Finset.single_le_sum (fun j _ => le_trans (by linarith) (htpos j).le) (Finset.mem_univ i)
        linarith [hp.1, hp.2]
      have htbox : t ∈ box := by
        simp only [hbox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        exact fun i => ⟨(htpos i).le, htle i⟩
      rw [Set.indicator_of_mem htbox]
      have hden : γ₀ / 2 < p.2 - ∑ i, t i := by linarith [hp.1]
      unfold integrandD
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith))
        (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [htpos i])))]
      rw [hC, pow_succ']
      apply mul_le_mul
      · rw [inv_le_comm₀ (by linarith) (by positivity)]
        rw [inv_div]; exact hden.le
      · calc ∏ i, (t i)⁻¹ ≤ ∏ _i : Fin n, 2 / γ₀ := by
              apply Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (by linarith [htpos i]))
              intro i _
              rw [inv_le_comm₀ (by linarith [htpos i]) (by positivity), inv_div]
              exact (htpos i).le
          _ = (2 / γ₀) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · exact Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [htpos i])
      · positivity
    · rw [Set.indicator_of_notMem ht, norm_zero]
      apply Set.indicator_nonneg
      intro _ _; positivity
  · apply (integrableOn_const ?_).integrable_indicator hboxm
    exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne
  · -- continuity off the boundary hyperplanes
    have hnull1 : ∀ᵐ t : Fin n → ℝ, ∀ i, t i ≠ γ₀ := by
      rw [ae_all_iff]
      intro i
      have := Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i γ₀
      rwa [← volume_pi] at this
    have hnull2 : ∀ᵐ t : Fin n → ℝ, ∑ i, t i ≠ w₀ - γ₀ :=
      compl_mem_ae_iff.mpr (sum_hyperplane_null n hn (w₀ - γ₀))
    filter_upwards [hnull1, hnull2] with t ht1 ht2
    by_cases hin : t ∈ regionD n γ₀ w₀
    · obtain ⟨hin1, hin2⟩ := hin
      have hs1 : ∀ i, γ₀ < t i := fun i => lt_of_le_of_ne (hin1 i) (ht1 i).symm
      have hs2 : ∑ i, t i < w₀ - γ₀ := lt_of_le_of_ne hin2 ht2
      have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t ∈ regionD n p.1 p.2 := by
        have hmin : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), ∀ i, p.1 < t i :=
          Filter.eventually_all.mpr fun i =>
            continuous_fst.continuousAt.eventually (gt_mem_nhds (hs1 i))
        have hsum : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), ∑ i, t i < p.2 - p.1 :=
          (continuous_snd.sub continuous_fst).continuousAt.eventually (lt_mem_nhds hs2)
        filter_upwards [hmin, hsum] with p h1 h2
        exact ⟨fun i => (h1 i).le, h2.le⟩
      have hcont : ContinuousAt (fun p : ℝ × ℝ => integrandD n p.2 t) (γ₀, w₀) := by
        unfold integrandD
        apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.inv₀ (continuous_snd.sub continuous_const).continuousAt
        show w₀ - ∑ i, t i ≠ 0
        linarith
      refine hcont.congr ?_
      filter_upwards [hev] with p hp
      rw [Set.indicator_of_mem hp]
    · have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t ∉ regionD n p.1 p.2 := by
        simp only [regionD, Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hin ⊢
        rcases hin with ⟨i, hi⟩ | hs
        · have : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), t i < p.1 :=
            continuous_fst.continuousAt.eventually (lt_mem_nhds hi)
          filter_upwards [this] with p hp
          exact Or.inl ⟨i, hp⟩
        · have : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 - p.1 < ∑ i, t i :=
            (continuous_snd.sub continuous_fst).continuousAt.eventually (gt_mem_nhds hs)
          filter_upwards [this] with p hp
          exact Or.inr hp
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hev] with p hp
      rw [Set.indicator_of_notMem hp]

lemma roughDensityTerm_succ_succ (γ w : ℝ) (j : ℕ) :
    roughDensityTerm γ w (j + 2) =
      (1 / ((j + 2).factorial : ℝ)) * ∫ t in regionD (j + 1) γ w, integrandD (j + 1) w t := rfl

theorem roughDensity_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => roughDensity p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  intro p₀ hp₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨γ₀, w₀⟩ := p₀
  simp only [Set.mem_prod, Set.mem_Ioi] at hp₀
  obtain ⟨hγ₀, hw₀⟩ := hp₀
  set N : ℕ := ⌈4 * w₀ / γ₀⌉₊ + 2 with hN
  have hnbhd : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 ∧ p.2 < 2 * w₀ ∧ 0 < p.2 := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), γ₀ / 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), p.2 < 2 * w₀ :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds (by linarith))
    have h3 : ∀ᶠ p : ℝ × ℝ in 𝓝 (γ₀, w₀), 0 < p.2 :=
      continuous_snd.continuousAt.eventually (lt_mem_nhds hw₀)
    exact h1.and (h2.and h3)
  have heq : (fun p : ℝ × ℝ => roughDensity p.1 p.2) =ᶠ[𝓝 (γ₀, w₀)]
      fun p => ∑ j ∈ Finset.range N, roughDensityTerm p.1 p.2 j := by
    filter_upwards [hnbhd] with p hp
    unfold roughDensity
    apply tsum_eq_sum
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    rw [roughDensityTerm_succ_succ, regionD_empty, Measure.restrict_empty, integral_zero_measure,
      mul_zero]
    have hceil := Nat.le_ceil (4 * w₀ / γ₀)
    rw [div_le_iff₀ hγ₀] at hceil
    have hk : (N : ℝ) ≤ k + 2 := by exact_mod_cast hj
    have hN' : (N : ℝ) = ⌈4 * w₀ / γ₀⌉₊ + 2 := by rw [hN]; push_cast; ring
    push_cast
    have : (⌈4 * w₀ / γ₀⌉₊ : ℝ) * (γ₀ / 2) < (k + 1 + 1) * p.1 := by
      have h0 : (0 : ℝ) ≤ ⌈4 * w₀ / γ₀⌉₊ := Nat.cast_nonneg _
      nlinarith [hp.1]
    nlinarith [hp.2.1]
  refine ContinuousAt.congr ?_ heq.symm
  have hterm : ∀ j, ContinuousAt (fun p : ℝ × ℝ => roughDensityTerm p.1 p.2 j) (γ₀, w₀) := by
    intro j
    match j with
    | 0 => simp only [roughDensityTerm]; exact continuousAt_const
    | 1 =>
      simp only [roughDensityTerm]
      exact (continuousAt_const.div continuous_snd.continuousAt hw₀.ne')
    | k + 2 =>
      simp only [roughDensityTerm_succ_succ]
      exact continuousAt_const.mul
        (continuousAt_integralD (k + 1) (Nat.succ_pos k) γ₀ w₀ hγ₀ hw₀)
  exact tendsto_finsetSum _ fun j _ => hterm j

lemma roughDensityTerm_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) (j : ℕ) :
    0 ≤ roughDensityTerm γ w j := by
  match j with
  | 0 => simp [roughDensityTerm]
  | 1 => simp only [roughDensityTerm]; positivity
  | j + 2 =>
    simp only [roughDensityTerm]
    apply mul_nonneg (by positivity)
    have hclosed : IsClosed {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} := by
      rw [Set.setOf_and, Set.ofPred_forall]
      exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    apply setIntegral_nonneg hclosed.measurableSet
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    apply mul_nonneg
    · apply inv_nonneg.mpr; linarith
    · apply Finset.prod_nonneg
      intro i _
      exact inv_nonneg.mpr (le_trans hγ.le (h1 i))

lemma roughDensity_nonneg (γ w : ℝ) (hγ : 0 < γ) (hw : 0 < w) : 0 ≤ roughDensity γ w :=
  tsum_nonneg fun j => roughDensityTerm_nonneg γ w hγ hw j

lemma continuousOn_F (b B : ℝ) (hb : 0 < b) (hB : B < 1) :
    ContinuousOn (fun p : ℝ × ℝ => roughDensity p.1 (1 - p.2))
      (Set.Icc b B ×ˢ Set.Icc b B) := by
  apply roughDensity_continuousOn.comp
    (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn
  intro p hp
  simp only [Set.mem_prod, Set.mem_Icc] at hp
  show 0 < p.1 ∧ 0 < 1 - p.2
  constructor <;> linarith [hp.1.1, hp.2.2]

lemma continuousOn_f (b B : ℝ) (hb : 0 < b) (hB : B < 1) :
    ContinuousOn (fun t : ℝ => roughDensity t (1 - t) / t) (Set.Icc b B) := by
  apply ContinuousOn.div _ continuousOn_id
  · intro t ht; simp only [id]; linarith [ht.1]
  apply roughDensity_continuousOn.comp
    (continuous_id.prodMk (continuous_const.sub continuous_id)).continuousOn
  intro t ht
  show 0 < t ∧ 0 < 1 - t
  constructor <;> linarith [ht.1, ht.2]

lemma intervalIntegrable_f (b B c d : ℝ) (hb : 0 < b) (hB : B < 1) (hc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ B) :
    IntervalIntegrable (fun t : ℝ => roughDensity t (1 - t) / t) volume c d := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hcd]
  exact (continuousOn_f b B hb hB).mono (Set.Icc_subset_Icc hc hd)

theorem density_integral_le (b κ : ℝ) (hb : 0 < b) (hκ : 0 < κ) (hbκ : b < 1 / 2 - κ) :
    (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) ≤
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t := by
  have h1 := intervalIntegrable_f b (1 / 2) b (1 / 2 - κ) hb (by norm_num) le_rfl hbκ.le
    (by linarith)
  have h2 := intervalIntegrable_f b (1 / 2) (1 / 2 - κ) (1 / 2) hb (by norm_num) hbκ.le
    (by linarith) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have : 0 ≤ ∫ t in (1 / 2 - κ)..(1 / 2), roughDensity t (1 - t) / t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact div_nonneg (roughDensity_nonneg t (1 - t) ht0 (by linarith [ht.2])) ht0.le
  linarith

theorem density_partition (b κ : ℝ) (hb : 0 < b) (hκ : 0 < κ) (hbκ : b < 1 / 2 - κ) :
    ∃ J : ℕ, ∃ γ S : ℕ → ℝ, γ 0 = b ∧ γ J = 1 / 2 - κ ∧ (∀ j < J, γ j < γ (j + 1)) ∧
      (∀ j < J, ∀ t ∈ Set.Icc (γ j) (γ (j + 1)), roughDensity (γ j) (1 - t) ≤ S j) ∧
      ∑ j ∈ Finset.range J, S j * log (γ (j + 1) / γ j) ≤
        (∫ t in b..(1 / 2 - κ), roughDensity t (1 - t) / t) + 0.1 := by
  set B := 1 / 2 - κ with hBdef
  have hB1 : B < 1 := by linarith
  set F : ℝ × ℝ → ℝ := fun p => roughDensity p.1 (1 - p.2) with hF
  have hUC : UniformContinuousOn F (Set.Icc b B ×ˢ Set.Icc b B) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (continuousOn_F b B hb hB1)
  have hlogpos : 0 < log (B / b) := Real.log_pos (by rw [lt_div_iff₀ hb]; linarith)
  set ε' := 0.1 / (2 * log (B / b) + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'log : 2 * ε' * log (B / b) ≤ 0.1 := by
    rw [hε']
    rw [show 2 * (0.1 / (2 * log (B / b) + 1)) * log (B / b) =
      0.1 * (2 * log (B / b) / (2 * log (B / b) + 1)) by ring]
    have : 2 * log (B / b) / (2 * log (B / b) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp hUC ε' hε'0
  set J : ℕ := ⌈(B - b) / δ⌉₊ + 1 with hJ
  have hJpos : (0 : ℝ) < J := by positivity
  set h := (B - b) / J with hh
  have hhpos : 0 < h := div_pos (by linarith) hJpos
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hJpos]
    have := Nat.le_ceil ((B - b) / δ)
    rw [div_le_iff₀ hδ] at this
    have : (J : ℝ) = ⌈(B - b) / δ⌉₊ + 1 := by rw [hJ]; push_cast; ring
    nlinarith
  set γ : ℕ → ℝ := fun j => b + j * h with hγ
  set S : ℕ → ℝ := fun j => F (γ j, γ j) + ε' with hS
  have hγJ : γ J = B := by
    simp only [hγ, hh]; field_simp; ring
  have hγmem : ∀ j ≤ J, γ j ∈ Set.Icc b B := by
    intro j hj
    have : (j : ℝ) * h ≤ J * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hhpos.le
    have hJh : (J : ℝ) * h = B - b := by rw [hh]; field_simp
    constructor
    · simp only [hγ]; have : 0 ≤ (j : ℝ) * h := by positivity
      linarith
    · simp only [hγ]; linarith
  have hγsucc : ∀ j, γ (j + 1) = γ j + h := by
    intro j; simp only [hγ]; push_cast; ring
  have hγpos : ∀ j, 0 < γ j := fun j => by simp only [hγ]; positivity
  -- pointwise control on a bin
  have hclose : ∀ j < J, ∀ s t, s ∈ Set.Icc (γ j) (γ (j + 1)) →
      t ∈ Set.Icc (γ j) (γ (j + 1)) → |F (s, t) - F (γ j, γ j)| < ε' := by
    intro j hj s t hs ht
    have hj0 := hγmem j hj.le
    have hj1 := hγmem (j + 1) hj
    have hsQ : s ∈ Set.Icc b B := ⟨le_trans hj0.1 hs.1, le_trans hs.2 hj1.2⟩
    have htQ : t ∈ Set.Icc b B := ⟨le_trans hj0.1 ht.1, le_trans ht.2 hj1.2⟩
    have := hδF (s, t) ⟨hsQ, htQ⟩ (γ j, γ j) ⟨hj0, hj0⟩ ?_
    · rwa [Real.dist_eq] at this
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [hγsucc] at hs ht
      apply max_lt
      · rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]
      · rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  refine ⟨J, γ, S, by simp [hγ], hγJ, fun j _ => by rw [hγsucc]; linarith, ?_, ?_⟩
  · intro j hj t ht
    have := hclose j hj (γ j) t ⟨le_rfl, (by rw [hγsucc]; linarith)⟩ ht
    rw [abs_lt] at this
    simp only [hS, hF] at this ⊢
    linarith [this.2]
  · -- per-bin comparison with the integral
    have hbin : ∀ j < J, S j * log (γ (j + 1) / γ j) ≤
        (∫ t in (γ j)..(γ (j + 1)), roughDensity t (1 - t) / t) +
          2 * ε' * log (γ (j + 1) / γ j) := by
      intro j hj
      have hj0 := hγmem j hj.le
      have hj1 := hγmem (j + 1) hj
      have hle : γ j ≤ γ (j + 1) := by rw [hγsucc]; linarith
      have hint := intervalIntegrable_f b B (γ j) (γ (j + 1)) hb hB1 hj0.1 hle hj1.2
      have hconst : IntervalIntegrable (fun t : ℝ => (F (γ j, γ j) - ε') * t⁻¹) volume
          (γ j) (γ (j + 1)) := by
        apply ContinuousOn.intervalIntegrable
        apply continuousOn_const.mul (continuousOn_inv₀.mono _)
        intro t ht
        rw [Set.uIcc_of_le hle] at ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1, hγpos j]
      have hmono := intervalIntegral.integral_mono_on hle hconst hint (fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le (hγpos j) ht.1
        have := hclose j hj t t ht ht
        rw [abs_lt] at this
        simp only [hF] at this
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith [this.1]) (inv_nonneg.mpr ht0.le))
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (hγpos j) (hγpos (j + 1))]
        at hmono
      simp only [hS]
      linarith
    have hsum1 := Finset.sum_le_sum (s := Finset.range J)
      (fun j hj => hbin j (Finset.mem_range.mp hj))
    rw [Finset.sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (fun k hk => intervalIntegrable_f b B (γ k) (γ (k + 1)) hb hB1 (hγmem k hk.le).1
        (by rw [hγsucc]; linarith) (hγmem (k + 1) hk).2)] at hsum1
    have htel : ∑ j ∈ Finset.range J, 2 * ε' * log (γ (j + 1) / γ j) =
        2 * ε' * log (B / b) := by
      rw [← Finset.mul_sum]
      congr 1
      have : ∀ j ∈ Finset.range J, log (γ (j + 1) / γ j) = log (γ (j + 1)) - log (γ j) :=
        fun j _ => Real.log_div (hγpos _).ne' (hγpos _).ne'
      rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j => log (γ j)), hγJ]
      simp only [hγ, Nat.cast_zero, zero_mul, add_zero]
      rw [Real.log_div (by linarith) hb.ne']
    rw [htel] at hsum1
    have h0 : γ 0 = b := by simp [hγ]
    rw [h0, hγJ] at hsum1
    linarith

lemma exists_bin (f : ℕ → ℝ) (v : ℝ) :
    ∀ J : ℕ, f 0 < v → v ≤ f J → ∃ j < J, f j < v ∧ v ≤ f (j + 1)
  | 0, h0, hJ => absurd (lt_of_lt_of_le h0 hJ) (lt_irrefl _)
  | J + 1, h0, hJ => by
    by_cases h : v ≤ f J
    · obtain ⟨j, hj, h1, h2⟩ := exists_bin f v J h0 h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨J, by omega, lt_of_not_ge h, hJ⟩

open Classical in
lemma fiber_le (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 0 < x) {K : ℕ} (a : Fin K → ℝ) (g : ℝ) (n : ℕ)
    (hn : n.Prime) (hgn : g < n) (s : Finset ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d.minFac = n) :
    ∑ d ∈ s, constructionWeight M c u Ψ x a d ≤
      ∑' m : ℕ, (if IsRough g m then constructionWeight M c u Ψ x a (m * n) else 0) := by
  set F : ℕ → ℝ := fun m => if IsRough g m then constructionWeight M c u Ψ x a (m * n) else 0
    with hF
  have hdvd : ∀ d ∈ s, n ∣ d := fun d hd => (hs d hd).2 ▸ Nat.minFac_dvd d
  have hinj : Set.InjOn (fun d : ℕ => d / n) (s : Set ℕ) := by
    intro d₁ h₁ d₂ h₂ h
    exact (Nat.div_left_inj (hdvd d₁ h₁) (hdvd d₂ h₂)).mp h
  have hF0 : ∀ m, 0 ≤ F m := fun m => by
    simp only [hF]; split_ifs
    · exact constructionWeight_nonneg M c u Ψ hΨ0 x a _
    · exact le_rfl
  have hsum : Summable F := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈2 * x⌉₊)
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    simp only [hF]
    split_ifs
    · apply weight_eq_zero_of_ge M c u Ψ hΨs x hx a
      exact le_trans hm (Nat.le_mul_of_pos_right m hn.pos)
    · rfl
  calc ∑ d ∈ s, constructionWeight M c u Ψ x a d = ∑ d ∈ s, F (d / n) := by
        apply Finset.sum_congr rfl
        intro d hd
        obtain ⟨hd2, hmin⟩ := hs d hd
        have hnd := hdvd d hd
        have hrough : IsRough g (d / n) := by
          refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hnd) hn.pos, fun q hq => ?_⟩
          rw [Nat.mem_primeFactors] at hq
          have hqd : q ∣ d := Nat.dvd_trans hq.2.1 (Nat.div_dvd_of_dvd hnd)
          have := Nat.minFac_le_of_dvd hq.1.two_le hqd
          rw [hmin] at this
          have : (n : ℝ) ≤ q := by exact_mod_cast this
          linarith
        simp only [hF, if_pos hrough, Nat.div_mul_cancel hnd]
    _ = ∑ m ∈ s.image (fun d => d / n), F m := (Finset.sum_image hinj).symm
    _ ≤ ∑' m, F m := hsum.sum_le_tsum _ (fun m _ => hF0 m)

open Classical in
/-- Every `x^b`-rough `d` is either `x^{1/2-κ}`-rough or has its least prime factor in one of
the bins `(x^{γ_j}, x^{γ_{j+1}}]` (§12.4). -/
lemma least_factor_decomp (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (x : ℝ) (hx : 1 < x) {K : ℕ} (a : Fin K → ℝ) (b κ : ℝ) (J : ℕ)
    (γ : ℕ → ℝ) (h0 : γ 0 = b) (hJ : γ J = 1 / 2 - κ) :
    ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) ≤
      ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d then constructionWeight M c u Ψ x a d else 0) +
      ∑ j ∈ Finset.range J,
        ∑ n ∈ (Finset.range (⌊x ^ γ (j + 1)⌋₊ + 1)).filter
            (fun n : ℕ => n.Prime ∧ x ^ γ j < n),
          ∑' m : ℕ, (if IsRough (x ^ γ j) m then
            constructionWeight M c u Ψ x a (m * n) else 0) := by
  have hx0 : 0 < x := by linarith
  rw [tsum_weight_eq_sum M c u Ψ hΨs x hx0 a, tsum_weight_eq_sum M c u Ψ hΨs x hx0 a]
  set N := ⌈2 * x⌉₊
  set w := constructionWeight M c u Ψ x a with hw
  have hw0 : ∀ d, 0 ≤ w d := constructionWeight_nonneg M c u Ψ hΨ0 x a
  set g : ℕ → ℕ → ℝ := fun j d =>
    if 2 ≤ d ∧ x ^ γ j < d.minFac ∧ (d.minFac : ℝ) ≤ x ^ γ (j + 1) then w d else 0 with hg
  have hg0 : ∀ j d, 0 ≤ g j d := fun j d => by
    simp only [hg]; split_ifs
    · exact hw0 d
    · exact le_rfl
  have step1 : ∑ d ∈ Finset.range N, (if IsRough (x ^ b) d then w d else 0) ≤
      ∑ d ∈ Finset.range N, ((if IsRough (x ^ (1 / 2 - κ)) d then w d else 0) +
        ∑ j ∈ Finset.range J, g j d) := by
    apply Finset.sum_le_sum
    intro d _
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range J, g j d := Finset.sum_nonneg fun j _ => hg0 j d
    by_cases hb : IsRough (x ^ b) d
    swap
    · rw [if_neg hb]
      have : 0 ≤ (if IsRough (x ^ (1 / 2 - κ)) d then w d else 0) := by
        split_ifs
        · exact hw0 d
        · exact le_rfl
      linarith
    rw [if_pos hb]
    by_cases hh : IsRough (x ^ (1 / 2 - κ)) d
    · rw [if_pos hh]; linarith
    rw [if_neg hh, zero_add]
    by_cases hwd : w d = 0
    · rw [hwd]; exact hsum0
    have hd2 := (constructionWeight_support M c u Ψ hΨs x hx0 a d hwd).1
    have hd1 : d ≠ 1 := by omega
    have hmp := Nat.minFac_prime hd1
    have hmin_mem : d.minFac ∈ d.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hmp, Nat.minFac_dvd d, by omega⟩
    have hlow : x ^ γ 0 < d.minFac := by rw [h0]; exact hb.2 _ hmin_mem
    have hhigh : (d.minFac : ℝ) ≤ x ^ γ J := by
      rw [hJ]
      simp only [IsRough, not_and, not_forall, not_lt] at hh
      obtain ⟨p, hp, hple⟩ := hh (by omega)
      have := Nat.minFac_le_of_dvd (Nat.mem_primeFactors.mp hp).1.two_le
        (Nat.mem_primeFactors.mp hp).2.1
      have : (d.minFac : ℝ) ≤ p := by exact_mod_cast this
      linarith
    obtain ⟨j, hj, h1, h2⟩ := exists_bin (fun j => x ^ γ j) d.minFac J hlow hhigh
    have hgj : g j d = w d := by
      simp only [hg]; rw [if_pos ⟨hd2, h1, h2⟩]
    rw [← hgj]
    exact Finset.single_le_sum (fun j _ => hg0 j d) (Finset.mem_range.mpr hj)
  refine le_trans step1 ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro j _
  set T := (Finset.range (⌊x ^ γ (j + 1)⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ j < n)
  set C : ℕ → Prop := fun d => 2 ≤ d ∧ x ^ γ j < d.minFac ∧ (d.minFac : ℝ) ≤ x ^ γ (j + 1)
  have hgsum : ∑ d ∈ Finset.range N, g j d = ∑ d ∈ (Finset.range N).filter C, w d := by
    rw [Finset.sum_filter]
  rw [hgsum]
  have hmaps : ∀ d ∈ (Finset.range N).filter C, d.minFac ∈ T := by
    intro d hd
    simp only [Finset.mem_filter, C] at hd
    obtain ⟨-, hd2, h1, h2⟩ := hd
    simp only [T, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor h2), Nat.minFac_prime (by omega), h1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro n hn
  simp only [T, Finset.mem_filter] at hn
  apply fiber_le M c u Ψ hΨs hΨ0 x hx0 a (x ^ γ j) n hn.2.1 hn.2.2
  intro d hd
  simp only [Finset.mem_filter, C] at hd
  exact ⟨hd.1.2.1, hd.2⟩

lemma partition_mono (γ : ℕ → ℝ) (J : ℕ) (hmono : ∀ j < J, γ j < γ (j + 1)) :
    ∀ i j, i ≤ j → j ≤ J → γ i ≤ γ j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact le_trans (ih (by omega)) (hmono j (by omega)).le

open Classical in
/-- (12.26). -/
theorem post_bin :
    ∃ C b₂ : ℝ, 0 < C ∧ 0 < b₂ ∧ b₂ ≤ 0.01 ∧
    ∀ (M c : ℕ) (u : ℤ), 0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → IsCoprime u M →
      (c : ℤ) ∣ u - 1 → IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
    ∀ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ Set.Ioo 1 2 →
      (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) → 0 < ∫ y, Ψ y →
    ∀ b : ℝ, 0 < b → b < b₂ → ∀ κ : ℝ, 0 < κ → κ < 0.01 →
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        singularSeries M * totalMass M c u Ψ x a / log x *
            (0.9 - exp (-eulerMascheroniConstant) / b * (C * exp (-(1 / 20) / b)) - η) ≤
          ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d then
            constructionWeight M c u Ψ x a d else 0) := by
  obtain ⟨hident, b₀, C_d, hb₀, hCd, hDb⟩ := rough_density
  obtain ⟨C_s, b₁, hCs, hb₁, hinit⟩ := initial_lower
  refine ⟨C_s + C_d, min (min b₀ b₁) 0.01, by positivity,
    lt_min (lt_min hb₀ hb₁) (by norm_num), min_le_right _ _, ?_⟩
  intro M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi b hb hbb κ hκ hκ'
  have hb0 : b < b₀ := lt_of_lt_of_le hbb (le_trans (min_le_left _ _) (min_le_left _ _))
  have hb1 : b < b₁ := lt_of_lt_of_le hbb (le_trans (min_le_left _ _) (min_le_right _ _))
  have hb01 : b < 0.01 := lt_of_lt_of_le hbb (min_le_right _ _)
  have hbκ : b < 1 / 2 - κ := by linarith
  obtain ⟨J, γ, S, h0, hJ, hmono, hS, hsum⟩ := density_partition b κ hb hκ hbκ
  have hpm := partition_mono γ J hmono
  have hbin : ∀ j : Fin J, ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∑ n ∈ (Finset.range (⌊x ^ γ (j + 1)⌋₊ + 1)).filter
            (fun n : ℕ => n.Prime ∧ x ^ γ j < n),
            ∑' m : ℕ, (if IsRough (x ^ γ j) m then
              constructionWeight M c u Ψ x a (m * n) else 0)
          ≤ singularSeries M * totalMass M c u Ψ x a / log x *
            (sSup ((fun t => roughDensity (γ j) (1 - t)) '' Set.Icc (γ j) (γ (j + 1))) *
              log (γ (j + 1) / γ j) + η) := fun j =>
    bin_cost M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi κ b (γ j) (γ (j + 1)) hκ hκ' hb
      hb01 (h0 ▸ hpm 0 j (Nat.zero_le _) j.2.le) (hmono j j.2)
      (hJ ▸ hpm (j + 1) J j.2 le_rfl)
  choose K₀ hK₀ using hbin
  refine ⟨Finset.univ.sup K₀, fun K hK1 hKK a ha ha' η hη => ?_⟩
  set η' := η / (J + 1) with hη'def
  have hη' : 0 < η' := by positivity
  have hbinx := fun j : Fin J =>
    hK₀ j K hK1 (le_trans (Finset.le_sup (Finset.mem_univ j)) hKK) a ha ha' η' hη'
  choose X hX using hbinx
  obtain ⟨x₁, hx₁⟩ := hinit M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi b hb hb1 K hK1 a
    ha ha' η' hη'
  refine ⟨max (max x₁ (∑ j, |X j|)) 2, fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX : ∀ j, X j ≤ x := fun j =>
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (X j))
      (Finset.mem_univ j)) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx))
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hL : 0 < log x := Real.log_pos (by linarith)
  set A := singularSeries M * totalMass M c u Ψ x a / log x with hA
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (singularSeries_pos M).le
    (totalMass_nonneg M c u Ψ hΨ0 x a)) hL.le
  set E := exp (-eulerMascheroniConstant) / b
  set e := exp (-(1 / 20) / b)
  -- the bins
  have hT : ∀ j : Fin J,
      ∑ n ∈ (Finset.range (⌊x ^ γ (j + 1)⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ j < n),
        ∑' m : ℕ, (if IsRough (x ^ γ j) m then constructionWeight M c u Ψ x a (m * n) else 0)
      ≤ A * (S j * log (γ (j + 1) / γ j) + η') := by
    intro j
    refine le_trans (hX j x (hxX j)) (mul_le_mul_of_nonneg_left ?_ hA0)
    refine add_le_add ?_ le_rfl
    have hγj : 0 < γ j := lt_of_lt_of_le hb (h0 ▸ hpm 0 j (Nat.zero_le _) j.2.le)
    have hlog : 0 ≤ log (γ (j + 1) / γ j) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hγj, one_mul]; exact (hmono j j.2).le
    apply mul_le_mul_of_nonneg_right _ hlog
    apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.mpr (hmono j j.2).le))
    rintro _ ⟨t, ht, rfl⟩
    exact hS j j.2 t ht
  have hTsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hT j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hTsum
  have hSsum : ∑ j : Fin J, S j * log (γ (j + 1) / γ j) ≤ E * (1 + C_d * e) - 0.9 := by
    have h1 : ∑ j : Fin J, S j * log (γ (j + 1) / γ j) =
        ∑ j ∈ Finset.range J, S j * log (γ (j + 1) / γ j) :=
      (Finset.sum_range (fun j => S j * log (γ (j + 1) / γ j))).symm
    have h2 := density_integral_le b κ hb hκ hbκ
    have h3 := hident b hb (by linarith)
    have h4 := hDb b hb hb0
    rw [h1]
    linarith
  have hdec := least_factor_decomp M c u Ψ hΨs hΨ0 x (by linarith) a b κ J γ h0 hJ
  rw [Finset.sum_range (fun j =>
      ∑ n ∈ (Finset.range (⌊x ^ γ (j + 1)⌋₊ + 1)).filter (fun n : ℕ => n.Prime ∧ x ^ γ j < n),
        ∑' m : ℕ, (if IsRough (x ^ γ j) m then
          constructionWeight M c u Ψ x a (m * n) else 0))] at hdec
  have hinit' := hx₁ x hx1
  have hbound : A * (∑ j : Fin J, S j * log (γ (j + 1) / γ j) + (J : ℝ) * η') ≤
      A * (E * (1 + C_d * e) - 0.9 + J * η') :=
    mul_le_mul_of_nonneg_left (by linarith) hA0
  have hid : A * (0.9 - E * ((C_s + C_d) * e) - η) =
      A * (E * (1 - C_s * e) - η') - A * (E * (1 + C_d * e) - 0.9 + J * η') := by
    rw [hη'def]; field_simp; ring
  rw [hid]
  linarith

lemma exists_small_b (C b₂ : ℝ) (hC : 0 < C) (hb₂ : 0 < b₂) :
    ∃ b : ℝ, 0 < b ∧ b < b₂ ∧
      exp (-eulerMascheroniConstant) / b * (C * exp (-(1 / 20) / b)) ≤ 0.2 := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hε : (0 : ℝ) < 0.01 / C := by positivity
  obtain ⟨s, hs1, hs2⟩ :=
    ((h.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop (1 / (20 * b₂) + 1))).exists
  have hs0 : 0 < s := by
    have : 0 < 1 / (20 * b₂) := by positivity
    linarith
  refine ⟨1 / (20 * s), by positivity, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 / (20 * b₂) < s := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  · have hγ : exp (-eulerMascheroniConstant) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [one_half_lt_eulerMascheroniConstant]
    have he : -(1 / 20 : ℝ) / (1 / (20 * s)) = -s := by field_simp
    rw [he]
    simp only [pow_one] at hs1
    rw [lt_div_iff₀ hC] at hs1
    have hE : 0 ≤ exp (-s) := (Real.exp_pos _).le
    have h1 : exp (-eulerMascheroniConstant) / (1 / (20 * s)) * (C * exp (-s)) =
        exp (-eulerMascheroniConstant) * (20 * (s * exp (-s) * C)) := by
      field_simp
    rw [h1]
    have h2 : 0 ≤ 20 * (s * exp (-s) * C) := by positivity
    calc exp (-eulerMascheroniConstant) * (20 * (s * exp (-s) * C))
        ≤ 1 * (20 * (s * exp (-s) * C)) := mul_le_mul_of_nonneg_right hγ h2
      _ ≤ 0.2 := by linarith

lemma marks_spec (K : ℕ) :
    StrictMono (fun i : Fin K => (0.1 : ℝ) + 0.1 * ((i : ℝ) + 1) / (K + 1)) ∧
      ∀ i : Fin K, (0.1 : ℝ) < 0.1 + 0.1 * ((i : ℝ) + 1) / (K + 1) ∧
        (0.1 : ℝ) + 0.1 * ((i : ℝ) + 1) / (K + 1) < 0.2 := by
  refine ⟨fun i j hij => ?_, fun i => ⟨?_, ?_⟩⟩
  · have : (i : ℝ) < j := by exact_mod_cast hij
    have hK : (0 : ℝ) < K + 1 := by positivity
    have := div_lt_div_of_pos_right (by linarith : 0.1 * ((i : ℝ) + 1) < 0.1 * ((j : ℝ) + 1)) hK
    linarith
  · have : 0 < 0.1 * ((i : ℝ) + 1) / (K + 1) := by positivity
    linarith
  · have hi : (i : ℝ) + 1 ≤ K := by exact_mod_cast i.2
    have hK : (0 : ℝ) < K + 1 := by positivity
    have : 0.1 * ((i : ℝ) + 1) / (K + 1) < 0.1 := by
      rw [div_lt_iff₀ hK]; nlinarith
    linarith

open Classical in
theorem prime_mass_lower (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M) (hc : c = 2 ∨ c = 4)
    (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1) (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c))
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ a : Fin K → ℝ, StrictMono a ∧ (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) ∧
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        singularSeries M * totalMass M c u Ψ x a / log x / 4 ≤
          ∑' d : ℕ, (if d.Prime then constructionWeight M c u Ψ x a d else 0) := by
  obtain ⟨C, b₂, hC, hb₂, -, hpost⟩ := post_bin
  obtain ⟨C₂, hC₂, hbal⟩ := balanced_cost M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  have hS := singularSeries_pos M
  set 𝔖 := singularSeries M with h𝔖
  set κ : ℝ := min (1 / 200) (𝔖 / (8 * C₂)) with hκ
  have hκ0 : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ1 : κ < 0.01 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hκC : C₂ * κ ≤ 𝔖 / 8 := by
    have := min_le_right (1 / 200 : ℝ) (𝔖 / (8 * C₂))
    rw [← hκ] at this
    calc C₂ * κ ≤ C₂ * (𝔖 / (8 * C₂)) := mul_le_mul_of_nonneg_left this hC₂.le
      _ = 𝔖 / 8 := by field_simp
  obtain ⟨b, hb0, hbb, hbE⟩ := exists_small_b C b₂ hC hb₂
  obtain ⟨K₁, hK₁⟩ := hpost M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi b hb0 hbb κ hκ0 hκ1
  obtain ⟨K₂, hK₂⟩ := hbal κ hκ0 hκ1
  set K := max (max K₁ K₂) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKK₁ : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKK₂ : K₂ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨ha, ha'⟩ := marks_spec K
  set a : Fin K → ℝ := fun i => (0.1 : ℝ) + 0.1 * ((i : ℝ) + 1) / (K + 1) with hadef
  refine ⟨K, hK1, a, ha, ha', ?_⟩
  obtain ⟨x₁, hx₁⟩ := hK₁ K hK1 hKK₁ a ha ha' 0.1 (by norm_num)
  obtain ⟨x₂, hx₂⟩ := hK₂ K hK1 hKK₂ a ha ha' (𝔖 / 100) (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop, 100 * C₂ / 𝔖 ≤ log x ∧ 0 < log x ∧ 0 < x :=
    (Real.tendsto_log_atTop.eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_gt_atTop 0).and (eventually_gt_atTop 0))
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max x₁ x₂) x₃, fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hLbig, hL0, hxpos⟩ := hx₃ x hx3
  have hU := hx₁ x hx1
  have hB := hx₂ x hx2
  set X := totalMass M c u Ψ x a / log x with hXdef
  have hX0 : 0 ≤ X := div_nonneg (totalMass_nonneg M c u Ψ hΨ0 x a) hL0.le
  -- U ≤ P + composites
  have hsplit : ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d then
        constructionWeight M c u Ψ x a d else 0) ≤
      ∑' d : ℕ, (if d.Prime then constructionWeight M c u Ψ x a d else 0) +
      ∑' d : ℕ, (if IsRough (x ^ (1 / 2 - κ)) d ∧ ¬ d.Prime then
            constructionWeight M c u Ψ x a d else 0) := by
    rw [← Summable.tsum_add (summable_weight M c u Ψ hΨs x hxpos a _)
      (summable_weight M c u Ψ hΨs x hxpos a _)]
    refine Summable.tsum_le_tsum (fun d => ?_) (summable_weight M c u Ψ hΨs x hxpos a _)
      ((summable_weight M c u Ψ hΨs x hxpos a _).add (summable_weight M c u Ψ hΨs x hxpos a _))
    have hw := constructionWeight_nonneg M c u Ψ hΨ0 x a d
    by_cases h1 : IsRough (x ^ (1 / 2 - κ)) d <;> by_cases h2 : d.Prime <;>
      simp only [h1, h2, if_true, if_false, not_true_eq_false, not_false_eq_true, and_true,
        and_false] <;> linarith
  have hC2L : C₂ * (1 / log x) ≤ 𝔖 / 100 := by
    rw [mul_one_div, div_le_iff₀ hL0]
    rw [div_le_iff₀ hS] at hLbig
    nlinarith
  have hfin : 𝔖 * X * (0.9 - 0.2 - 0.1) - (C₂ * (κ + 1 / log x) * X + 𝔖 / 100 * X) ≤
      ∑' d : ℕ, (if d.Prime then constructionWeight M c u Ψ x a d else 0) := by
    have hU' : 𝔖 * X * (0.9 - 0.2 - 0.1) ≤
        𝔖 * totalMass M c u Ψ x a / log x *
          (0.9 - exp (-eulerMascheroniConstant) / b * (C * exp (-(1 / 20) / b)) - 0.1) := by
      rw [mul_div_assoc, ← hXdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have h1 : C₂ * (κ + 1 / log x) * X ≤ (𝔖 / 8 + 𝔖 / 100) * X := by
    apply mul_le_mul_of_nonneg_right _ hX0
    linarith
  have h2 : 𝔖 * totalMass M c u Ψ x a / log x / 4 = 𝔖 * X / 4 := by
    rw [hXdef]; ring
  rw [h2]
  nlinarith

end ArtinPrimitiveRoots.P21controlled_predecessors


open ArtinPrimitiveRoots ArtinPrimitiveRoots.P21controlled_predecessors in
theorem solution (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M)
    (hc : c = 2 ∨ c = 4) (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1)
    (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c)) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      C * x / Real.log x ^ 2 ≤
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
          ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
            ∀ ℓ ∈ r.primeFactors, Real.exp (Real.log x ^ (0.1 : ℝ)) < ℓ ∧
              (ℓ : ℝ) < Real.exp (Real.log x ^ (0.3 : ℝ))} : ℝ) := by
  obtain ⟨Ψ, hΨ, hΨs, hΨ0, hΨ1, hΨi⟩ := exists_bump
  obtain ⟨K, hK, a, ha, ha', x₁, hx₁⟩ :=
    prime_mass_lower M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨B, hB, x₂, hx₂⟩ := count_from_mass M c u hM Ψ hΨs hΨ1 hΨ0 K hK a ha'
  obtain ⟨-, c₁, c₂, hc₁, hc₂, hwfd⟩ :=
    weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi
  obtain ⟨x₃, hx₃⟩ := hwfd c u hc hu hcu hcop K hK a ha ha'
  obtain ⟨CJ, hCJ⟩ := harmonic_mass M c u hM h8 hc hu hcu hcop Ψ hΨ hΨs hΨ0 hΨ1 hΨi K hK
  obtain ⟨x₄, hx₄⟩ := hCJ a ha ha' 1 one_pos
  have hS := singularSeries_pos M
  refine ⟨singularSeries M * c₁ / (4 * B), by positivity, max (max x₁ x₂) (max (max x₃ x₄) 3),
    fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx4 : x₄ ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx5 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hL : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hJ : 1 ≤ harmonicMass x a := (hx₄ x hx4).2.2.1
  have hX : c₁ * (x * harmonicMass x a / Real.log x) ≤ totalMass M c u Ψ x a := (hx₃ x hx3).1
  have hP := hx₁ x hx1
  have hN := hx₂ x hx2
  set N := (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
          ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
            ∀ ℓ ∈ r.primeFactors, Real.exp (Real.log x ^ (0.1 : ℝ)) < ℓ ∧
              (ℓ : ℝ) < Real.exp (Real.log x ^ (0.3 : ℝ))} : ℝ) with hNdef
  have hLpos : 0 < Real.log x := by linarith
  have hxpos : 0 < x := by linarith
  have h1 : c₁ * (x / Real.log x) ≤ totalMass M c u Ψ x a := by
    refine le_trans ?_ hX
    apply mul_le_mul_of_nonneg_left _ hc₁.le
    apply div_le_div_of_nonneg_right _ hLpos.le
    nlinarith
  have h2 : singularSeries M * (c₁ * (x / Real.log x)) / Real.log x / 4 ≤ B * N := by
    refine le_trans ?_ (le_trans hP hN)
    have := mul_le_mul_of_nonneg_left h1 hS.le
    have h3 := div_le_div_of_nonneg_right this hLpos.le
    linarith
  rw [div_le_iff₀ (by positivity)]
  have h4 : singularSeries M * c₁ / (4 * B) * x =
      (singularSeries M * (c₁ * (x / Real.log x)) / Real.log x / 4) / B * Real.log x ^ 2 := by
    field_simp
  rw [h4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_le_iff₀ hB]
  linarith
