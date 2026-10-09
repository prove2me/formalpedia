-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_pairs_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T12:14:10.762993+00:00
-- url     : https://prove2.me/submissions/9c8846da-ac14-4aaa-ac64-209f8d81e0db

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_block_sieve
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_weighted_family_distribution

namespace ArtinPrimitiveRoots.RoughPairs

open Real Finset Filter Topology

/-! ## A one-dimensional sieve for periodic conditions -/

/-- Residue classes in an interval. -/
lemma count_modEq_Ico (q : ℕ) (hq : 0 < q) (a b v : ℕ) (hab : a ≤ b) :
    |((#{n ∈ Ico a b | n ≡ v [MOD q]} : ℕ) : ℝ) - ((b : ℝ) - a) / q| ≤ 2 := by
  have h1 : (Ico a b).filter (fun n => n ≡ v [MOD q]) =
      ((range b).filter (fun n => n ≡ v [MOD q])) \ ((range a).filter (fun n => n ≡ v [MOD q])) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, fun h => by omega⟩
    · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨⟨by by_contra h; exact h4 ⟨by omega, h3⟩, h2⟩, h3⟩
  have hsub : ((range a).filter (fun n => n ≡ v [MOD q])) ⊆ ((range b).filter (fun n => n ≡ v [MOD q])) := by
    intro n; simp only [mem_filter, mem_range]; rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [h1, card_sdiff_of_subset hsub]
  have cb := Nat.count_modEq_card (b := b) hq v
  have ca := Nat.count_modEq_card (b := a) hq v
  rw [Nat.count_eq_card_filter_range] at cb ca
  rw [Nat.cast_sub (card_le_card hsub), cb, ca]
  have hb1 : ((b / q : ℕ) : ℝ) ≤ (b : ℝ) / q := Nat.cast_div_le
  have hb2 : (b : ℝ) / q - 1 ≤ ((b / q : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := b) hq
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : (b : ℝ) < ((b / q : ℕ) : ℝ) * q + q := by exact_mod_cast this
    linarith
  have ha1 : ((a / q : ℕ) : ℝ) ≤ (a : ℝ) / q := Nat.cast_div_le
  have ha2 : (a : ℝ) / q - 1 ≤ ((a / q : ℕ) : ℝ) := by
    have := Nat.lt_div_mul_add (a := a) hq
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    have : (a : ℝ) < ((a / q : ℕ) : ℝ) * q + q := by exact_mod_cast this
    linarith
  have e1 : ((if v % q < b % q then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> simp
  have e2 : (0 : ℝ) ≤ ((if v % q < b % q then 1 else 0 : ℕ) : ℝ) := by positivity
  have e3 : ((if v % q < a % q then 1 else 0 : ℕ) : ℝ) ≤ 1 := by split_ifs <;> simp
  have e4 : (0 : ℝ) ≤ ((if v % q < a % q then 1 else 0 : ℕ) : ℝ) := by positivity
  rw [sub_div, Nat.cast_add, Nat.cast_add]
  rw [abs_le]; constructor <;> linarith

/-- Periodic predicates in an interval. -/
lemma count_periodic_Ico (q : ℕ) (hq : 0 < q) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ n, P n ↔ P (n % q))
    (a b : ℕ) (hab : a ≤ b) :
    |((#{n ∈ Ico a b | P n} : ℕ) : ℝ) - #{t ∈ range q | P t} * (((b : ℝ) - a) / q)| ≤
      2 * #{t ∈ range q | P t} := by
  have hsplit : #{n ∈ Ico a b | P n} =
      ∑ t ∈ (range q).filter P, #{n ∈ Ico a b | n ≡ t [MOD q]} := by
    rw [card_eq_sum_card_fiberwise (f := fun n => n % q) (t := (range q).filter P)]
    · apply sum_congr rfl
      intro t ht
      simp only [mem_filter, mem_range] at ht
      congr 1; ext n
      simp only [mem_filter, Nat.ModEq, Nat.mod_eq_of_lt ht.1]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, (hP n).2 (h2 ▸ ht.2)⟩, h2⟩
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
      exact ⟨Nat.mod_lt _ hq, (hP n).1 hn.2⟩
  have e1 : (#{t ∈ range q | P t} : ℝ) * (((b : ℝ) - a) / q) =
      ∑ t ∈ (range q).filter P, ((b : ℝ) - a) / q := by rw [sum_const, nsmul_eq_mul]
  have e2 : 2 * (#{t ∈ range q | P t} : ℝ) = ∑ t ∈ (range q).filter P, (2 : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_comm]
  rw [hsplit, e1, e2, Nat.cast_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact sum_le_sum fun t _ => count_modEq_Ico q hq a b t hab

/-- Chinese remainder count for two coprime moduli. -/
lemma crt_count (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (co : Nat.Coprime a b)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (hP : ∀ n, P n ↔ P (n % a)) (hQ : ∀ n, Q n ↔ Q (n % b)) :
    #{t ∈ range (a * b) | P t ∧ Q t} = #{t ∈ range a | P t} * #{t ∈ range b | Q t} := by
  rw [← card_product]
  refine card_nbij' (fun t => (t % a, t % b))
    (fun uv => (Nat.chineseRemainder co uv.1 uv.2).1) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_product, Set.mem_prod] at ht ⊢
    exact ⟨⟨Nat.mod_lt _ ha, (hP t).1 ht.2.1⟩, ⟨Nat.mod_lt _ hb, (hQ t).1 ht.2.2⟩⟩
  · intro uv huv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, coe_product, Set.mem_prod] at huv ⊢
    have h := (Nat.chineseRemainder co uv.1 uv.2).2
    refine ⟨Nat.chineseRemainder_lt_mul co _ _ ha.ne' hb.ne', ?_, ?_⟩
    · rw [hP, h.1, Nat.mod_eq_of_lt huv.1.1]; exact huv.1.2
    · rw [hQ, h.2, Nat.mod_eq_of_lt huv.2.1]; exact huv.2.2
  · intro t ht
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ht
    have h := (Nat.chineseRemainder co (t % a) (t % b)).2
    have h1 : (Nat.chineseRemainder co (t % a) (t % b)).1 ≡ t [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul co).1 ⟨h.1.trans (Nat.mod_modEq t a),
        h.2.trans (Nat.mod_modEq t b)⟩
    have hlt := Nat.chineseRemainder_lt_mul co (t % a) (t % b) ha.ne' hb.ne'
    simp only
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt ht.1] at h1
  · intro uv huv
    simp only [coe_product, Set.mem_prod, coe_filter, mem_range, Set.mem_ofPred_eq] at huv
    have h := (Nat.chineseRemainder co uv.1 uv.2).2
    simp only [Nat.ModEq] at h
    show ((Nat.chineseRemainder co uv.1 uv.2).1 % a, (Nat.chineseRemainder co uv.1 uv.2).1 % b) = uv
    rw [h.1, h.2, Nat.mod_eq_of_lt huv.1.1, Nat.mod_eq_of_lt huv.2.1]

/-- Chinese remainder count for a base modulus and a set of primes. -/
lemma crt_count_prod (k : ℕ) (hk : 0 < k) (Pk : ℕ → Prop) [DecidablePred Pk]
    (hPk : ∀ n, Pk n ↔ Pk (n % k))
    (bad : ℕ → ℕ → Prop) [∀ j, DecidablePred (bad j)] (hbad : ∀ j n, bad j n ↔ bad j (n % j)) :
    ∀ S : Finset ℕ, (∀ j ∈ S, j.Prime ∧ Nat.Coprime j k) →
      (∀ n, (Pk n ∧ ∀ j ∈ S, bad j n) ↔ (Pk (n % (k * ∏ j ∈ S, j)) ∧
          ∀ j ∈ S, bad j (n % (k * ∏ j ∈ S, j)))) ∧
      #{t ∈ range (k * ∏ j ∈ S, j) | Pk t ∧ ∀ j ∈ S, bad j t} =
        #{t ∈ range k | Pk t} * ∏ j ∈ S, #{t ∈ range j | bad j t} := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    constructor
    · intro n; simp only [prod_empty, mul_one, notMem_empty, IsEmpty.forall_iff, implies_true,
        and_true]; exact hPk n
    · simp
  | insert j S hjS ih =>
    intro hS
    obtain ⟨ihp, ihc⟩ := ih (fun i hi => hS i (mem_insert_of_mem hi))
    have hj := hS j (mem_insert_self j S)
    have hpos : 0 < k * ∏ i ∈ S, i :=
      Nat.mul_pos hk (prod_pos fun i hi => (hS i (mem_insert_of_mem hi)).1.pos)
    have hco : Nat.Coprime (k * ∏ i ∈ S, i) j := by
      apply Nat.Coprime.mul_left hj.2.symm
      apply Nat.Coprime.prod_left
      intro i hi
      have hi' := (hS i (mem_insert_of_mem hi)).1
      rw [Nat.coprime_primes hi' hj.1]
      rintro rfl; exact hjS hi
    have hmod : k * ∏ i ∈ insert j S, i = (k * ∏ i ∈ S, i) * j := by
      rw [prod_insert hjS]; ring
    have key : ∀ n, (Pk n ∧ ∀ i ∈ insert j S, bad i n) ↔
        ((Pk n ∧ ∀ i ∈ S, bad i n) ∧ bad j n) := by
      intro n; simp only [mem_insert, forall_eq_or_imp]; tauto
    constructor
    · intro n
      rw [key, key, hmod]
      have e1 : n % ((k * ∏ i ∈ S, i) * j) % (k * ∏ i ∈ S, i) = n % (k * ∏ i ∈ S, i) :=
        Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)
      have e2 : n % ((k * ∏ i ∈ S, i) * j) % j = n % j :=
        Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)
      rw [ihp n, ihp (n % ((k * ∏ i ∈ S, i) * j)), e1, hbad j (n % ((k * ∏ i ∈ S, i) * j)), e2,
        ← hbad j n]
    · rw [hmod]
      have := crt_count (k * ∏ i ∈ S, i) j hpos hj.1.pos hco
        (fun n => Pk n ∧ ∀ i ∈ S, bad i n) (bad j) ihp (hbad j)
      rw [filter_congr (fun n _ => key n), this, ihc, prod_insert hjS]
      ring

/-- Reciprocal primes over a block `(v, v²]` are uniformly bounded. -/
lemma prime_block_sum : ∃ C : ℝ, ∀ v : ℝ, 1 < v →
    ∑ p ∈ (range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), (1 : ℝ) / p ≤ C := by
  have h := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hev := h.eventually (eventually_le_nhds (show log (2 / 1) < log (2 / 1) + 1 by linarith))
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  refine ⟨max (log (2 / 1) + 1) (∑ p ∈ range (⌊(max X 1) ^ 2⌋₊ + 1), (1 : ℝ) / p),
    fun v hv => ?_⟩
  by_cases hvX : X ≤ v
  · have := hX v hvX
    simp only [rpow_one, rpow_two] at this
    exact le_max_of_le_left this
  · apply le_max_of_le_right
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      have h1 : v ^ 2 ≤ (max X 1) ^ 2 := by
        have : v ≤ max X 1 := le_max_of_le_left (le_of_lt (not_le.1 hvX))
        exact pow_le_pow_left₀ (by linarith) this 2
      have := Nat.floor_mono h1
      omega
    · intro p _ _; positivity

/-- The conclusion of the one-dimensional upper-bound sieve, with constant `B`. -/
def SieveBound (B : ℝ) : Prop := ∀ (k : ℕ), 0 < k → ∀ (Pk : ℕ → Prop) [DecidablePred Pk],
    (∀ n, Pk n ↔ Pk (n % k)) → #{t ∈ range k | Pk t} ≤ 1 →
    ∀ (z : ℝ), 2 ≤ z → ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z ∧ Nat.Coprime p k) →
    ∀ (bad : ℕ → ℕ → Prop) [∀ j, DecidablePred (bad j)], (∀ j n, bad j n ↔ bad j (n % j)) →
    (∀ j ∈ Pset, #{t ∈ range j | bad j t} ≤ 2 ∧ 3 * #{t ∈ range j | bad j t} ≤ 2 * j) →
    ∀ Mr : ℝ, 0 ≤ Mr →
    (#{n ∈ Ico ⌈Mr⌉₊ ⌈2 * Mr⌉₊ | Pk n ∧ ∀ j ∈ Pset, ¬ bad j n} : ℝ) ≤
      B * ((Mr + 1) / k * ∏ j ∈ Pset, (1 - (#{t ∈ range j | bad j t} : ℝ) / j) +
        2 * z ^ 10 * (z ^ 10 + 1))


/-- A one-dimensional upper-bound sieve for periodic conditions on an interval, from the
block sieve. -/
theorem sieve1 : ∃ B : ℝ, 0 ≤ B ∧ SieveBound B := by
  obtain ⟨Cm, hCm⟩ := prime_block_sum
  obtain ⟨B, hB⟩ := (block_sieve.{0} (1 / 3) (2 * Cm) (by norm_num)).2
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro k hk Pk _ hPk hsk z hz Pset hP bad _ hbad hρ Mr hM
  have hab : ⌈Mr⌉₊ ≤ ⌈2 * Mr⌉₊ := Nat.ceil_mono (by linarith)
  have hba : ((⌈2 * Mr⌉₊ : ℕ) : ℝ) - ⌈Mr⌉₊ ≤ Mr + 1 := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ 2 * Mr by linarith)
    have h2 := Nat.le_ceil Mr
    linarith
  have hba0 : (0 : ℝ) ≤ ((⌈2 * Mr⌉₊ : ℕ) : ℝ) - ⌈Mr⌉₊ := by
    have : ((⌈Mr⌉₊ : ℕ) : ℝ) ≤ ⌈2 * Mr⌉₊ := by exact_mod_cast hab
    linarith
  generalize ⌈Mr⌉₊ = a at hab hba hba0 ⊢
  generalize ⌈2 * Mr⌉₊ = b at hab hba hba0 ⊢
  have hs1' : (#{t ∈ range k | Pk t} : ℝ) ≤ 1 := by exact_mod_cast hsk
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (#{t ∈ range k | Pk t} : ℝ) := ⟨_, rfl⟩
  have hs1 : s ≤ 1 := hs_def ▸ hs1'
  have hs0 : 0 ≤ s := hs_def ▸ Nat.cast_nonneg _
  let g : ℕ → ℝ := fun j => (#{t ∈ range j | bad j t} : ℝ) / j
  have hg : ∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - 1 / 3 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    refine ⟨div_nonneg (Nat.cast_nonneg _) hp0.le, ?_⟩
    show (#{t ∈ range p | bad p t} : ℝ) / p ≤ 1 - 1 / 3
    rw [div_le_iff₀ hp0]
    have : (3 * #{t ∈ range p | bad p t} : ℝ) ≤ 2 * p := by exact_mod_cast (hρ p hp).2
    linarith
  have hgp : ∀ p ∈ Pset, g p ≤ 2 / p := by
    intro p hp
    show (#{t ∈ range p | bad p t} : ℝ) / p ≤ 2 / p
    have : (#{t ∈ range p | bad p t} : ℝ) ≤ 2 := by exact_mod_cast (hρ p hp).1
    gcongr
  have hblock : ∀ v : ℝ, 1 < v →
      ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ 2 * Cm := by
    intro v hv
    calc ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p
        ≤ ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), 2 * ((1 : ℝ) / p) :=
          sum_le_sum fun p hp => by
            rw [mul_one_div]; exact hgp p (Finset.mem_filter.1 hp).1
      _ ≤ ∑ p ∈ (range (⌊v ^ 2⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v < p), 2 * ((1 : ℝ) / p) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
            refine ⟨?_, (hP p hp.1).1, hp.2.1⟩
            have := Nat.le_floor hp.2.2
            omega
          · intro p _ _; positivity
      _ ≤ 2 * Cm := by rw [← mul_sum]; linarith [hCm v hv]
  have hX : (0 : ℝ) ≤ s * (((b : ℝ) - a) / k) := by positivity
  have key := hB ((Ico a b).filter Pk) (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) z hz Pset
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) bad (s * (((b : ℝ) - a) / k)) hX g hg hblock
  simp only [sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter] at key
  -- error terms
  have hE : ∀ d ∈ (∏ p ∈ Pset, p).divisors,
      |(#{n ∈ Ico a b | Pk n ∧ ∀ p ∈ d.primeFactors, bad p n} : ℝ) -
        s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p| ≤ 2 * d := by
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    have hdv : d ∣ ∏ p ∈ Pset, p := Nat.dvd_of_mem_divisors hd
    have hS : ∀ j ∈ d.primeFactors, j.Prime ∧ Nat.Coprime j k := by
      intro j hj
      have hjp := Nat.prime_of_mem_primeFactors hj
      have hjd := Nat.dvd_of_mem_primeFactors hj
      obtain ⟨i, hi, hji⟩ := (Prime.dvd_finsetProd_iff hjp.prime _).1 (hjd.trans hdv)
      have : j = i := (Nat.prime_dvd_prime_iff_eq hjp (hP i hi).1).1 hji
      subst this
      exact ⟨hjp, (hP j hi).2.2⟩
    have hSsub : ∀ j ∈ d.primeFactors, j ∈ Pset ∧ j.Prime := by
      intro j hj
      have hjp := Nat.prime_of_mem_primeFactors hj
      have hjd := Nat.dvd_of_mem_primeFactors hj
      obtain ⟨i, hi, hji⟩ := (Prime.dvd_finsetProd_iff hjp.prime _).1 (hjd.trans hdv)
      have : j = i := (Nat.prime_dvd_prime_iff_eq hjp (hP i hi).1).1 hji
      subst this; exact ⟨hi, hjp⟩
    obtain ⟨hper, hcnt⟩ := crt_count_prod k hk Pk hPk bad hbad d.primeFactors hS
    have hq : 0 < k * ∏ j ∈ d.primeFactors, j :=
      Nat.mul_pos hk (prod_pos fun j hj => (hS j hj).1.pos)
    have hc := count_periodic_Ico (k * ∏ j ∈ d.primeFactors, j) hq
      (fun n => Pk n ∧ ∀ j ∈ d.primeFactors, bad j n) hper a b hab
    rw [hcnt] at hc
    have hmain : s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p =
        ((#{t ∈ range k | Pk t} * ∏ j ∈ d.primeFactors, #{t ∈ range j | bad j t} : ℕ) : ℝ) *
          (((b : ℝ) - a) / ((k * ∏ j ∈ d.primeFactors, j : ℕ) : ℝ)) := by
      rw [hs_def]
      simp only [g]
      rw [prod_div_distrib, Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
      ring
    rw [hmain]
    refine hc.trans ?_
    have h1 : ((#{t ∈ range k | Pk t} * ∏ j ∈ d.primeFactors, #{t ∈ range j | bad j t} : ℕ) : ℝ)
        ≤ ∏ j ∈ d.primeFactors, (j : ℝ) := by
      push_cast
      calc (#{t ∈ range k | Pk t} : ℝ) * ∏ j ∈ d.primeFactors, (#{t ∈ range j | bad j t} : ℝ)
          ≤ 1 * ∏ j ∈ d.primeFactors, (j : ℝ) := by
            apply mul_le_mul hs1' _ (prod_nonneg fun _ _ => Nat.cast_nonneg _) zero_le_one
            apply prod_le_prod (fun _ _ => Nat.cast_nonneg _)
            intro j hj
            have h2 : (#{t ∈ range j | bad j t} : ℝ) ≤ 2 := by
              exact_mod_cast (hρ j (hSsub j hj).1).1
            have h3 : (2 : ℝ) ≤ j := by exact_mod_cast (hSsub j hj).2.two_le
            linarith
        _ = _ := one_mul _
    have h2 : ∏ j ∈ d.primeFactors, (j : ℝ) ≤ d := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Nat.prod_primeFactors_dvd d)
      rw [← Nat.cast_prod]; exact_mod_cast this
    linarith
  have hEsum : ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
      |(#{n ∈ Ico a b | Pk n ∧ ∀ p ∈ d.primeFactors, bad p n} : ℝ) -
        s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p| ≤ 2 * z ^ 10 * (z ^ 10 + 1) := by
    calc _ ≤ ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
          2 * z ^ 10 := by
          apply sum_le_sum
          intro d hd
          rw [Finset.mem_filter] at hd
          exact (hE d hd.1).trans (by linarith [hd.2])
      _ = #((∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ))) *
            (2 * z ^ 10) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (z ^ 10 + 1) * (2 * z ^ 10) := by
          gcongr
          have hsub : (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)) ⊆
              range (⌊z ^ 10⌋₊ + 1) := by
            intro d hd
            rw [Finset.mem_filter] at hd
            rw [Finset.mem_range]
            have := Nat.le_floor hd.2
            omega
          have := card_le_card hsub
          rw [card_range] at this
          have h2 : ((⌊z ^ 10⌋₊ : ℕ) : ℝ) ≤ z ^ 10 := Nat.floor_le (by positivity)
          have : (#((∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ))) : ℝ)
              ≤ ((⌊z ^ 10⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this
          linarith
      _ = 2 * z ^ 10 * (z ^ 10 + 1) := by ring
  have hprod0 : 0 ≤ ∏ j ∈ Pset, (1 - g j) :=
    prod_nonneg fun j hj => by linarith [(hg j hj).2]
  have hmainle : s * (((b : ℝ) - a) / k) * ∏ j ∈ Pset, (1 - g j) ≤
      (Mr + 1) / k * ∏ j ∈ Pset, (1 - g j) := by
    apply mul_le_mul_of_nonneg_right _ hprod0
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    calc s * (((b : ℝ) - a) / k) ≤ 1 * ((Mr + 1) / k) := by
          apply mul_le_mul hs1 (by gcongr) (by positivity) zero_le_one
      _ = _ := one_mul _
  have hfin : (#{n ∈ Ico a b | Pk n ∧ ∀ j ∈ Pset, ¬ bad j n} : ℝ) ≤
      B * (s * (((b : ℝ) - a) / k) * ∏ j ∈ Pset, (1 - g j) +
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
          |(#{n ∈ Ico a b | Pk n ∧ ∀ p ∈ d.primeFactors, bad p n} : ℝ) -
            s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p|) := by
    convert key <;> rfl
  have hY0 : 0 ≤ s * (((b : ℝ) - a) / k) * ∏ j ∈ Pset, (1 - g j) +
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
          |(#{n ∈ Ico a b | Pk n ∧ ∀ p ∈ d.primeFactors, bad p n} : ℝ) -
            s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p| :=
    add_nonneg (by positivity) (sum_nonneg fun _ _ => abs_nonneg _)
  calc _ ≤ _ := hfin
    _ ≤ max B 0 * (s * (((b : ℝ) - a) / k) * ∏ j ∈ Pset, (1 - g j) +
        ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)),
          |(#{n ∈ Ico a b | Pk n ∧ ∀ p ∈ d.primeFactors, bad p n} : ℝ) -
            s * (((b : ℝ) - a) / k) * ∏ p ∈ d.primeFactors, g p|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hY0
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact add_le_add hmainle hEsum

/-! ## The Euler factor `∏_{p ∣ n} (1 - 1/p)` -/

/-- `Rf n = ∏_{p ∣ n} (1 - 1/p) = φ(n)/n`. -/
noncomputable def Rf (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))

lemma one_sub_inv_mem {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  refine ⟨?_, ?_⟩
  · rw [sub_pos, div_lt_one (by linarith)]; linarith
  · have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith

lemma Rf_pos (n : ℕ) : 0 < Rf n :=
  prod_pos fun _ hp => (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hp)).1

lemma Rf_mul_ge (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : Rf a * Rf b ≤ Rf (a * b) := by
  unfold Rf
  rw [Nat.primeFactors_mul ha hb, ← union_sdiff_self_eq_union,
    prod_union disjoint_sdiff]
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun p hp =>
    (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hp)).1.le)
  apply prod_le_prod_of_subset_of_le_one sdiff_subset
  · intro p hp; exact (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hp)).1.le
  · intro p hp _; exact (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hp)).2

lemma Rf_two_or_four (c : ℕ) (hc : c = 2 ∨ c = 4) : Rf c = 1 / 2 := by
  have h2 : Nat.primeFactors c = {2} := by
    rcases hc with rfl | rfl
    · exact Nat.Prime.primeFactors Nat.prime_two
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  unfold Rf; rw [h2]; norm_num

lemma Rf_ge_half (n : ℕ) (hn : 0 < n) (T : ℝ) (hT : 1 < T) (hp : ∀ p ∈ n.primeFactors, T ≤ p)
    (hlog : 2 * log n ≤ T * log T) : 1 / 2 ≤ Rf n := by
  set N := #n.primeFactors with hN
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < log T := log_pos hT
  have h1 : T ^ N ≤ n := by
    calc T ^ N = ∏ _p ∈ n.primeFactors, T := by rw [prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) := Finset.prod_le_prod (fun _ _ => hT0.le) hp
      _ ≤ n := by
          have := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
          rw [← Nat.cast_prod]; exact_mod_cast this
  have h2 : N * log T ≤ log n := by
    rw [← log_pow]; exact log_le_log (by positivity) h1
  have h3 : (N : ℝ) ≤ T / 2 := by
    have : 2 * (N * log T) ≤ T * log T := by linarith
    have : 2 * N ≤ T := by nlinarith
    linarith
  have h4 : (1 - 1 / T) ^ N ≤ Rf n := by
    calc (1 - 1 / T) ^ N = ∏ _p ∈ n.primeFactors, (1 - 1 / T) := by rw [prod_const]
      _ ≤ Rf n := by
          apply Finset.prod_le_prod
          · intro _ _
            rw [sub_nonneg, div_le_one hT0]; exact hT.le
          · intro p hpn
            have := hp p hpn
            have : 1 / (p : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT0 this
            linarith
  have h5 : 1 + (N : ℝ) * (-(1 / T)) ≤ (1 + -(1 / T)) ^ N := by
    apply one_add_mul_le_pow
    have : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT.le
    linarith
  have h6 : (N : ℝ) * (1 / T) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hT0]; linarith
  have : (1 + -(1 / T)) = 1 - 1 / T := by ring
  rw [this] at h5
  linarith

lemma mertensProduct_le_one (y : ℝ) : mertensProduct y ≤ 1 := by
  unfold mertensProduct
  apply prod_le_one
  · intro p hp; exact (one_sub_inv_mem (Finset.mem_filter.1 hp).2).1.le
  · intro p hp; exact (one_sub_inv_mem (Finset.mem_filter.1 hp).2).2

lemma mertensProduct_nonneg (y : ℝ) : 0 ≤ mertensProduct y := by
  unfold mertensProduct
  exact prod_nonneg fun p hp => (one_sub_inv_mem (Finset.mem_filter.1 hp).2).1.le

/-! ## The sieve products -/

lemma prod_sieve_le (W z : ℝ) (hW : 0 ≤ W) (hWz : W ≤ z) (q : ℕ) (hq : q ≠ 0) (ρ : ℕ → ℝ)
    (hρ : ∀ j ∈ (range (⌊z⌋₊ + 1)).filter (fun j => j.Prime ∧ ¬ j ∣ q),
      (1 + if (j : ℝ) ≤ W then 1 else 0) ≤ ρ j ∧ ρ j ≤ j) :
    ∏ j ∈ (range (⌊z⌋₊ + 1)).filter (fun j => j.Prime ∧ ¬ j ∣ q), (1 - ρ j / j) ≤
      mertensProduct W * mertensProduct z / Rf q ^ 2 := by
  classical
  set Pall := (range (⌊z⌋₊ + 1)).filter Nat.Prime with hPall
  let f : ℕ → ℝ := fun j => (1 - 1 / (j : ℝ)) * (if (j : ℝ) ≤ W then (1 - 1 / (j : ℝ)) else 1)
  have hPset : (range (⌊z⌋₊ + 1)).filter (fun j => j.Prime ∧ ¬ j ∣ q) =
      Pall.filter (fun j => ¬ j ∣ q) := by rw [hPall, filter_filter]
  have hf_pos : ∀ j ∈ Pall, 0 < f j := by
    intro j hj
    have h := one_sub_inv_mem (Finset.mem_filter.1 hj).2
    apply mul_pos h.1
    split_ifs <;> linarith [h.1]
  have hf_ge : ∀ j ∈ Pall, (1 - 1 / (j : ℝ)) ^ 2 ≤ f j := by
    intro j hj
    have h := one_sub_inv_mem (Finset.mem_filter.1 hj).2
    simp only [f]
    rw [sq]
    apply mul_le_mul_of_nonneg_left _ h.1.le
    split_ifs
    · exact le_rfl
    · exact h.2
  -- step a
  have ha : ∏ j ∈ (range (⌊z⌋₊ + 1)).filter (fun j => j.Prime ∧ ¬ j ∣ q), (1 - ρ j / j) ≤
      ∏ j ∈ Pall.filter (fun j => ¬ j ∣ q), f j := by
    rw [← hPset]
    apply Finset.prod_le_prod
    · intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_filter.1 hj).2.1.pos
      rw [sub_nonneg, div_le_one hj0]; exact (hρ j hj).2
    · intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_filter.1 hj).2.1.pos
      have hρj := (hρ j hj).1
      simp only [f]
      split_ifs at hρj ⊢ with hW'
      · have : 2 / (j : ℝ) ≤ ρ j / j := div_le_div_of_nonneg_right (by linarith) hj0.le
        have e : (1 - 1 / (j : ℝ)) * (1 - 1 / (j : ℝ)) = 1 - 2 / j + 1 / j ^ 2 := by
          field_simp; ring
        rw [e]
        have : (0 : ℝ) ≤ 1 / j ^ 2 := by positivity
        linarith
      · have : 1 / (j : ℝ) ≤ ρ j / j := div_le_div_of_nonneg_right (by linarith) hj0.le
        linarith
  -- step b, c
  have hc : ∏ j ∈ Pall, f j = mertensProduct z * mertensProduct W := by
    simp only [f]
    rw [prod_mul_distrib, ← prod_filter]
    congr 1
    unfold mertensProduct
    congr 1
    ext j
    simp only [hPall, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hp⟩, hjW⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hjW), hp⟩
    · rintro ⟨hj, hp⟩
      have hjW : (j : ℝ) ≤ W := (Nat.le_floor_iff hW).1 (Nat.lt_succ_iff.1 hj)
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor (hjW.trans hWz)), hp⟩, hjW⟩
  have hb := prod_filter_not_mul_prod_filter Pall (fun j => j ∣ q) f
  -- step d
  have hd : Rf q ^ 2 ≤ ∏ j ∈ Pall.filter (fun j => j ∣ q), f j := by
    calc Rf q ^ 2 ≤ (∏ j ∈ Pall.filter (fun j => j ∣ q), (1 - 1 / (j : ℝ))) ^ 2 := by
          apply pow_le_pow_left₀ (Rf_pos q).le
          apply prod_le_prod_of_subset_of_le_one
          · intro j hj
            rw [Finset.mem_filter] at hj
            exact Nat.mem_primeFactors.2 ⟨(Finset.mem_filter.1 hj.1).2, hj.2, hq⟩
          · intro j hj; exact (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hj)).1.le
          · intro j hj _; exact (one_sub_inv_mem (Nat.prime_of_mem_primeFactors hj)).2
      _ = ∏ j ∈ Pall.filter (fun j => j ∣ q), (1 - 1 / (j : ℝ)) ^ 2 := by rw [prod_pow]
      _ ≤ _ := Finset.prod_le_prod (fun j _ => sq_nonneg _)
          (fun j hj => hf_ge j (Finset.mem_filter.1 hj).1)
  have hpos : 0 < ∏ j ∈ Pall.filter (fun j => j ∣ q), f j :=
    prod_pos fun j hj => hf_pos j (Finset.mem_filter.1 hj).1
  have hRpos : 0 < Rf q ^ 2 := by have := Rf_pos q; positivity
  refine ha.trans ?_
  have heq : ∏ j ∈ Pall.filter (fun j => ¬ j ∣ q), f j =
      mertensProduct z * mertensProduct W / ∏ j ∈ Pall.filter (fun j => j ∣ q), f j := by
    rw [eq_div_iff hpos.ne', hb, hc]
  rw [heq, mul_comm (mertensProduct z)]
  apply div_le_div_of_nonneg_left _ hRpos hd
  exact mul_nonneg (mertensProduct_nonneg _) (mertensProduct_nonneg _)

lemma inv_unique (k m t t' : ℕ) (ht : t < k) (ht' : t' < k) (h1 : m * t % k = 1 % k)
    (h2 : m * t' % k = 1 % k) : t = t' := by
  have hco : Nat.Coprime m k := Nat.coprime_of_mul_modEq_one t h1
  have h : m * t ≡ m * t' [MOD k] := h1.trans h2.symm
  have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hco) h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at this

lemma card_inv_le (k m : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ t, P t ↔ m * t % k = 1 % k) : #{t ∈ range k | P t} ≤ 1 := by
  apply card_le_one.2
  intro t ht t' ht'
  rw [Finset.mem_filter, Finset.mem_range, hP] at ht ht'
  exact inv_unique k m t t' ht.1 ht'.1 ht.2 ht'.2

open Classical in
lemma n_count (B : ℝ) (hB0 : 0 ≤ B) (hB : SieveBound B) (W z Q0 : ℝ) (hW : 0 ≤ W)
    (hWz : W ≤ z) (hz : 2 ≤ z) (hzQ : z ≤ Q0) (k m : ℕ) (hk : 0 < k) (hk2 : 2 ∣ k) (hm : 0 < m)
    (M2 : ℝ) (hM2 : 0 ≤ M2) :
    (#{n ∈ Ico ⌈M2⌉₊ ⌈2 * M2⌉₊ | IsRough W n ∧ ∃ Q : ℕ, Q.Prime ∧ Q0 < Q ∧ m * n = k * Q + 1} : ℝ)
      ≤ B * ((M2 + 1) / k * (mertensProduct W * mertensProduct z / Rf (k * m) ^ 2) +
        2 * z ^ 10 * (z ^ 10 + 1)) := by
  have hkm : k * m ≠ 0 := (Nat.mul_pos hk hm).ne'
  set Pset := (range (⌊z⌋₊ + 1)).filter (fun j => j.Prime ∧ ¬ j ∣ k * m) with hPset_def
  have hPmem : ∀ j ∈ Pset, j.Prime ∧ ¬ j ∣ k * m ∧ (j : ℝ) ≤ z := by
    intro j hj
    rw [hPset_def, Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨hj.2.1, hj.2.2, ?_⟩
    exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 hj.1)).trans (Nat.floor_le (by linarith))
  have hj3 : ∀ j ∈ Pset, 3 ≤ j := by
    intro j hj
    obtain ⟨hp, hnd, _⟩ := hPmem j hj
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd (h ▸ dvd_mul_of_dvd_left hk2 m) hnd
    · have := hp.two_le
      rcases Nat.lt_or_ge j 3 with h3 | h3
      · interval_cases j; exact absurd h (by decide)
      · exact h3
  have hjm : ∀ j ∈ Pset, Nat.Coprime m j := by
    intro j hj
    obtain ⟨hp, hnd, _⟩ := hPmem j hj
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hnd (dvd_mul_of_dvd_right h k)).symm
  have key := hB k hk (fun n => m * n % k = 1 % k)
    (fun n => by rw [Nat.mul_mod m (n % k), Nat.mod_mod, ← Nat.mul_mod])
    (card_inv_le k m _ (fun t => Iff.rfl)) z hz Pset
    (fun p hp => ⟨(hPmem p hp).1, (hPmem p hp).2.2,
      (Nat.Prime.coprime_iff_not_dvd (hPmem p hp).1).2
        fun h => (hPmem p hp).2.1 (dvd_mul_of_dvd_left h m)⟩)
    (fun j n => m * n % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ n % j = 0))
    (fun j n => by rw [Nat.mul_mod m (n % j), Nat.mod_mod, ← Nat.mul_mod])
    (fun j hj => by
      have hle : #{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)} ≤ 2 := by
        calc #{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)}
            ≤ #({t ∈ range j | m * t % j = 1 % j} ∪ {0}) := by
              apply card_le_card
              intro t ht
              rw [Finset.mem_filter] at ht
              rw [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
              rcases ht.2 with h | h
              · exact Or.inl ⟨ht.1, h⟩
              · right
                have := Finset.mem_range.1 ht.1
                rw [Nat.mod_eq_of_lt this] at h; exact h.2
          _ ≤ #{t ∈ range j | m * t % j = 1 % j} + #({0} : Finset ℕ) := card_union_le _ _
          _ ≤ 1 + 1 := by
              rw [card_singleton]
              exact Nat.add_le_add_right (card_inv_le j m _ (fun t => Iff.rfl)) 1
      refine ⟨hle, ?_⟩
      have := hj3 j hj
      omega)
    M2 hM2
  -- lower bounds for the number of bad residues
  have hρ : ∀ j ∈ Pset,
      (1 + if (j : ℝ) ≤ W then 1 else 0) ≤
        ((#{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)} : ℕ) : ℝ) ∧
      ((#{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)} : ℕ) : ℝ) ≤ j := by
    intro j hj
    have hj1 : 1 < j := (hPmem j hj).1.one_lt
    obtain ⟨t0, ht0, ht0e⟩ := Nat.exists_mul_mod_eq_one_of_coprime (hjm j hj) hj1
    have h1j : 1 % j = 1 := Nat.mod_eq_of_lt hj1
    constructor
    · split_ifs with hW'
      · have hsub : ({t0, 0} : Finset ℕ) ⊆
            (range j).filter (fun t => m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)) := by
          intro t ht
          rw [Finset.mem_insert, Finset.mem_singleton] at ht
          rw [Finset.mem_filter, Finset.mem_range]
          rcases ht with rfl | rfl
          · exact ⟨ht0, Or.inl (by rw [ht0e, h1j])⟩
          · exact ⟨by omega, Or.inr ⟨hW', Nat.zero_mod _⟩⟩
        have hne : t0 ≠ 0 := by rintro rfl; simp at ht0e
        have := card_le_card hsub
        rw [card_pair hne] at this
        have : (2 : ℝ) ≤ ((#{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)} : ℕ) : ℝ) := by
          exact_mod_cast this
        linarith
      · have hsub : ({t0} : Finset ℕ) ⊆
            (range j).filter (fun t => m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)) := by
          intro t ht
          rw [Finset.mem_singleton] at ht
          rw [Finset.mem_filter, Finset.mem_range, ht]
          exact ⟨ht0, Or.inl (by rw [ht0e, h1j])⟩
        have := card_le_card hsub
        rw [card_singleton] at this
        have : (1 : ℝ) ≤ ((#{t ∈ range j | m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0)} : ℕ) : ℝ) := by
          exact_mod_cast this
        linarith
    · have := card_filter_le (range j) (fun t => m * t % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ t % j = 0))
      rw [card_range] at this
      exact_mod_cast this
  have hprod := prod_sieve_le W z hW hWz (k * m) hkm _ hρ
  -- the target set is inside the sieved set
  have hsub : (Ico ⌈M2⌉₊ ⌈2 * M2⌉₊).filter
      (fun n => IsRough W n ∧ ∃ Q : ℕ, Q.Prime ∧ Q0 < Q ∧ m * n = k * Q + 1) ⊆
      (Ico ⌈M2⌉₊ ⌈2 * M2⌉₊).filter (fun n => m * n % k = 1 % k ∧
        ∀ j ∈ Pset, ¬ (m * n % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ n % j = 0))) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnI, hR, Q, hQ, hQ0, hQe⟩ := hn
    refine ⟨hnI, by rw [hQe, Nat.mul_add_mod], fun j hj hbad => ?_⟩
    obtain ⟨hjp, hjnd, hjz⟩ := hPmem j hj
    rcases hbad with h | ⟨hjW, h0⟩
    · rw [hQe] at h
      have h' : k * Q + 1 ≡ 0 + 1 [MOD j] := by simpa [Nat.ModEq] using h
      have h'' := Nat.ModEq.add_right_cancel' 1 h'
      have hdvd : j ∣ k * Q := (Nat.modEq_zero_iff_dvd).1 h''
      rcases (Nat.Prime.dvd_mul hjp).1 hdvd with h1 | h1
      · exact hjnd (dvd_mul_of_dvd_left h1 m)
      · have := (Nat.prime_dvd_prime_iff_eq hjp hQ).1 h1
        subst this
        linarith
    · have hjn : j ∈ n.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hjp, Nat.dvd_of_mod_eq_zero h0, hR.1.ne'⟩
      have := hR.2 j hjn
      linarith
  have hcard := card_le_card hsub
  have hcardR : ((#((Ico ⌈M2⌉₊ ⌈2 * M2⌉₊).filter
      (fun n => IsRough W n ∧ ∃ Q : ℕ, Q.Prime ∧ Q0 < Q ∧ m * n = k * Q + 1)) : ℕ) : ℝ) ≤
      ((#((Ico ⌈M2⌉₊ ⌈2 * M2⌉₊).filter (fun n => m * n % k = 1 % k ∧
        ∀ j ∈ Pset, ¬ (m * n % j = 1 % j ∨ ((j : ℝ) ≤ W ∧ n % j = 0)))) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans (key.trans ?_)
  apply mul_le_mul_of_nonneg_left _ hB0
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left hprod
  positivity

open Classical in
lemma m_count (B : ℝ) (_hB0 : 0 ≤ B) (hB : SieveBound B) (W : ℝ) (hW : 2 ≤ W) (M1 : ℝ)
    (hM1 : 0 ≤ M1) :
    (#{m ∈ Ico ⌈M1⌉₊ ⌈2 * M1⌉₊ | IsRough W m} : ℝ) ≤
      B * ((M1 + 1) * mertensProduct W + 2 * W ^ 10 * (W ^ 10 + 1)) := by
  set Pset := (range (⌊W⌋₊ + 1)).filter Nat.Prime with hPset_def
  have hPmem : ∀ j ∈ Pset, j.Prime ∧ (j : ℝ) ≤ W := by
    intro j hj
    rw [hPset_def, Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨hj.2, (Nat.cast_le.2 (Nat.lt_succ_iff.1 hj.1)).trans (Nat.floor_le (by linarith))⟩
  have hρ1 : ∀ j ∈ Pset, #{t ∈ range j | t % j = 0} = 1 := by
    intro j hj
    rw [card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; rwa [Nat.mod_eq_of_lt h1] at h2
    · rintro rfl; exact ⟨(hPmem j hj).1.pos, Nat.zero_mod _⟩
  have key := hB 1 one_pos (fun _ => True) (fun _ => Iff.rfl)
    (by
      apply card_le_one.2
      intro t ht t' ht'
      rw [Finset.mem_filter, Finset.mem_range] at ht ht'
      omega) W hW Pset
    (fun p hp => ⟨(hPmem p hp).1, (hPmem p hp).2, Nat.coprime_one_right _⟩)
    (fun j n => n % j = 0) (fun j n => by simp only [Nat.mod_mod])
    (fun j hj => by
      rw [hρ1 j hj]
      have := (hPmem j hj).1.two_le
      omega)
    M1 hM1
  have hprod : ∏ j ∈ Pset, (1 - ((#{t ∈ range j | t % j = 0} : ℕ) : ℝ) / j) = mertensProduct W := by
    unfold mertensProduct
    apply prod_congr rfl
    intro j hj
    rw [hρ1 j hj]; simp
  have hsub : (Ico ⌈M1⌉₊ ⌈2 * M1⌉₊).filter (fun m => IsRough W m) ⊆
      (Ico ⌈M1⌉₊ ⌈2 * M1⌉₊).filter (fun m => True ∧ ∀ j ∈ Pset, ¬ m % j = 0) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, trivial, fun j hj h0 => ?_⟩
    have hjn : j ∈ m.primeFactors :=
      Nat.mem_primeFactors.2 ⟨(hPmem j hj).1, Nat.dvd_of_mod_eq_zero h0, hm.2.1.ne'⟩
    have := hm.2.2 j hjn
    linarith [(hPmem j hj).2]
  have hcard : ((#((Ico ⌈M1⌉₊ ⌈2 * M1⌉₊).filter (fun m => IsRough W m)) : ℕ) : ℝ) ≤
      ((#((Ico ⌈M1⌉₊ ⌈2 * M1⌉₊).filter (fun m => True ∧ ∀ j ∈ Pset, ¬ m % j = 0)) : ℕ) : ℝ) := by
    exact_mod_cast card_le_card hsub
  refine hcard.trans (key.trans (le_of_eq ?_))
  rw [hprod, Nat.cast_one, div_one]

lemma box_sub (M : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (range ⌈2 * M⌉₊).filter (fun n : ℕ => M ≤ n ∧ (n : ℝ) < 2 * M ∧ P n) ⊆
      (Ico ⌈M⌉₊ ⌈2 * M⌉₊).filter P := by
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
  exact ⟨⟨Nat.ceil_le.2 hn.2.1, hn.1⟩, hn.2.2.2⟩

/-! ## Mertens bounds and asymptotics -/

lemma mertens_bounds : ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ y, y₀ ≤ y →
    1 / (2 * log y) ≤ mertensProduct y ∧ mertensProduct y ≤ 1 / log y := by
  have h := mertens_product
  have hlt1 : exp (-eulerMascheroniConstant) < 1 :=
    Real.exp_lt_one_iff.2 (by linarith [one_half_lt_eulerMascheroniConstant])
  have hgt : 1 / 2 < exp (-eulerMascheroniConstant) := by
    have h23 : (2 : ℝ) / 3 < log 2 := by linarith [log_two_gt_d9]
    have : exp (2 / 3) < 2 := by
      calc exp (2 / 3) < exp (log 2) := exp_lt_exp.2 h23
        _ = 2 := exp_log (by norm_num)
    have h3 : exp (-(2 / 3)) < exp (-eulerMascheroniConstant) :=
      exp_lt_exp.2 (by linarith [eulerMascheroniConstant_lt_two_thirds])
    rw [exp_neg] at h3
    have : 1 / 2 < (exp (2 / 3))⁻¹ := by
      rw [one_div]; exact inv_strictAnti₀ (exp_pos _) this
    linarith
  have hev := (h.eventually (Ioo_mem_nhds hgt hlt1)).and (eventually_ge_atTop (2 : ℝ))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hev
  refine ⟨max y₀ 2, by linarith [le_max_right y₀ 2], fun y hy => ?_⟩
  obtain ⟨⟨hlo, hhi⟩, hy2⟩ := hy₀ y (le_of_max_le_left hy)
  have hlog : 0 < log y := log_pos (by linarith)
  constructor
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ hlog]; linarith

lemma ev_exp_rpow (α C : ℝ) (hα : 0 < α) : ∀ᶠ L : ℝ in atTop, C * L ≤ exp (L ^ α) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ (n : ℝ) * α := by
    refine ⟨⌈1 / α⌉₊, ?_⟩
    have := Nat.le_ceil (1 / α)
    rw [div_le_iff₀ hα] at this
    linarith
  have hu := tendsto_rpow_atTop hα
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hu.eventually_ge_atTop (max 1 (|C| * (n + 1).factorial))] with L hL1 hL
  have hu0 : 0 ≤ L ^ α := by positivity
  have hLu : L ≤ (L ^ α) ^ n := by
    rw [← rpow_natCast, ← rpow_mul (by linarith)]
    calc L = L ^ (1 : ℝ) := (rpow_one L).symm
      _ ≤ L ^ (α * n) := rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hfac : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hC : |C| * (n + 1).factorial ≤ L ^ α := le_of_max_le_right hL
  have h1 : C * L ≤ |C| * (L ^ α) ^ n := by
    calc C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * (L ^ α) ^ n := mul_le_mul_of_nonneg_left hLu (abs_nonneg C)
  have h2 : |C| * (L ^ α) ^ n ≤ (L ^ α) ^ (n + 1) / (n + 1).factorial := by
    rw [le_div_iff₀ hfac, pow_succ]
    have : 0 ≤ (L ^ α) ^ n := by positivity
    nlinarith
  exact h1.trans (h2.trans (pow_div_factorial_le_exp (L ^ α) hu0 (n + 1)))

lemma ev_rpow_le (β c : ℝ) (hβ : β < 1) (hc : 0 < c) : ∀ᶠ L : ℝ in atTop, L ^ β ≤ c * L := by
  have hu := tendsto_rpow_atTop (show 0 < 1 - β by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hu.eventually_ge_atTop (1 / c)] with L hL0 hL
  have e : L = L ^ β * L ^ (1 - β) := by
    rw [← rpow_add hL0]; simp
  have h0 : 0 ≤ L ^ β := by positivity
  calc L ^ β = L ^ β * 1 := (mul_one _).symm
    _ ≤ L ^ β * (c * L ^ (1 - β)) := by
        apply mul_le_mul_of_nonneg_left _ h0
        rw [div_le_iff₀ hc] at hL; linarith
    _ = c * (L ^ β * L ^ (1 - β)) := by ring
    _ = c * L := by rw [← e]

/-- The asymptotic facts used, in terms of `z = x^{0.002}`. -/
lemma eventually_facts : ∀ᶠ x : ℝ in atTop,
    1 < x ∧ 2 ≤ sieveLevel x ∧ sieveLevel x ≤ x ^ (0.002 : ℝ) ∧
    x ^ (0.002 : ℝ) ≤ x ^ (0.9 : ℝ) ∧
    2 * sieveLevel x ^ 10 * (sieveLevel x ^ 10 + 1) ≤ (x ^ (0.002 : ℝ)) ^ 5 ∧
    1 / (x ^ (0.002 : ℝ)) ^ 5 ≤ mertensProduct (sieveLevel x) ∧
    1 / (x ^ (0.002 : ℝ)) ^ 5 ≤ mertensProduct (x ^ (0.002 : ℝ)) ∧
    mertensProduct (x ^ (0.002 : ℝ)) ≤ 500 / log x ∧
    (∀ m : ℕ, 0 < m → (m : ℝ) ≤ 8 * x → IsRough (sieveLevel x) m → 1 / 2 ≤ Rf m) ∧
    (∀ r : ℕ, 0 < r → (r : ℝ) ≤ x →
      (∀ p ∈ r.primeFactors, exp (log x ^ (0.1 : ℝ)) ≤ p) → 1 / 2 ≤ Rf r) := by
  obtain ⟨y₀, hy₀1, hy₀⟩ := mertens_bounds
  have hlog := tendsto_log_atTop
  have hL24 := tendsto_rpow_atTop (show (0 : ℝ) < 0.24 by norm_num)
  have hA : ∀ᶠ x : ℝ in atTop,
      1 ≤ log x ∧ log 8 ≤ log x ∧ log 4 ≤ 0.005 * log x ∧
      4 * log x ≤ exp (log x ^ (0.24 : ℝ)) ∧ 2 * log x ≤ exp (log x ^ (0.1 : ℝ)) ∧
      log x ^ (0.24 : ℝ) ≤ 0.002 * log x ∧ 20 * log x ^ (0.24 : ℝ) ≤ 0.005 * log x ∧
      log y₀ ≤ log x ^ (0.24 : ℝ) :=
    (hlog.eventually ((eventually_ge_atTop 1).and ((eventually_ge_atTop (log 8)).and
      ((eventually_ge_atTop (log 4 / 0.005)).and ((ev_exp_rpow 0.24 4 (by norm_num)).and
      ((ev_exp_rpow 0.1 2 (by norm_num)).and ((ev_rpow_le 0.24 0.002 (by norm_num)
        (by norm_num)).and ((ev_rpow_le 0.24 (0.005 / 20) (by norm_num) (by norm_num)).and
      (hL24.eventually_ge_atTop (log y₀)))))))))).mono fun x h => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
        refine ⟨h1, h2, ?_, h4, h5, h6, ?_, h8⟩
        · rw [div_le_iff₀ (by norm_num)] at h3; linarith
        · linarith
  filter_upwards [hA, eventually_gt_atTop (1 : ℝ)] with x hA hx1
  obtain ⟨hL1, hL8, hL4, hW4, hT2, hWz', h20, hy⟩ := hA
  have hx0 : 0 < x := by linarith
  set L := log x with hL_def
  have hW : sieveLevel x = exp (L ^ (0.24 : ℝ)) := rfl
  have hz : x ^ (0.002 : ℝ) = exp (0.002 * L) := by rw [rpow_def_of_pos hx0, mul_comm]
  have hlogz : log (x ^ (0.002 : ℝ)) = 0.002 * L := by rw [hz, log_exp]
  have hlogW : log (sieveLevel x) = L ^ (0.24 : ℝ) := by rw [hW, log_exp]
  have hL24ge : 1 ≤ L ^ (0.24 : ℝ) := one_le_rpow hL1 (by norm_num)
  have hL10ge : 1 ≤ L ^ (0.1 : ℝ) := one_le_rpow hL1 (by norm_num)
  have he2 : (2 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hW2 : 2 ≤ sieveLevel x := by
    rw [hW]; exact he2.trans (exp_le_exp.2 hL24ge)
  have hWz : sieveLevel x ≤ x ^ (0.002 : ℝ) := by rw [hW, hz]; exact exp_le_exp.2 hWz'
  have hz2 : 2 ≤ x ^ (0.002 : ℝ) := hW2.trans hWz
  have hz5 : (x ^ (0.002 : ℝ)) ^ 5 = exp (0.01 * L) := by
    rw [hz, ← exp_nat_mul]; congr 1; push_cast; ring
  have hWy : y₀ ≤ sieveLevel x := by
    rw [hW]
    calc y₀ = exp (log y₀) := (exp_log (by linarith)).symm
      _ ≤ _ := exp_le_exp.2 hy
  have hlogz_le : 2 * log (x ^ (0.002 : ℝ)) ≤ (x ^ (0.002 : ℝ)) ^ 5 := by
    have h1 : log (x ^ (0.002 : ℝ)) ≤ x ^ (0.002 : ℝ) := (log_le_sub_one_of_pos (by linarith)).trans
      (by linarith)
    have h2 : 2 * x ^ (0.002 : ℝ) ≤ (x ^ (0.002 : ℝ)) ^ 5 := by
      have : (2 : ℝ) ^ 4 ≤ (x ^ (0.002 : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hz2 4
      nlinarith
    linarith
  have hlogpos : 0 < log (sieveLevel x) := by rw [hlogW]; linarith
  have hlogzpos : 0 < log (x ^ (0.002 : ℝ)) := by rw [hlogz]; linarith
  have hz5pos : 0 < (x ^ (0.002 : ℝ)) ^ 5 := by positivity
  refine ⟨hx1, hW2, hWz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  · -- `2 W^10 (W^10 + 1) ≤ z^5`
    have hW1 : 1 ≤ sieveLevel x ^ 10 := one_le_pow₀ (by linarith)
    have h1 : 2 * sieveLevel x ^ 10 * (sieveLevel x ^ 10 + 1) ≤ 4 * sieveLevel x ^ 20 := by
      have e : sieveLevel x ^ 20 = sieveLevel x ^ 10 * sieveLevel x ^ 10 := by rw [← pow_add]
      nlinarith
    have h2 : 4 * sieveLevel x ^ 20 = exp (log 4 + 20 * L ^ (0.24 : ℝ)) := by
      rw [exp_add, exp_log (by norm_num), hW, ← exp_nat_mul]; push_cast; ring_nf
    rw [hz5]
    refine h1.trans (h2 ▸ exp_le_exp.2 ?_)
    linarith
  · -- `1/z^5 ≤ V(W)`
    have := (hy₀ (sieveLevel x) hWy).1
    refine le_trans ?_ this
    rw [div_le_div_iff₀ hz5pos (by positivity)]
    have : log (sieveLevel x) ≤ log (x ^ (0.002 : ℝ)) := log_le_log (by linarith) hWz
    linarith
  · -- `1/z^5 ≤ V(z)`
    have := (hy₀ (x ^ (0.002 : ℝ)) (hWy.trans hWz)).1
    refine le_trans ?_ this
    rw [div_le_div_iff₀ hz5pos (by positivity)]
    linarith
  · -- `V(z) ≤ 500 / L`
    have := (hy₀ (x ^ (0.002 : ℝ)) (hWy.trans hWz)).2
    rw [hlogz] at this
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  · intro m hm hm8 hR
    apply Rf_ge_half m hm (sieveLevel x) (by linarith) (fun p hp => (hR.2 p hp).le)
    rw [hlogW]
    have hlm : log m ≤ log 8 + L := by
      rw [← log_mul (by norm_num) hx0.ne']
      exact log_le_log (by exact_mod_cast hm) hm8
    have : 4 * L ≤ sieveLevel x * L ^ (0.24 : ℝ) := by
      rw [hW]
      have := hW4
      have h0 : 0 ≤ exp (L ^ (0.24 : ℝ)) := (exp_pos _).le
      nlinarith
    linarith
  · intro r hr hrx hp
    have hT : 1 < exp (L ^ (0.1 : ℝ)) := one_lt_exp_iff.2 (by linarith)
    apply Rf_ge_half r hr _ hT hp
    rw [log_exp]
    have hlr : log r ≤ L := log_le_log (by exact_mod_cast hr) hrx
    have h0 : 0 ≤ exp (L ^ (0.1 : ℝ)) := (exp_pos _).le
    nlinarith

/-! ## The weight bound -/

lemma mark_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 ≤ mark (1 / 2) x a h := by
  unfold mark
  apply mul_nonneg (zpow_nonneg (by norm_num) _)
  apply prod_nonneg
  intro i _
  apply div_nonneg (Nat.cast_nonneg _)
  unfold groupReciprocalSum
  exact sum_nonneg fun p _ => by positivity

lemma mem_groupPrimes_prime (x : ℝ) {K : ℕ} (a : Fin K → ℝ) {p : ℕ} (hp : p ∈ groupPrimes x a) :
    p.Prime := by
  unfold groupPrimes at hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hp
  exact (Finset.mem_filter.1 hi).2.1

lemma groupPart_dvd (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) (hh : h ≠ 0) :
    groupPart x a h ∣ h := by
  classical
  unfold groupPart
  rw [← prod_filter_of_ne (p := fun p => p ∈ h.primeFactors)]
  · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hh]
    rw [Finsupp.prod, Nat.support_factorization]
    exact prod_dvd_prod_of_subset _ _ _ (fun p hp => (Finset.mem_filter.1 hp).2)
  · intro p _ hne
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0; rw [h0, pow_zero] at hne; exact hne rfl

lemma groupPart_pos (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : 0 < groupPart x a h := by
  unfold groupPart
  exact prod_pos fun p hp => pow_pos (mem_groupPrimes_prime x a hp).pos _

lemma isGroupInteger_groupPart (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) :
    IsGroupInteger x a (groupPart x a h) := by
  refine ⟨groupPart_pos x a h, fun q hq => ?_⟩
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  unfold groupPart at hqd
  obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
  have := hqp.dvd_of_dvd_pow hqp'
  rw [(Nat.prime_dvd_prime_iff_eq hqp (mem_groupPrimes_prime x a hp)).1 this]
  exact hp

lemma mark_groupPart (q x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) (hh : h ≠ 0) :
    mark q x a (groupPart x a h) = mark q x a h := by
  have key : ∀ i, groupOmega x (a i) (groupPart x a h) = groupOmega x (a i) h := by
    intro i
    unfold groupOmega
    congr 1
    apply filter_congr
    intro p hp
    constructor
    · intro hd; exact hd.trans (groupPart_dvd x a h hh)
    · intro hd
      have hpp : p.Prime := (Finset.mem_filter.1 hp).2.1
      have hG : p ∈ groupPrimes x a := by
        unfold groupPrimes; exact Finset.mem_biUnion.2 ⟨i, mem_univ _, hp⟩
      have hpos := hpp.factorization_pos_of_dvd hh hd
      unfold groupPart
      exact (dvd_pow_self p hpos.ne').trans (dvd_prod_of_mem _ hG)
  unfold mark markOmega
  simp only [key]

open Classical in
lemma weight_le (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (_hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hc : 2 ≤ c) (x : ℝ) (hx : 0 < x) {K : ℕ}
    (a : Fin K → ℝ) (d : ℕ) :
    constructionWeight M c u Ψ x a d ≤
      ∑ r ∈ (range (⌊x ^ (0.1 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a),
        mark (1 / 2) x a r *
          (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * r * Q + 1 then 1 else 0) := by
  have hsum0 : 0 ≤ ∑ r ∈ (range (⌊x ^ (0.1 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a),
      mark (1 / 2) x a r *
        (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * r * Q + 1 then (1 : ℝ) else 0) :=
    sum_nonneg fun r _ => mul_nonneg (mark_nonneg x a r) (by split_ifs <;> norm_num)
  unfold constructionWeight
  split_ifs with hd
  · unfold predecessorIndicator
    split_ifs with hF
    · obtain ⟨Q, hQp, hQx, hQe⟩ := hF
      have hh0 : d - 1 ≠ 0 := by omega
      have hrd := groupPart_dvd x a (d - 1) hh0
      have hdec : d - 1 = c * groupPart x a (d - 1) * Q := by
        rw [mul_comm c, mul_assoc, ← hQe, Nat.mul_div_cancel' hrd]
      have hdd : d = c * groupPart x a (d - 1) * Q + 1 := by omega
      by_cases hΨz : Ψ (d / x) = 0
      · rw [hΨz, zero_mul, zero_mul]; exact hsum0
      · have hmem : (d : ℝ) / x ∈ Set.Ioo 1 2 := hΨs (subset_tsupport Ψ hΨz)
        have hdx : (d : ℝ) < 2 * x := by
          have := hmem.2; rw [div_lt_iff₀ hx] at this; linarith
        set r := groupPart x a (d - 1) with hr_def
        have hr0 : 0 < r := groupPart_pos x a (d - 1)
        have hx9 : 0 < x ^ (0.9 : ℝ) := rpow_pos_of_pos hx _
        have hrx : (r : ℝ) < x ^ (0.1 : ℝ) := by
          have hcast : ((d : ℕ) : ℝ) = c * r * Q + 1 := by exact_mod_cast hdd
          have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
          have hxx : x = x ^ (0.1 : ℝ) * x ^ (0.9 : ℝ) := by
            rw [← rpow_add hx]; norm_num
          have h1 : (r : ℝ) * x ^ (0.9 : ℝ) < r * Q :=
            mul_lt_mul_of_pos_left hQx (by exact_mod_cast hr0)
          have h2 : (2 : ℝ) * (r * Q) ≤ c * r * Q := by
            have : (0 : ℝ) ≤ r * Q := by positivity
            nlinarith
          have h3 : (r : ℝ) * x ^ (0.9 : ℝ) < x ^ (0.1 : ℝ) * x ^ (0.9 : ℝ) := by
            rw [← hxx]; linarith
          exact lt_of_mul_lt_mul_right h3 hx9.le
        have hrmem : r ∈ (range (⌊x ^ (0.1 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a) := by
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_of_le (Nat.le_floor hrx.le), isGroupInteger_groupPart x a _⟩
        have hmk := mark_groupPart (1 / 2) x a (d - 1) hh0
        rw [← hr_def] at hmk
        calc Ψ (d / x) * 1 * mark (1 / 2) x a (d - 1) ≤ mark (1 / 2) x a r := by
              rw [mul_one, ← hmk]
              exact mul_le_of_le_one_left (mark_nonneg x a r) (hΨ1 _)
          _ = mark (1 / 2) x a r *
              (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * r * Q + 1 then (1 : ℝ) else 0) := by
              rw [if_pos ⟨Q, hQp, hQx, hdd⟩, mul_one]
          _ ≤ _ := single_le_sum (f := fun r => mark (1 / 2) x a r *
              (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ d = c * r * Q + 1 then (1 : ℝ) else 0))
              (fun r _ => mul_nonneg (mark_nonneg x a r) (by split_ifs <;> norm_num)) hrmem
    · rw [mul_zero, zero_mul]; exact hsum0
  · exact hsum0

lemma harmonic_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (S : Finset ℕ)
    (hS : ∀ r ∈ S, IsGroupInteger x a r) :
    ∑ r ∈ S, mark (1 / 2) x a r / r ≤ harmonicMass x a := by
  -- a uniform bound on the mark
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ r, mark (1 / 2) x a r ≤ C := by
    refine ⟨2 ^ K * ∏ i, ((primeGroup x (a i)).card : ℝ) / groupReciprocalSum x (a i),
      fun r => ?_⟩
    unfold mark
    apply mul_le_mul
    · have : ((1 : ℝ) / 2) ^ ((markOmega x a r : ℤ) - K) ≤ ((1 : ℝ) / 2) ^ (-(K : ℤ)) :=
        zpow_le_zpow_right_of_le_one₀ (by norm_num) (by norm_num) (by omega)
      refine this.trans (le_of_eq ?_)
      rw [zpow_neg, zpow_natCast, one_div, inv_pow, inv_inv]
    · apply Finset.prod_le_prod
      · intro i _
        apply div_nonneg (Nat.cast_nonneg _)
        unfold groupReciprocalSum; exact sum_nonneg fun p _ => by positivity
      · intro i _
        have hV : 0 ≤ groupReciprocalSum x (a i) := by
          unfold groupReciprocalSum; exact sum_nonneg fun p _ => by positivity
        apply div_le_div_of_nonneg_right _ hV
        unfold groupOmega
        exact_mod_cast card_filter_le _ _
    · apply prod_nonneg
      intro i _
      apply div_nonneg (Nat.cast_nonneg _)
      unfold groupReciprocalSum; exact sum_nonneg fun p _ => by positivity
    · positivity
  -- summability of `1/r` over group integers
  have hE := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => ((n : ℝ))⁻¹) (by simp) (fun {m n} _ => by push_cast; rw [mul_inv])
    (fun {p} hp => by
      simp only [Nat.cast_pow, norm_inv, norm_pow, Real.norm_natCast, ← inv_pow]
      exact summable_geometric_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)))
    (groupPrimes x a)
  let i : {r : ℕ // IsGroupInteger x a r} → Nat.factoredNumbers (groupPrimes x a) :=
    fun r => ⟨r.1, Nat.mem_factoredNumbers'.2 fun p hp hpd =>
      r.2.2 p (Nat.mem_primeFactors.2 ⟨hp, hpd, r.2.1.ne'⟩)⟩
  have hi : Function.Injective i := by
    intro r s hrs
    apply Subtype.ext
    have := congrArg Subtype.val hrs
    exact this
  have hsum1 := hE.1.comp_injective hi
  have hsumm : Summable (fun r : {r : ℕ // IsGroupInteger x a r} => mark (1 / 2) x a r / r) := by
    refine Summable.of_nonneg_of_le (fun r => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _))
      (fun r => ?_) (hsum1.mul_left C)
    simp only [Function.comp_apply, i, norm_inv, Real.norm_natCast]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hC r) (by positivity)
  classical
  have h1 : ∑ r ∈ S, mark (1 / 2) x a r / r =
      ∑ r ∈ S.subtype (IsGroupInteger x a), mark (1 / 2) x a r / r := by
    rw [Finset.sum_subtype_eq_sum_filter (f := fun r : ℕ => mark (1 / 2) x a r / (r : ℝ)),
      filter_true_of_mem hS]
  rw [h1]
  exact hsumm.sum_le_tsum _ (fun r _ => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _))

/-! ## The pair count -/

lemma Rf_crm (c r m : ℕ) (hc : c = 2 ∨ c = 4) (hr0 : 0 < r) (hm0 : 0 < m)
    (hRr : 1 / 2 ≤ Rf r) (hRm : 1 / 2 ≤ Rf m) : 1 / 8 ≤ Rf (c * r * m) := by
  have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have e1 := Rf_mul_ge (c * r) m (Nat.mul_ne_zero hc0 hr0.ne') hm0.ne'
  have e2 := Rf_mul_ge c r hc0 hr0.ne'
  rw [Rf_two_or_four c hc] at e2
  have h3 : 1 / 4 ≤ Rf (c * r) := by
    calc (1 : ℝ) / 4 = 1 / 2 * (1 / 2) := by norm_num
      _ ≤ 1 / 2 * Rf r := mul_le_mul_of_nonneg_left hRr (by norm_num)
      _ ≤ _ := e2
  calc (1 : ℝ) / 8 = 1 / 4 * (1 / 2) := by norm_num
    _ ≤ Rf (c * r) * Rf m := mul_le_mul h3 hRm (by norm_num) (Rf_pos _).le
    _ ≤ _ := e1

open Classical in
lemma inner_bound (B : ℝ) (hB0 : 0 ≤ B) (hB : SieveBound B) (x W z : ℝ) (hW2 : 2 ≤ W)
    (hWz : W ≤ z) (hz9 : z ≤ x ^ (0.9 : ℝ)) (c r m : ℕ) (hc : c = 2 ∨ c = 4) (hr0 : 0 < r)
    (hRr : 1 / 2 ≤ Rf r) (hm0 : 0 < m) (hRm : 1 / 2 ≤ Rf m) (M₂ : ℝ) (hM2 : 0 ≤ M₂) :
    ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
        (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough W n),
      (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1 then (1 : ℝ) else 0)
      ≤ B * (64 * (M₂ + 1) / ((c * r : ℕ) : ℝ) * mertensProduct W * mertensProduct z +
        2 * z ^ 10 * (z ^ 10 + 1)) := by
  have hcr : 0 < c * r := Nat.mul_pos (by rcases hc with rfl | rfl <;> norm_num) hr0
  have hcr2 : 2 ∣ c * r := by
    rcases hc with rfl | rfl
    · exact dvd_mul_right 2 r
    · exact dvd_mul_of_dvd_left (by norm_num) r
  rw [sum_boole]
  have hsub : ((Finset.range ⌈2 * M₂⌉₊).filter
        (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough W n)).filter
        (fun n => ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1) ⊆
      (Ico ⌈M₂⌉₊ ⌈2 * M₂⌉₊).filter
        (fun n => IsRough W n ∧ ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = (c * r) * Q + 1) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨Nat.ceil_le.2 hn.1.2.1, hn.1.1⟩, hn.1.2.2.2, hn.2⟩
  have hcount := n_count B hB0 hB W z (x ^ (0.9 : ℝ)) (by linarith) hWz (hW2.trans hWz) hz9
    (c * r) m hcr hcr2 hm0 M₂ hM2
  have hRcrm := Rf_crm c r m hc hr0 hm0 hRr hRm
  have hV0 := mertensProduct_nonneg W
  have hVz0 := mertensProduct_nonneg z
  have hinv : mertensProduct W * mertensProduct z / Rf (c * r * m) ^ 2 ≤
      64 * (mertensProduct W * mertensProduct z) := by
    have hpos : 0 < Rf (c * r * m) ^ 2 := by have := Rf_pos (c * r * m); positivity
    rw [div_le_iff₀ hpos]
    have h64 : 1 ≤ 64 * Rf (c * r * m) ^ 2 := by
      have : (1 / 8 : ℝ) ^ 2 ≤ Rf (c * r * m) ^ 2 := pow_le_pow_left₀ (by norm_num) hRcrm 2
      linarith
    have hVV : 0 ≤ mertensProduct W * mertensProduct z := mul_nonneg hV0 hVz0
    calc mertensProduct W * mertensProduct z = mertensProduct W * mertensProduct z * 1 := by ring
      _ ≤ mertensProduct W * mertensProduct z * (64 * Rf (c * r * m) ^ 2) :=
          mul_le_mul_of_nonneg_left h64 hVV
      _ = _ := by ring
  have hc1 : ((#(((Finset.range ⌈2 * M₂⌉₊).filter
        (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough W n)).filter
        (fun n => ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1)) : ℕ) : ℝ)
      ≤ ((#((Ico ⌈M₂⌉₊ ⌈2 * M₂⌉₊).filter
        (fun n => IsRough W n ∧ ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
          m * n = (c * r) * Q + 1)) : ℕ) : ℝ) := by exact_mod_cast card_le_card hsub
  refine hc1.trans (hcount.trans ?_)
  apply mul_le_mul_of_nonneg_left _ hB0
  apply add_le_add _ le_rfl
  have hk0 : (0 : ℝ) < ((c * r : ℕ) : ℝ) := by exact_mod_cast hcr
  have hMk : 0 ≤ (M₂ + 1) / ((c * r : ℕ) : ℝ) := by positivity
  calc (M₂ + 1) / ((c * r : ℕ) : ℝ) * (mertensProduct W * mertensProduct z / Rf (c * r * m) ^ 2)
      ≤ (M₂ + 1) / ((c * r : ℕ) : ℝ) * (64 * (mertensProduct W * mertensProduct z)) :=
        mul_le_mul_of_nonneg_left hinv hMk
    _ = 64 * (M₂ + 1) / ((c * r : ℕ) : ℝ) * mertensProduct W * mertensProduct z := by ring

lemma numeric_bound (B x z r M₁ M₂ V Vz b1 k : ℝ) (_hB0 : 0 ≤ B) (hz2 : 2 ≤ z)
    (e500 : x = z ^ 500) (hr1 : 1 ≤ r) (hrx : r ≤ z ^ 50)
    (h2 : M₁ * M₂ ≤ 2 * x) (h3 : z ^ 230 / 2 ≤ M₁) (h4 : M₁ ≤ 2 * z ^ 270)
    (h5 : z ^ 230 / 2 ≤ M₂) (h6 : M₂ ≤ 2 * z ^ 270)
    (hV0 : 0 ≤ V) (hV1 : V ≤ 1) (hVz0 : 0 ≤ Vz) (hVz1 : Vz ≤ 1)
    (hVW : 1 / z ^ 5 ≤ V) (hVz : 1 / z ^ 5 ≤ Vz) (_hb0 : 0 ≤ b1) (hb1 : b1 ≤ z ^ 5)
    (hk : 2 * r ≤ k) :
    B * ((M₁ + 1) * V + b1) * (B * (64 * (M₂ + 1) / k * V * Vz + 2 * z ^ 10 * (z ^ 10 + 1)))
      ≤ 257 * B ^ 2 * (x / r) * V ^ 2 * Vz := by
  have hz1 : 1 ≤ z := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → z ^ a ≤ z ^ b := fun a b hab => pow_le_pow_right₀ hz1 hab
  have hz230 : (2 : ℝ) ≤ z ^ 230 := hz2.trans (by simpa using hpow 1 230 (by norm_num))
  have hM1 : 1 ≤ M₁ := by linarith
  have hM2 : 1 ≤ M₂ := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  set X := x / r * V ^ 2 * Vz with hX
  have hXlow : z ^ 435 ≤ X := by
    have hxr : z ^ 450 ≤ x / r := by
      rw [le_div_iff₀ (by linarith), e500]
      calc z ^ 450 * r ≤ z ^ 450 * z ^ 50 := mul_le_mul_of_nonneg_left hrx (by positivity)
        _ = z ^ 500 := by rw [← pow_add]
    have hprod : 1 / z ^ 15 ≤ V ^ 2 * Vz := by
      have e : 1 / z ^ 15 = (1 / z ^ 5) ^ 2 * (1 / z ^ 5) := by
        rw [div_pow, one_pow, one_div_mul_one_div, ← pow_mul, ← pow_add]
      rw [e]
      have hz0 : 0 < z := by linarith
      have h15 : 0 ≤ 1 / z ^ 5 := by positivity
      exact mul_le_mul (pow_le_pow_left₀ h15 hVW 2) hVz h15 (by positivity)
    calc z ^ 435 = z ^ 450 * (1 / z ^ 15) := by
          rw [mul_one_div, eq_div_iff (by positivity), ← pow_add]
      _ ≤ x / r * (V ^ 2 * Vz) := by
          have hz0 : 0 < z := by linarith
          have hx0 : 0 ≤ x := by rw [e500]; positivity
          have : 0 ≤ x / r := div_nonneg hx0 (by linarith)
          exact mul_le_mul hxr hprod (by positivity) this
      _ = X := by rw [hX]; ring
  have hMM : (M₁ + 1) * (M₂ + 1) ≤ 8 * x := by nlinarith
  have hz10 : 2 * z ^ 10 * (z ^ 10 + 1) ≤ 4 * z ^ 20 := by
    have : 1 ≤ z ^ 10 := one_le_pow₀ hz1
    have e : z ^ 20 = z ^ 10 * z ^ 10 := by rw [← pow_add]
    nlinarith
  have h270 : 1 ≤ z ^ 270 := one_le_pow₀ hz1
  set a1 := (M₁ + 1) * V with ha1
  set c1 := 64 * (M₂ + 1) / k * V * Vz with hc1
  set d1 := 2 * z ^ 10 * (z ^ 10 + 1) with hd1
  have hq0 : 0 ≤ 64 * (M₂ + 1) / k := by positivity
  have ha1n : 0 ≤ a1 := by positivity
  have hc1n : 0 ≤ c1 := by positivity
  have hd1n : 0 ≤ d1 := by positivity
  have ha1u : a1 ≤ 4 * z ^ 270 := by
    calc (M₁ + 1) * V ≤ (M₁ + 1) * 1 := mul_le_mul_of_nonneg_left hV1 (by linarith)
      _ ≤ _ := by linarith
  have hc1u : c1 ≤ 256 * z ^ 270 := by
    have h1 : 64 * (M₂ + 1) / k ≤ 64 * (M₂ + 1) := div_le_self (by positivity) hk1
    have h2 : 64 * (M₂ + 1) / k * V * Vz ≤ 64 * (M₂ + 1) / k := by
      calc 64 * (M₂ + 1) / k * V * Vz ≤ 64 * (M₂ + 1) / k * 1 * 1 := by gcongr
        _ = _ := by ring
    linarith
  have hac : a1 * c1 ≤ 256 * X := by
    have e : (M₁ + 1) * V * (64 * (M₂ + 1) / k * V * Vz) =
        64 * ((M₁ + 1) * (M₂ + 1)) / k * (V ^ 2 * Vz) := by ring
    rw [ha1, hc1, e]
    have e2 : 256 * X = 256 * x / r * (V ^ 2 * Vz) := by rw [hX]; ring
    rw [e2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_div_iff₀ hk0 (by linarith)]
    have hx0 : 0 ≤ x := by rw [e500]; positivity
    have hP0 : 0 ≤ (M₁ + 1) * (M₂ + 1) := by positivity
    calc 64 * ((M₁ + 1) * (M₂ + 1)) * r ≤ 64 * (8 * x) * r := by gcongr
      _ = 256 * x * (2 * r) := by ring
      _ ≤ 256 * x * k := by gcongr
  have hrest : a1 * d1 + b1 * c1 + b1 * d1 ≤ 276 * z ^ 290 := by
    have t1 : a1 * d1 ≤ 16 * z ^ 290 := by
      calc a1 * d1 ≤ (4 * z ^ 270) * (4 * z ^ 20) :=
            mul_le_mul ha1u hz10 hd1n (by positivity)
        _ = 16 * z ^ 290 := by rw [mul_mul_mul_comm, ← pow_add]; norm_num
    have t2 : b1 * c1 ≤ 256 * z ^ 275 := by
      calc b1 * c1 ≤ z ^ 5 * (256 * z ^ 270) := mul_le_mul hb1 hc1u hc1n (by positivity)
        _ = 256 * z ^ 275 := by rw [mul_left_comm, ← pow_add]
    have t3 : b1 * d1 ≤ 4 * z ^ 25 := by
      calc b1 * d1 ≤ z ^ 5 * (4 * z ^ 20) := mul_le_mul hb1 hz10 hd1n (by positivity)
        _ = 4 * z ^ 25 := by rw [mul_left_comm, ← pow_add]
    have := hpow 275 290 (by norm_num)
    have := hpow 25 290 (by norm_num)
    linarith
  have hbig : 276 * z ^ 290 ≤ z ^ 435 := by
    have h1 : (276 : ℝ) ≤ z ^ 145 := by
      calc (276 : ℝ) ≤ 2 ^ 145 := by norm_num
        _ ≤ z ^ 145 := pow_le_pow_left₀ (by norm_num) hz2 145
    calc 276 * z ^ 290 ≤ z ^ 145 * z ^ 290 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = z ^ 435 := by rw [← pow_add]
  have hsplit : B * (a1 + b1) * (B * (c1 + d1)) =
      B ^ 2 * (a1 * c1 + (a1 * d1 + b1 * c1 + b1 * d1)) := by ring
  rw [hsplit]
  calc B ^ 2 * (a1 * c1 + (a1 * d1 + b1 * c1 + b1 * d1)) ≤ B ^ 2 * (256 * X + X) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
        linarith
    _ = 257 * B ^ 2 * (x / r) * V ^ 2 * Vz := by rw [hX]; ring

open Classical in
lemma pair_count (B : ℝ) (hB0 : 0 ≤ B) (hB : SieveBound B) : ∀ᶠ x : ℝ in atTop,
    ∀ (c r : ℕ), (c = 2 ∨ c = 4) → 0 < r → (r : ℝ) ≤ x ^ (0.1 : ℝ) → 1 / 2 ≤ Rf r →
    ∀ M₁ M₂ : ℝ, x / 4 ≤ M₁ * M₂ → M₁ * M₂ ≤ 2 * x →
      x ^ (0.46 : ℝ) / 2 ≤ M₁ → M₁ ≤ 2 * x ^ (0.54 : ℝ) →
      x ^ (0.46 : ℝ) / 2 ≤ M₂ → M₂ ≤ 2 * x ^ (0.54 : ℝ) →
      ∑ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
            (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
        ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
            (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n),
          (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1 then (1 : ℝ) else 0)
        ≤ 257 * B ^ 2 * (x / r) * mertensProduct (sieveLevel x) ^ 2 *
            mertensProduct (x ^ (0.002 : ℝ)) := by
  filter_upwards [eventually_facts] with x hx
  obtain ⟨hx1, hW2, hWz, hz9, hW10, hVW, hVz, -, hRm, -⟩ := hx
  intro c r hc hr0 hrx hRr M₁ M₂ _ h2 h3 h4 h5 h6
  have hx0 : 0 < x := by linarith
  have hz2 : 2 ≤ x ^ (0.002 : ℝ) := hW2.trans hWz
  have hzp : ∀ n : ℕ, (x ^ (0.002 : ℝ)) ^ n = x ^ ((n : ℝ) * 0.002) := by
    intro n
    rw [← rpow_natCast, ← rpow_mul hx0.le, mul_comm]
  have e500 : x = (x ^ (0.002 : ℝ)) ^ 500 := by rw [hzp]; norm_num
  have e50 : x ^ (0.1 : ℝ) = (x ^ (0.002 : ℝ)) ^ 50 := by rw [hzp]; norm_num
  have e230 : x ^ (0.46 : ℝ) = (x ^ (0.002 : ℝ)) ^ 230 := by rw [hzp]; norm_num
  have e270 : x ^ (0.54 : ℝ) = (x ^ (0.002 : ℝ)) ^ 270 := by rw [hzp]; norm_num
  rw [e230] at h3 h5
  rw [e270] at h4 h6
  rw [e50] at hrx
  have hz1 : (1 : ℝ) ≤ x ^ (0.002 : ℝ) := by linarith
  have hM1 : 0 ≤ M₁ := le_trans (by positivity) h3
  have hM2 : 0 ≤ M₂ := le_trans (by positivity) h5
  have hinner : ∀ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
      (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
      ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
          (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n),
        (if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1 then (1 : ℝ) else 0)
        ≤ B * (64 * (M₂ + 1) / ((c * r : ℕ) : ℝ) * mertensProduct (sieveLevel x) *
          mertensProduct (x ^ (0.002 : ℝ)) +
          2 * (x ^ (0.002 : ℝ)) ^ 10 * ((x ^ (0.002 : ℝ)) ^ 10 + 1)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨_, _, hm2, hmR⟩ := hm
    have hm8 : (m : ℝ) ≤ 8 * x := by
      have : (x ^ (0.002 : ℝ)) ^ 270 ≤ (x ^ (0.002 : ℝ)) ^ 500 :=
        pow_le_pow_right₀ hz1 (by norm_num)
      rw [← e500] at this
      linarith
    exact inner_bound B hB0 hB x (sieveLevel x) (x ^ (0.002 : ℝ)) hW2 hWz hz9 c r m hc hr0 hRr
      hmR.1 (hRm m hmR.1 hm8 hmR) M₂ hM2
  have hY2nn : 0 ≤ B * (64 * (M₂ + 1) / ((c * r : ℕ) : ℝ) * mertensProduct (sieveLevel x) *
          mertensProduct (x ^ (0.002 : ℝ)) +
          2 * (x ^ (0.002 : ℝ)) ^ 10 * ((x ^ (0.002 : ℝ)) ^ 10 + 1)) := by
    have := mertensProduct_nonneg (sieveLevel x)
    have := mertensProduct_nonneg (x ^ (0.002 : ℝ))
    positivity
  have hS1 : ((#((Finset.range ⌈2 * M₁⌉₊).filter
      (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m)) : ℕ) : ℝ) ≤
      B * ((M₁ + 1) * mertensProduct (sieveLevel x) +
        2 * sieveLevel x ^ 10 * (sieveLevel x ^ 10 + 1)) := by
    have := card_le_card (box_sub M₁ (IsRough (sieveLevel x)))
    refine le_trans ?_ (m_count B hB0 hB (sieveLevel x) hW2 M₁ hM1)
    exact_mod_cast this
  have hk : 2 * (r : ℝ) ≤ ((c * r : ℕ) : ℝ) := by
    push_cast
    have : (2 : ℝ) ≤ c := by rcases hc with rfl | rfl <;> norm_num
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  calc _ ≤ ∑ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
        (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
        B * (64 * (M₂ + 1) / ((c * r : ℕ) : ℝ) * mertensProduct (sieveLevel x) *
          mertensProduct (x ^ (0.002 : ℝ)) +
          2 * (x ^ (0.002 : ℝ)) ^ 10 * ((x ^ (0.002 : ℝ)) ^ 10 + 1)) := sum_le_sum hinner
    _ = _ * _ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hS1 hY2nn
    _ ≤ _ := numeric_bound B x (x ^ (0.002 : ℝ)) r M₁ M₂ _ _ _ _ hB0 hz2 e500
        (by exact_mod_cast hr0) hrx h2 h3 h4 h5 h6 (mertensProduct_nonneg _)
        (mertensProduct_le_one _) (mertensProduct_nonneg _) (mertensProduct_le_one _) hVW hVz
        (by positivity) hW10 hk

/-- Group primes are large. -/
lemma groupPrime_large (x : ℝ) (hx : 1 ≤ log x) {K : ℕ} (a : Fin K → ℝ)
    (ha : ∀ i, (0.1 : ℝ) < a i) (r : ℕ) (hr : IsGroupInteger x a r) :
    ∀ p ∈ r.primeFactors, exp (log x ^ (0.1 : ℝ)) ≤ p := by
  intro p hp
  have hG := hr.2 p hp
  unfold groupPrimes at hG
  rw [Finset.mem_biUnion] at hG
  obtain ⟨i, _, hi⟩ := hG
  unfold primeGroup at hi
  rw [Finset.mem_filter] at hi
  refine le_trans ?_ hi.2.2
  apply exp_le_exp.2
  exact rpow_le_rpow_of_exponent_le hx (ha i).le

end ArtinPrimitiveRoots.RoughPairs

open ArtinPrimitiveRoots Real Finset Filter Topology ArtinPrimitiveRoots.RoughPairs RoughPairs Classical in
theorem solution (M : ℕ) (hM : 0 < M) (h8 : 8 ∣ M)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨs : tsupport Ψ ⊆ Set.Ioo 1 2)
    (hΨ0 : ∀ y, 0 ≤ Ψ y) (hΨ1 : ∀ y, Ψ y ≤ 1) (hΨi : 0 < ∫ y, Ψ y) :
    ∃ C₁ : ℝ, ∀ (c : ℕ) (u : ℤ), (c = 2 ∨ c = 4) → IsCoprime u M → (c : ℤ) ∣ u - 1 →
        IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
      ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M₁ M₂ : ℝ, x / 4 ≤ M₁ * M₂ → M₁ * M₂ ≤ 2 * x →
        x ^ (0.46 : ℝ) / 2 ≤ M₁ → M₁ ≤ 2 * x ^ (0.54 : ℝ) →
        x ^ (0.46 : ℝ) / 2 ≤ M₂ → M₂ ≤ 2 * x ^ (0.54 : ℝ) →
        ∑ m ∈ (Finset.range ⌈2 * M₁⌉₊).filter
              (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m),
          ∑ n ∈ (Finset.range ⌈2 * M₂⌉₊).filter
              (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n),
            constructionWeight M c u Ψ x a (m * n) ≤
          C₁ * totalMass M c u Ψ x a * mertensProduct (sieveLevel x) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := sieve1
  obtain ⟨c₁, c₂, hc₁, hc₂, hwfd⟩ :=
    (weighted_family_distribution M hM h8 Ψ hΨ hΨs hΨ0 hΨ1 hΨi).2
  refine ⟨257 * B ^ 2 * 500 / c₁, ?_⟩
  intro c u hc hu hcu hcop K hK a ha ha'
  obtain ⟨x₁, hx₁⟩ := hwfd c u hc hu hcu hcop K hK a ha ha'
  have hev := (eventually_facts.and (pair_count B hB0 hB)).and
    (eventually_ge_atTop (max x₁ (exp 1)))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hev
  refine ⟨x₀, fun x hx M₁ M₂ h1 h2 h3 h4 h5 h6 => ?_⟩
  obtain ⟨⟨facts, hpair⟩, hxbig⟩ := hx₀ x hx
  obtain ⟨hx1, -, -, -, -, -, -, hVz, -, hRr⟩ := facts
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (le_of_max_le_right hxbig)
  have hc2 : 2 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have hJ := (hx₁ x (le_of_max_le_left hxbig)).1
  set Rset := (range (⌊x ^ (0.1 : ℝ)⌋₊ + 1)).filter (IsGroupInteger x a) with hRset
  set V := mertensProduct (sieveLevel x) with hV
  set Vz := mertensProduct (x ^ (0.002 : ℝ)) with hVz_def
  set S1 := (Finset.range ⌈2 * M₁⌉₊).filter
    (fun m : ℕ => M₁ ≤ m ∧ (m : ℝ) < 2 * M₁ ∧ IsRough (sieveLevel x) m) with hS1
  set S2 := (Finset.range ⌈2 * M₂⌉₊).filter
    (fun n : ℕ => M₂ ≤ n ∧ (n : ℝ) < 2 * M₂ ∧ IsRough (sieveLevel x) n) with hS2
  set ind : ℕ → ℕ → ℕ → ℝ := fun m n r =>
    if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ m * n = c * r * Q + 1 then (1 : ℝ) else 0
    with hind
  have step1 : ∑ m ∈ S1, ∑ n ∈ S2, constructionWeight M c u Ψ x a (m * n) ≤
      ∑ m ∈ S1, ∑ n ∈ S2, ∑ r ∈ Rset, mark (1 / 2) x a r * ind m n r :=
    sum_le_sum fun m _ => sum_le_sum fun n _ =>
      weight_le M c u Ψ hΨs hΨ0 hΨ1 hc2 x hx0 a (m * n)
  have step2 : ∑ m ∈ S1, ∑ n ∈ S2, ∑ r ∈ Rset, mark (1 / 2) x a r * ind m n r =
      ∑ r ∈ Rset, mark (1 / 2) x a r * ∑ m ∈ S1, ∑ n ∈ S2, ind m n r := by
    calc ∑ m ∈ S1, ∑ n ∈ S2, ∑ r ∈ Rset, mark (1 / 2) x a r * ind m n r
        = ∑ m ∈ S1, ∑ r ∈ Rset, ∑ n ∈ S2, mark (1 / 2) x a r * ind m n r :=
          sum_congr rfl fun m _ => sum_comm
      _ = ∑ r ∈ Rset, ∑ m ∈ S1, ∑ n ∈ S2, mark (1 / 2) x a r * ind m n r := sum_comm
      _ = _ := by
          refine sum_congr rfl fun r _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun m _ => by rw [mul_sum]
  have step3 : ∑ r ∈ Rset, mark (1 / 2) x a r * ∑ m ∈ S1, ∑ n ∈ S2, ind m n r ≤
      ∑ r ∈ Rset, mark (1 / 2) x a r * (257 * B ^ 2 * (x / r) * V ^ 2 * Vz) := by
    refine sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (mark_nonneg x a r)
    rw [hRset, Finset.mem_filter, Finset.mem_range] at hr
    have hr0 : 0 < r := hr.2.1
    have hrx : (r : ℝ) ≤ x ^ (0.1 : ℝ) := by
      have := Nat.lt_succ_iff.1 hr.1
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
    have hrx' : (r : ℝ) ≤ x := by
      refine hrx.trans ?_
      calc x ^ (0.1 : ℝ) ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
        _ = x := rpow_one x
    have hRf := hRr r hr0 hrx' (groupPrime_large x hL a (fun i => (ha' i).1) r hr.2)
    exact hpair c r hc hr0 hrx hRf M₁ M₂ h1 h2 h3 h4 h5 h6
  have hsum : ∑ r ∈ Rset, mark (1 / 2) x a r / r ≤ harmonicMass x a :=
    harmonic_le x a Rset fun r hr => (Finset.mem_filter.1 hr).2
  have step4 : ∑ r ∈ Rset, mark (1 / 2) x a r * (257 * B ^ 2 * (x / r) * V ^ 2 * Vz) =
      257 * B ^ 2 * x * V ^ 2 * Vz * ∑ r ∈ Rset, mark (1 / 2) x a r / r := by
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    ring
  have hVnn : 0 ≤ V := mertensProduct_nonneg _
  have hVznn : 0 ≤ Vz := mertensProduct_nonneg _
  have hJ0 : 0 ≤ harmonicMass x a :=
    tsum_nonneg fun r => div_nonneg (mark_nonneg x a r) (Nat.cast_nonneg _)
  have hLpos : 0 < log x := by linarith
  have step5 : 257 * B ^ 2 * x * V ^ 2 * Vz * ∑ r ∈ Rset, mark (1 / 2) x a r / r ≤
      257 * B ^ 2 * x * V ^ 2 * (500 / log x) * harmonicMass x a := by
    have h0 : 0 ≤ 257 * B ^ 2 * x * V ^ 2 := by positivity
    calc 257 * B ^ 2 * x * V ^ 2 * Vz * ∑ r ∈ Rset, mark (1 / 2) x a r / r
        ≤ 257 * B ^ 2 * x * V ^ 2 * Vz * harmonicMass x a :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg h0 hVznn)
      _ ≤ 257 * B ^ 2 * x * V ^ 2 * (500 / log x) * harmonicMass x a := by
          apply mul_le_mul_of_nonneg_right _ hJ0
          exact mul_le_mul_of_nonneg_left hVz h0
  have step6 : 257 * B ^ 2 * x * V ^ 2 * (500 / log x) * harmonicMass x a ≤
      257 * B ^ 2 * 500 / c₁ * totalMass M c u Ψ x a * V ^ 2 := by
    have e : 257 * B ^ 2 * x * V ^ 2 * (500 / log x) * harmonicMass x a =
        (257 * B ^ 2 * 500 / c₁ * V ^ 2) * (c₁ * (x * harmonicMass x a / log x)) := by
      field_simp
    rw [e]
    have : 0 ≤ 257 * B ^ 2 * 500 / c₁ * V ^ 2 := by positivity
    calc (257 * B ^ 2 * 500 / c₁ * V ^ 2) * (c₁ * (x * harmonicMass x a / log x))
        ≤ (257 * B ^ 2 * 500 / c₁ * V ^ 2) * totalMass M c u Ψ x a :=
          mul_le_mul_of_nonneg_left hJ this
      _ = _ := by ring
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3
    _ = _ := step4
    _ ≤ _ := step5
    _ ≤ _ := step6


