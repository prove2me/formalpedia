-- Prove2me | solution 1 for ArtinPrimitiveRoots.marked_type_ii_of_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T17:25:25.789926+00:00
-- url     : https://prove2.me/submissions/3381ec9f-6376-43a0-bb01-050a577af033

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Theorems.Thm_ArtinPrimitiveRoots_square_major_replacement
import Theorems.Thm_ArtinPrimitiveRoots_major_square_bound

section
/-! # L102L: the Cauchy step of Lemma 10.2

For one dyad `Y`, the dyadic piece of the expanded marked sum is bounded, by Cauchy's inequality in
the common cofactor `h`, by `(4 H_m H_n / Y + 1) ‖Q_Y‖`, where `Q_Y = expandedSquare` ([21] (3.8)). -/

namespace ArtinPrimitiveRoots.L102L

open Real Finset

lemma one_lt_of_dyadicBump_ne_zero {t : ℝ} (h : dyadicBump t ≠ 0) : 1 < t := by
  by_contra h1
  push Not at h1
  apply h
  unfold dyadicBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

lemma labelTuples_prime {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) (i : Fin K) : (p i).Prime := by
  have := Fintype.mem_piFinset.1 hp i
  simp only [primeGroup, Finset.mem_filter] at this
  exact this.2.1

lemma labelTuples_prod_pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) : 0 < ∏ i, p i :=
  Finset.prod_pos fun i _ => (labelTuples_prime hp i).pos

lemma sum_h_single (G : ℕ → ℂ) (b k H : ℕ) (hb : 0 < b) (hk : ∀ h, k = b * h → h < H)
    (c : ℂ) :
    ∑ h ∈ range H, G h * (if k = b * h then c else 0) =
      c * (if b ∣ k then G (k / b) else 0) := by
  by_cases hdvd : b ∣ k
  · obtain ⟨h₀, rfl⟩ := hdvd
    rw [if_pos (dvd_mul_right b h₀), Nat.mul_div_cancel_left h₀ hb,
      Finset.sum_eq_single h₀]
    · simp [mul_comm]
    · intro h _ hne
      have : ¬ b * h₀ = b * h := fun e => hne (Nat.eq_of_mul_eq_mul_left hb e).symm
      simp [this]
    · intro hn
      exact absurd (Finset.mem_range.2 (hk h₀ rfl)) hn
  · rw [if_neg hdvd, mul_zero]
    apply Finset.sum_eq_zero
    intro h _
    have : ¬ k = b * h := by rintro rfl; exact hdvd (dvd_mul_right b h)
    simp [this]

open Classical in
lemma sum_h_pair (b b' k k' H : ℕ) (hb : 0 < b) (hk : ∀ h, k = b * h → h < H) (c : ℂ) :
    ∑ h ∈ range H, (if k = b * h ∧ k' = b' * h then c else 0) =
      if ∃ h : ℕ, k = b * h ∧ k' = b' * h then c else 0 := by
  split_ifs with hex
  · obtain ⟨h₀, h1, h2⟩ := hex
    rw [Finset.sum_eq_single h₀]
    · simp [h1, h2]
    · intro h _ hne
      have : ¬ (k = b * h ∧ k' = b' * h) := by
        rintro ⟨e1, -⟩
        exact hne (Nat.eq_of_mul_eq_mul_left hb (e1.symm.trans h1))
      simp [this]
    · intro hn
      exact absurd (Finset.mem_range.2 (hk h₀ h1)) hn
  · apply Finset.sum_eq_zero
    intro h _
    have : ¬ (k = b * h ∧ k' = b' * h) := fun hh => hex ⟨h, hh⟩
    simp [this]

lemma ite_mul_conj (P Q : Prop) [Decidable P] [Decidable Q] (e e' : ℂ) :
    (if P then e else 0) * (starRingEnd ℂ) (if Q then e' else 0) =
      if P ∧ Q then e * (starRingEnd ℂ) e' else 0 := by
  split_ifs <;> simp_all

/-- Cauchy's inequality in the cofactor `h`, with the square written as `expandedSquare`. -/
theorem cauchy_square {x : ℝ} {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (hY : 0 < Y)
    (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β : ℕ → ℂ) (G : ℕ → ℂ) (hG : ∀ h, ‖G h‖ ≤ 1) :
    ‖((∏ i, (groupReciprocalSum x (a i))⁻¹ : ℝ) : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
        (dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) : ℂ) * α m * β n *
          (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0)‖ ^ 2 ≤
      ((⌊4 * Hm * Hn / Y⌋₊ + 1 : ℕ) : ℝ) * ‖expandedSquare x a Y Hm Hn α β‖ := by
  classical
  set P0 : ℝ := ∏ i, (groupReciprocalSum x (a i))⁻¹ with hP0
  set H : ℕ := ⌊4 * Hm * Hn / Y⌋₊ + 1 with hH
  set M1 : ℕ := ⌊2 * Hm⌋₊ + 1 with hM1
  set N1 : ℕ := ⌊2 * Hn⌋₊ + 1 with hN1
  -- the range of the cofactor
  have hrange : ∀ p ∈ labelTuples x a, ∀ m ∈ range M1, ∀ n ∈ range N1,
      dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) ≠ 0 → ∀ h, m * n - 1 = (∏ i, p i) * h → h < H := by
    intro p hp m hm n hn hη h hh
    have hb := one_lt_of_dyadicBump_ne_zero hη
    rw [lt_div_iff₀ hY, one_mul] at hb
    have hm' : (m : ℝ) ≤ 2 * Hm :=
      (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))).trans
        (Nat.floor_le (by positivity))
    have hn' : (n : ℝ) ≤ 2 * Hn :=
      (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))).trans
        (Nat.floor_le (by positivity))
    have hle : ((∏ i, p i : ℕ) : ℝ) * h ≤ 4 * Hm * Hn := by
      have : (∏ i, p i) * h ≤ m * n := hh ▸ Nat.sub_le _ _
      calc ((∏ i, p i : ℕ) : ℝ) * h = (((∏ i, p i) * h : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((m * n : ℕ) : ℝ) := Nat.cast_le.2 this
        _ = m * n := by push_cast; ring
        _ ≤ (2 * Hm) * (2 * Hn) := mul_le_mul hm' hn' (Nat.cast_nonneg _) (by positivity)
        _ = 4 * Hm * Hn := by ring
    have hhY : (h : ℝ) ≤ 4 * Hm * Hn / Y := by
      rw [le_div_iff₀ hY]
      nlinarith [mul_le_mul_of_nonneg_left hb.le (Nat.cast_nonneg (α := ℝ) h)]
    exact Nat.lt_succ_of_le (Nat.le_floor hhY)
  -- the cofactor-indexed vector
  set t : ℕ → (Fin K → ℕ) → ℕ → ℕ → ℂ := fun h p m n =>
    if m * n - 1 = (∏ i, p i) * h then
      (dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) : ℂ) * α m * β n else 0 with ht
  set T : ℕ → ℂ := fun h => (P0 : ℂ) *
    ∑ p ∈ labelTuples x a, ∑ m ∈ range M1, ∑ n ∈ range N1, t h p m n with hT
  -- Step 1: the dyadic piece is `∑_h G h T h`
  have step1 : (P0 : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ m ∈ range M1, ∑ n ∈ range N1,
        (dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) : ℂ) * α m * β n *
          (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0) =
      ∑ h ∈ range H, G h * T h := by
    symm
    simp only [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    have e : ∀ h, G h * ((P0 : ℂ) * t h p m n) = (P0 : ℂ) * (G h * t h p m n) := fun h => by
      ring
    simp_rw [e]
    rw [← Finset.mul_sum]
    congr 1
    by_cases hη : dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) = 0
    · simp only [ht, hη, Complex.ofReal_zero, zero_mul, mul_zero, ite_self,
        Finset.sum_const_zero]
    · rw [sum_h_single G _ _ H (labelTuples_prod_pos hp) (hrange p hp m hm n hn hη)]
  -- Step 2: the expanded square is `∑_h |T h|²`
  have step3 : ∑ h ∈ range H, T h * (starRingEnd ℂ) (T h) = expandedSquare x a Y Hm Hn α β := by
    unfold expandedSquare
    have hsq : (squareNorm x a : ℂ) = (P0 : ℂ) * (P0 : ℂ) := by
      rw [squareNorm, hP0, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
      simp [sq]
    rw [hsq]
    have e1 : ∀ h, T h * (starRingEnd ℂ) (T h) = (P0 : ℂ) * (P0 : ℂ) *
        ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a, ∑ m ∈ range M1, ∑ n ∈ range N1,
          ∑ r ∈ range M1, ∑ s ∈ range N1, t h p m n * (starRingEnd ℂ) (t h p' r s) := by
      intro h
      simp only [hT, map_mul, map_sum, Complex.conj_ofReal]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun h _ => e1 h, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun s hs => ?_
    simp only [ht, ite_mul_conj]
    by_cases hη : dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) = 0
    · simp only [hη, Complex.ofReal_zero, zero_mul, ite_self, Finset.sum_const_zero]
    · rw [sum_h_pair _ _ _ _ H (labelTuples_prod_pos hp) (hrange p hp m hm n hn hη)]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
  have step2 : ‖∑ h ∈ range H, G h * T h‖ ≤ ∑ h ∈ range H, ‖T h‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hG h)
  have step4 : ‖expandedSquare x a Y Hm Hn α β‖ = ∑ h ∈ range H, ‖T h‖ ^ 2 := by
    rw [← step3]
    have : ∑ h ∈ range H, T h * (starRingEnd ℂ) (T h) =
        ((∑ h ∈ range H, ‖T h‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [this, Complex.norm_of_nonneg (Finset.sum_nonneg fun h _ => sq_nonneg _)]
  rw [step1, step4]
  calc ‖∑ h ∈ range H, G h * T h‖ ^ 2 ≤ (∑ h ∈ range H, ‖T h‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) step2 2
    _ ≤ (range H).card * ∑ h ∈ range H, ‖T h‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [Finset.card_range]

end ArtinPrimitiveRoots.L102L
end

section
/-! # L102L: expanding the mark over label tuples

For pairwise disjoint prime groups, `∏ ω_i(h) = ∑_p 1_{b(p) ∣ h}` over label tuples `p` with
`b(p) = ∏ p_i`, so the mark is `q^{ω(h)-K} ∏ V_i⁻¹ ∑_p 1_{b(p) ∣ h}`; and for `h' = b(p) h` with no
`p_i ∣ h`, `ω(h') = ω(h) + K`. -/

namespace ArtinPrimitiveRoots.L102L

open Real Finset

/-- The prime groups are pairwise disjoint (true for large `x`). -/
def GroupsDisjoint (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Prop :=
  ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

lemma mem_primeGroup_prime {y : ℝ} {P : ℕ} (hP : P ∈ primeGroup x y) : P.Prime :=
  (mem_filter.1 hP).2.1

lemma label_mem {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) (i : Fin K) :
    p i ∈ primeGroup x (a i) :=
  Fintype.mem_piFinset.1 hp i

lemma label_eq_of_dvd (hd : GroupsDisjoint x a) {p : Fin K → ℕ} (hp : p ∈ labelTuples x a)
    {P : ℕ} (i : Fin K) (hP : P ∈ primeGroup x (a i)) (hdvd : P ∣ ∏ j, p j) : P = p i := by
  have hPp : P.Prime := mem_primeGroup_prime hP
  obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hPp.prime _).1 hdvd
  have hPj : P = p j := (Nat.prime_dvd_prime_iff_eq hPp (labelTuples_prime hp j)).1 hj
  by_cases hij : i = j
  · subst hij; exact hPj
  · exact absurd (hPj ▸ label_mem hp j) (Finset.disjoint_left.1 (hd i j hij) hP)

lemma label_dvd_iff (hd : GroupsDisjoint x a) {p : Fin K → ℕ} (hp : p ∈ labelTuples x a)
    (h : ℕ) : (∏ i, p i) ∣ h ↔ ∀ i, p i ∣ h := by
  classical
  constructor
  · intro hb i
    exact (Finset.dvd_prod_of_mem p (mem_univ i)).trans hb
  · intro hall
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact Finset.disjoint_left.1 (hd i j hne) (label_mem hp i) (hij ▸ label_mem hp j)
    have e : ∏ P ∈ univ.image p, P = ∏ i, p i := Finset.prod_image fun i _ j _ e => hinj e
    rw [← e]
    apply Finset.prod_primes_dvd
    · intro P hP
      obtain ⟨i, -, rfl⟩ := mem_image.1 hP
      exact (labelTuples_prime hp i).prime
    · intro P hP
      obtain ⟨i, -, rfl⟩ := mem_image.1 hP
      exact hall i

lemma prod_groupOmega (hd : GroupsDisjoint x a) (h : ℕ) :
    (∏ i, (groupOmega x (a i) h : ℝ)) =
      ∑ p ∈ labelTuples x a, if (∏ i, p i) ∣ h then (1 : ℝ) else 0 := by
  classical
  have e1 : ∀ i, (groupOmega x (a i) h : ℝ) =
      ∑ P ∈ primeGroup x (a i), if P ∣ h then (1 : ℝ) else 0 := by
    intro i
    rw [groupOmega, Finset.natCast_card_filter]
  simp_rw [e1]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.prod_boole]
  simp only [mem_univ, true_implies]
  exact if_congr (label_dvd_iff hd hp h).symm rfl rfl

/-- The mark expanded over label tuples. -/
lemma mark_eq (hd : GroupsDisjoint x a) (q : ℝ) (h : ℕ) :
    mark q x a h = q ^ ((markOmega x a h : ℤ) - K) * (∏ i, (groupReciprocalSum x (a i))⁻¹) *
      ∑ p ∈ labelTuples x a, if (∏ i, p i) ∣ h then (1 : ℝ) else 0 := by
  rw [mark, ← prod_groupOmega hd, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, mul_comm]

lemma groupOmega_label_mul (hd : GroupsDisjoint x a) {p : Fin K → ℕ} (hp : p ∈ labelTuples x a)
    (h : ℕ) (i : Fin K) (hi : ¬ p i ∣ h) :
    groupOmega x (a i) ((∏ j, p j) * h) = groupOmega x (a i) h + 1 := by
  classical
  unfold groupOmega
  have : (primeGroup x (a i)).filter (· ∣ (∏ j, p j) * h) =
      insert (p i) ((primeGroup x (a i)).filter (· ∣ h)) := by
    ext P
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hP, hdvd⟩
      rcases (Nat.Prime.dvd_mul (mem_primeGroup_prime hP)).1 hdvd with h1 | h1
      · exact Or.inl (label_eq_of_dvd hd hp i hP h1)
      · exact Or.inr ⟨hP, h1⟩
    · rintro (rfl | ⟨hP, h1⟩)
      · exact ⟨label_mem hp i,
          dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem p (mem_univ i)) _⟩
      · exact ⟨hP, dvd_mul_of_dvd_right h1 _⟩
  rw [this, card_insert_of_notMem]
  simp [hi]

lemma markOmega_label_mul (hd : GroupsDisjoint x a) {p : Fin K → ℕ} (hp : p ∈ labelTuples x a)
    (h : ℕ) (hi : ∀ i, ¬ p i ∣ h) :
    markOmega x a ((∏ j, p j) * h) = markOmega x a h + K := by
  unfold markOmega
  simp_rw [groupOmega_label_mul hd hp h _ (hi _)]
  rw [Finset.sum_add_distrib]
  simp

lemma le_markOmega {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) {h : ℕ}
    (hdvd : (∏ j, p j) ∣ h) : K ≤ markOmega x a h := by
  unfold markOmega groupOmega
  calc K = ∑ _i : Fin K, 1 := by simp
    _ ≤ ∑ i, ((primeGroup x (a i)).filter (· ∣ h)).card := Finset.sum_le_sum fun i _ =>
      Finset.card_pos.2
      ⟨p i, mem_filter.2 ⟨label_mem hp i, (dvd_prod_of_mem p (mem_univ i)).trans hdvd⟩⟩

lemma F_label_mul (F : ℕ → ℂ) (hF : ∀ h, 0 < h → ∀ P ∈ groupPrimes x a, F (P * h) = F h)
    {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) (h : ℕ) (hh : 0 < h) :
    F ((∏ i, p i) * h) = F h := by
  classical
  have key : ∀ s : Finset (Fin K), F ((∏ i ∈ s, p i) * h) = F h := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, mul_assoc,
        hF _ (Nat.mul_pos (Finset.prod_pos fun i _ => (labelTuples_prime hp i).pos) hh) _
          (by simp only [groupPrimes]; exact Finset.mem_biUnion.2 ⟨j, mem_univ j, label_mem hp j⟩),
        ih]
  exact key univ

/-- At most `N/d + 1` integers `n ≤ N` satisfy `m n ≡ 1 (mod d)`. -/
lemma card_dvd_sub_one (d m N : ℕ) :
    ((range (N + 1)).filter (fun n => 1 ≤ m * n ∧ d ∣ m * n - 1)).card ≤ N / d + 1 := by
  rw [← Finset.card_range (N / d + 1)]
  apply Finset.card_le_card_of_injOn (fun n => n / d)
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.1 hn.1))
  · intro n₁ h₁ n₂ h₂ he
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at h₁ h₂
    have c1 : m * n₁ ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' h₁.2.1).2 h₁.2.2).symm
    have c2 : m * n₂ ≡ 1 [MOD d] := ((Nat.modEq_iff_dvd' h₂.2.1).2 h₂.2.2).symm
    have hcop : Nat.Coprime m d := Nat.coprime_of_mul_modEq_one n₁ c1
    have hmod : n₁ ≡ n₂ [MOD d] :=
      Nat.ModEq.cancel_left_of_coprime hcop.symm (c1.trans c2.symm)
    simp only at he
    rw [← Nat.div_add_mod n₁ d, ← Nat.div_add_mod n₂ d, he, hmod]

end ArtinPrimitiveRoots.L102L
end

section
/-! # L102L: replacing the damping `q^{ω(mn-1)-K}` by `q^{ω(h)}`, [21] (3.6)

After the mark expansion, a term with `mn - 1 = b(p) h` changes only when some selected prime
`p_i` divides `h`, i.e. `b(p) p_i ∣ mn - 1`; those pairs are counted directly. -/

namespace ArtinPrimitiveRoots.L102L

open Real Finset

/-- The damped twist `G(h) = F(h) q^{ω(h)}` (and `G(0) = 0`). -/
noncomputable def damped (q x : ℝ) {K : ℕ} (a : Fin K → ℝ) (F : ℕ → ℂ) (h : ℕ) : ℂ :=
  if h = 0 then 0 else F h * ((q ^ markOmega x a h : ℝ) : ℂ)

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

lemma norm_damped_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (F : ℕ → ℂ)
    (hFb : ∀ h, 0 < h → ‖F h‖ ≤ 1) (h : ℕ) : ‖damped q x a F h‖ ≤ 1 := by
  unfold damped
  split_ifs with h0
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hq0 _)]
    exact mul_le_one₀ (hFb h (Nat.pos_of_ne_zero h0)) (by positivity)
      (pow_le_one₀ hq0.le hq1.le)

lemma groupReciprocalSum_nonneg (x y : ℝ) : 0 ≤ groupReciprocalSum x y :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma P0_nonneg : 0 ≤ ∏ i, (groupReciprocalSum x (a i))⁻¹ :=
  Finset.prod_nonneg fun _i _ => inv_nonneg.2 (groupReciprocalSum_nonneg _ _)

lemma sum_label_inv :
    ∑ p ∈ labelTuples x a, (1 / ((∏ i, p i : ℕ) : ℝ)) = ∏ i, groupReciprocalSum x (a i) := by
  classical
  unfold labelTuples groupReciprocalSum
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  rw [one_div, ← Finset.prod_inv_distrib]
  simp [one_div]

lemma P0_mul_sum_label_inv_le :
    (∏ i, (groupReciprocalSum x (a i))⁻¹) * ∑ p ∈ labelTuples x a, (1 / ((∏ i, p i : ℕ) : ℝ))
      ≤ 1 := by
  rw [sum_label_inv, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_one
  · intro i _
    exact mul_nonneg (inv_nonneg.2 (groupReciprocalSum_nonneg _ _))
      (groupReciprocalSum_nonneg _ _)
  · intro i _
    by_cases hV : groupReciprocalSum x (a i) = 0
    · simp [hV]
    · rw [inv_mul_cancel₀ hV]

/-- The pointwise damping change for one label tuple. -/
lemma label_diff_le (hd : GroupsDisjoint x a) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (F : ℕ → ℂ) (hFb : ∀ h, 0 < h → ‖F h‖ ≤ 1)
    (hFi : ∀ h, 0 < h → ∀ P ∈ groupPrimes x a, F (P * h) = F h)
    {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) (h' : ℕ) (hh' : 1 ≤ h') :
    ‖(if (∏ i, p i) ∣ h' then F h' * ((q ^ ((markOmega x a h' : ℤ) - K) : ℝ) : ℂ) else 0) -
        (if (∏ i, p i) ∣ h' then damped q x a F (h' / ∏ i, p i) else 0)‖ ≤
      ∑ i, (if (∏ j, p j) * p i ∣ h' then (1 : ℝ) else 0) := by
  have hnn : 0 ≤ ∑ i, (if (∏ j, p j) * p i ∣ h' then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  by_cases hb : (∏ i, p i) ∣ h'
  swap
  · simp [hb]
  obtain ⟨h, rfl⟩ := hb
  have hbpos := labelTuples_prod_pos hp
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp at hh'
    · exact h0
  rw [if_pos (dvd_mul_right _ _), if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left h hbpos,
    damped, if_neg hh.ne', F_label_mul F hFi hp h hh]
  by_cases hall : ∀ i, ¬ p i ∣ h
  · rw [markOmega_label_mul hd hp h hall]
    have : ((markOmega x a h + K : ℕ) : ℤ) - K = (markOmega x a h : ℕ) := by push_cast; ring
    rw [this, zpow_natCast, sub_self, norm_zero]
    exact hnn
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have h1 : (1 : ℝ) ≤ ∑ i, (if (∏ j, p j) * p i ∣ (∏ j, p j) * h then (1 : ℝ) else 0) := by
      have := Finset.single_le_sum (f := fun i => if (∏ j, p j) * p i ∣ (∏ j, p j) * h
        then (1 : ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
      simp only [if_pos (mul_dvd_mul_left _ hi)] at this
      exact this
    refine le_trans ?_ h1
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hK : (0 : ℤ) ≤ (markOmega x a ((∏ i, p i) * h) : ℤ) - K := by
      have := le_markOmega hp (dvd_mul_right (∏ i, p i) h)
      omega
    refine mul_le_one₀ (hFb h hh) (abs_nonneg _) (abs_sub_le_of_nonneg_of_le
      (zpow_nonneg hq0.le _) (zpow_le_one₀ hq0 hq1.le hK) (pow_nonneg hq0.le _)
      (pow_le_one₀ hq0.le hq1.le))

lemma swap3 {ι : Type*} (s : Finset ι) (A B : Finset ℕ) (c : ℂ) (f : ι → ℕ → ℕ → ℂ) :
    c * ∑ p ∈ s, ∑ m ∈ A, ∑ n ∈ B, f p m n = ∑ m ∈ A, ∑ n ∈ B, c * ∑ p ∈ s, f p m n := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_comm

lemma swap4 {ι κ : Type*} (A B : Finset ℕ) (s : Finset ι) (t : Finset κ)
    (g : ι → κ → ℕ → ℕ → ℝ) :
    ∑ m ∈ A, ∑ n ∈ B, ∑ p ∈ s, ∑ i ∈ t, g p i m n =
      ∑ p ∈ s, ∑ i ∈ t, ∑ m ∈ A, ∑ n ∈ B, g p i m n := by
  calc _ = ∑ m ∈ A, ∑ p ∈ s, ∑ n ∈ B, ∑ i ∈ t, g p i m n :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ m ∈ A, ∑ n ∈ B, ∑ i ∈ t, g p i m n := Finset.sum_comm
    _ = ∑ p ∈ s, ∑ m ∈ A, ∑ i ∈ t, ∑ n ∈ B, g p i m n :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- [21] (3.6): replacing the damping costs at most the count of pairs with `b(p) p_i ∣ mn - 1`. -/
theorem damping (hd : GroupsDisjoint x a) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (F : ℕ → ℂ) (hFb : ∀ h, 0 < h → ‖F h‖ ≤ 1)
    (hFi : ∀ h, 0 < h → ∀ P ∈ groupPrimes x a, F (P * h) = F h)
    (α β : ℕ → ℂ) (Ca Cb : ℝ) (hα : ∀ m, ‖α m‖ ≤ Ca) (hβ : ∀ n, ‖β n‖ ≤ Cb)
    (hsupp : ∀ m n, α m ≠ 0 → β n ≠ 0 → 2 ≤ m * n) (M N : ℕ)
    (Pmin Pmax : ℝ) (hPmin : 0 < Pmin) (hPmax : 0 ≤ Pmax)
    (hP : ∀ i, ∀ P ∈ primeGroup x (a i), Pmin ≤ (P : ℝ) ∧ (P : ℝ) ≤ Pmax) :
    ‖∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
        α m * β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ) -
      ((∏ i, (groupReciprocalSum x (a i))⁻¹ : ℝ) : ℂ) *
        ∑ p ∈ labelTuples x a, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
          α m * β n * (if (∏ i, p i) ∣ m * n - 1 then damped q x a F ((m * n - 1) / ∏ i, p i)
            else 0)‖ ≤
      Ca * Cb * ((M + 1) * K * (N / Pmin + Pmax ^ K)) := by
  classical
  set P0 : ℝ := ∏ i, (groupReciprocalSum x (a i))⁻¹ with hP0
  have hP0nn : 0 ≤ P0 := P0_nonneg
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (hα 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hβ 0)
  set ind : (Fin K → ℕ) → Fin K → ℕ → ℕ → ℝ := fun p i m n =>
    if 1 ≤ m * n ∧ (∏ j, p j) * p i ∣ m * n - 1 then 1 else 0 with hind
  have ind_nn : ∀ p i m n, 0 ≤ ind p i m n := fun p i m n => by
    simp only [hind]; split_ifs <;> norm_num
  -- the pointwise bound
  have pt : ∀ m n, ‖α m * β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ) -
      (P0 : ℂ) * ∑ p ∈ labelTuples x a, α m * β n *
        (if (∏ i, p i) ∣ m * n - 1 then damped q x a F ((m * n - 1) / ∏ i, p i) else 0)‖ ≤
      Ca * Cb * (P0 * ∑ p ∈ labelTuples x a, ∑ i, ind p i m n) := by
    intro m n
    have rhs_nn : 0 ≤ Ca * Cb * (P0 * ∑ p ∈ labelTuples x a, ∑ i, ind p i m n) :=
      mul_nonneg (mul_nonneg hCa hCb) (mul_nonneg hP0nn
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => ind_nn p i m n))
    by_cases hab : α m = 0 ∨ β n = 0
    · rcases hab with h0 | h0 <;> simpa [h0] using rhs_nn
    push Not at hab
    have hmn := hsupp m n hab.1 hab.2
    have hmn1 : 1 ≤ m * n := by omega
    have eX : α m * β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ) =
        (P0 : ℂ) * ∑ p ∈ labelTuples x a, α m * β n *
          (if (∏ i, p i) ∣ m * n - 1 then
            F (m * n - 1) * ((q ^ ((markOmega x a (m * n - 1) : ℤ) - K) : ℝ) : ℂ) else 0) := by
      rw [mark_eq hd, ← hP0]
      simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs
      · simp; ring
      · simp
    rw [eX, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hP0nn, mul_left_comm (Ca * Cb)]
    apply mul_le_mul_of_nonneg_left _ hP0nn
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [← mul_sub, norm_mul, norm_mul]
    have hl := label_diff_le hd q hq0 hq1 F hFb hFi hp (m * n - 1) (by omega)
    have e : ∑ i, (if (∏ j, p j) * p i ∣ m * n - 1 then (1 : ℝ) else 0) = ∑ i, ind p i m n := by
      simp only [hind, hmn1, true_and]
    rw [e] at hl
    calc ‖α m‖ * ‖β n‖ * _ ≤ Ca * Cb * ∑ i, ind p i m n :=
          mul_le_mul (mul_le_mul (hα m) (hβ n) (norm_nonneg _) hCa) hl (norm_nonneg _)
            (mul_nonneg hCa hCb)
      _ = _ := by ring
  -- sum the pointwise bound
  rw [swap3, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum (g := fun m =>
    ∑ n ∈ range (N + 1), Ca * Cb * (P0 * ∑ p ∈ labelTuples x a, ∑ i, ind p i m n))
      fun m _ => ?_) ?_)
  · rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => pt m n)
  have e : ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
      Ca * Cb * (P0 * ∑ p ∈ labelTuples x a, ∑ i, ind p i m n) =
      Ca * Cb * (P0 * ∑ p ∈ labelTuples x a, ∑ i, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
        ind p i m n) := by
    rw [← swap4]
    simp only [Finset.mul_sum]
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCa hCb)
  have hE : 0 ≤ ((M : ℝ) + 1) * K * (N / Pmin + Pmax ^ K) := by
    positivity
  have hcount : ∀ p ∈ labelTuples x a, ∑ i, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
      ind p i m n ≤ ((M : ℝ) + 1) * K * (N / Pmin + Pmax ^ K) * (1 / ((∏ i, p i : ℕ) : ℝ)) := by
    intro p hp
    have hb : (0 : ℝ) < ((∏ i, p i : ℕ) : ℝ) := Nat.cast_pos.2 (labelTuples_prod_pos hp)
    have hbP : ((∏ i, p i : ℕ) : ℝ) ≤ Pmax ^ K := by
      rw [Nat.cast_prod]
      calc ∏ i, ((p i : ℕ) : ℝ) ≤ ∏ _i : Fin K, Pmax :=
            Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
              (fun i _ => (hP i (p i) (label_mem hp i)).2)
        _ = Pmax ^ K := by simp
    have hi : ∀ i, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1), ind p i m n ≤
        ((M : ℝ) + 1) * (N / Pmin + Pmax ^ K) * (1 / ((∏ i, p i : ℕ) : ℝ)) := by
      intro i
      have hpi : Pmin ≤ (p i : ℝ) := (hP i (p i) (label_mem hp i)).1
      have hn : ∀ m, ∑ n ∈ range (N + 1), ind p i m n ≤
          (N : ℝ) / (((∏ i, p i : ℕ) : ℝ) * (p i : ℝ)) + 1 := by
        intro m
        have h1 : ∑ n ∈ range (N + 1), ind p i m n =
            (((range (N + 1)).filter (fun n => 1 ≤ m * n ∧ (∏ j, p j) * p i ∣ m * n - 1)).card
              : ℝ) := by
          simp only [hind]
          rw [Finset.sum_boole]
        rw [h1]
        refine (Nat.cast_le.2 (card_dvd_sub_one _ m N)).trans ?_
        push_cast
        gcongr
        exact_mod_cast Nat.cast_div_le
      calc ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1), ind p i m n ≤
            ∑ _m ∈ range (M + 1), ((N : ℝ) / (((∏ i, p i : ℕ) : ℝ) * (p i : ℝ)) + 1) :=
            Finset.sum_le_sum fun m _ => hn m
        _ = ((M : ℝ) + 1) * ((N : ℝ) / (((∏ i, p i : ℕ) : ℝ) * (p i : ℝ)) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ ((M : ℝ) + 1) * (N / Pmin + Pmax ^ K) * (1 / ((∏ i, p i : ℕ) : ℝ)) := by
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [add_mul]
            apply add_le_add
            · rw [div_mul_div_comm, mul_one, mul_comm Pmin]
              exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hb hPmin)
                (mul_le_mul_of_nonneg_left hpi hb.le)
            · rw [← div_eq_mul_one_div, le_div_iff₀ hb, one_mul]
              exact hbP
    calc ∑ i, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1), ind p i m n ≤
          ∑ _i : Fin K, ((M : ℝ) + 1) * (N / Pmin + Pmax ^ K) * (1 / ((∏ i, p i : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = _ := by simp; ring
  calc P0 * ∑ p ∈ labelTuples x a, ∑ i, ∑ m ∈ range (M + 1), ∑ n ∈ range (N + 1),
        ind p i m n ≤ P0 * ∑ p ∈ labelTuples x a,
          ((M : ℝ) + 1) * K * (N / Pmin + Pmax ^ K) * (1 / ((∏ i, p i : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcount) hP0nn
    _ = ((M : ℝ) + 1) * K * (N / Pmin + Pmax ^ K) *
          (P0 * ∑ p ∈ labelTuples x a, (1 / ((∏ i, p i : ℕ) : ℝ))) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((M : ℝ) + 1) * K * (N / Pmin + Pmax ^ K) * 1 :=
        mul_le_mul_of_nonneg_left P0_mul_sum_label_inv_le hE
    _ = _ := mul_one _

end ArtinPrimitiveRoots.L102L
end

section
/-! # L102L: the dyadic split of the label product and the bound for the main term -/

namespace ArtinPrimitiveRoots.L102L

open Real Finset

/-- The dyadic partition telescopes: `∑_{j ≤ J} η(t/2^j) = 1` for `2 ≤ t ≤ 2^{J+1}`. -/
lemma sum_dyadicBump (t : ℝ) (J : ℕ) (h2 : 2 ≤ t) (hJ : t ≤ 2 ^ (J + 1)) :
    ∑ j ∈ range (J + 1), dyadicBump (t / 2 ^ j) = 1 := by
  have key : ∀ j : ℕ, dyadicBump (t / 2 ^ j) =
      Real.smoothTransition (t / 2 ^ j - 1) - Real.smoothTransition (t / 2 ^ (j + 1) - 1) := by
    intro j; unfold dyadicBump; rw [pow_succ, div_div]
  simp_rw [key]
  rw [Finset.sum_range_sub' (fun j => Real.smoothTransition (t / 2 ^ j - 1))]
  have h1 : t / 2 ^ (J + 1) ≤ 1 := (div_le_one (by positivity)).2 hJ
  rw [pow_zero, div_one, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

lemma label_prod_le {Pmax : ℝ} (hP : ∀ i, ∀ P ∈ primeGroup x (a i), (P : ℝ) ≤ Pmax)
    {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) : ((∏ i, p i : ℕ) : ℝ) ≤ Pmax ^ K := by
  rw [Nat.cast_prod]
  calc ∏ i, ((p i : ℕ) : ℝ) ≤ ∏ _i : Fin K, Pmax :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hP i (p i) (label_mem hp i))
    _ = Pmax ^ K := by simp

lemma two_le_label_prod (hK : 1 ≤ K) {p : Fin K → ℕ} (hp : p ∈ labelTuples x a) :
    2 ≤ ∏ i, p i := by
  have i0 : Fin K := ⟨0, hK⟩
  calc 2 ≤ p i0 := (labelTuples_prime hp i0).two_le
    _ ≤ ∏ i, p i := Finset.single_le_prod' (fun i _ => (labelTuples_prime hp i).one_lt.le)
      (Finset.mem_univ i0)

/-- Inserting `1 = ∑_j η(b/2^j)` splits the main term into dyads. -/
lemma main_split (P0 Hm Hn : ℝ) (α β G : ℕ → ℂ) (J : ℕ)
    (hb : ∀ p ∈ labelTuples x a, 2 ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 ^ (J + 1)) :
    (P0 : ℂ) * ∑ p ∈ labelTuples x a, ∑ m ∈ range (⌊2 * Hm⌋₊ + 1),
        ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
          α m * β n * (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0) =
      ∑ j ∈ range (J + 1), (P0 : ℂ) * ∑ p ∈ labelTuples x a, ∑ m ∈ range (⌊2 * Hm⌋₊ + 1),
        ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
          (dyadicBump (((∏ i, p i : ℕ) : ℝ) / 2 ^ j) : ℂ) * α m * β n *
            (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0) := by
  rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : ∑ j ∈ range (J + 1), (dyadicBump (((∏ i, p i : ℕ) : ℝ) / 2 ^ j) : ℂ) = 1 := by
    exact_mod_cast sum_dyadicBump _ J (hb p hp).1 (hb p hp).2
  calc _ = ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
        (∑ j ∈ range (J + 1), (dyadicBump (((∏ i, p i : ℕ) : ℝ) / 2 ^ j) : ℂ)) * α m * β n *
          (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0) := by
        rw [h1]; simp only [one_mul]
    _ = _ := by
        simp_rw [Finset.sum_mul]
        symm
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm

/-- One dyadic piece: Cauchy plus a bound for the expanded square. -/
lemma piece_sq_le (Y Hm Hn c w : ℝ) (hY : 0 < Y) (hYX : Y ≤ Hm * Hn) (hHm : 0 ≤ Hm)
    (hHn : 0 ≤ Hn) (α β G : ℕ → ℂ) (hG : ∀ h, ‖G h‖ ≤ 1)
    (hQ : ‖expandedSquare x a Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * w)) :
    ‖((∏ i, (groupReciprocalSum x (a i))⁻¹ : ℝ) : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
        (dyadicBump (((∏ i, p i : ℕ) : ℝ) / Y) : ℂ) * α m * β n *
          (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0)‖ ^ 2 ≤
      5 * (c * w) * (Hm * Hn) ^ 2 := by
  have hc := cauchy_square (x := x) a Y Hm Hn hY hHm hHn α β G hG
  have hX : 0 < Hm * Hn := hY.trans_le hYX
  have hfl : ((⌊4 * Hm * Hn / Y⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * Hm * Hn / Y + 1 := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 4 * Hm * Hn / Y by positivity)
    linarith
  have hcw : 0 ≤ c * w := by
    have h0 : 0 ≤ c * (Hm * Hn * Y * w) := (norm_nonneg _).trans hQ
    have : c * (Hm * Hn * Y * w) = (c * w) * (Hm * Hn * Y) := by ring
    rw [this] at h0
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  calc _ ≤ ((⌊4 * Hm * Hn / Y⌋₊ + 1 : ℕ) : ℝ) * ‖expandedSquare x a Y Hm Hn α β‖ := hc
    _ ≤ (4 * Hm * Hn / Y + 1) * (c * (Hm * Hn * Y * w)) :=
        mul_le_mul hfl hQ (norm_nonneg _) (by positivity)
    _ = (c * w) * (4 * (Hm * Hn) ^ 2 + (Hm * Hn) * Y) := by field_simp
    _ ≤ (c * w) * (5 * (Hm * Hn) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hcw
        nlinarith
    _ = 5 * (c * w) * (Hm * Hn) ^ 2 := by ring

/-- The main term, summed over the dyads. -/
lemma main_bound (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β G : ℕ → ℂ)
    (hG : ∀ h, ‖G h‖ ≤ 1) (J : ℕ)
    (hb : ∀ p ∈ labelTuples x a, 2 ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 ^ (J + 1))
    (c w B : ℝ) (hB : 0 ≤ B) (hB2 : 5 * (c * w) * (Hm * Hn) ^ 2 ≤ B ^ 2)
    (hQ : ∀ j ∈ range (J + 1), (2 : ℝ) ^ j ≤ Hm * Hn ∧
      ‖expandedSquare x a (2 ^ j) Hm Hn α β‖ ≤ c * (Hm * Hn * 2 ^ j * w)) :
    ‖((∏ i, (groupReciprocalSum x (a i))⁻¹ : ℝ) : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
        α m * β n * (if (∏ i, p i) ∣ m * n - 1 then G ((m * n - 1) / ∏ i, p i) else 0)‖ ≤
      (J + 1) * B := by
  rw [main_split _ Hm Hn α β G J hb]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _j ∈ range (J + 1), B := Finset.sum_le_sum fun j hj => by
        have hsq := piece_sq_le (2 ^ j) Hm Hn c w (by positivity) (hQ j hj).1 hHm hHn α β G hG
          (hQ j hj).2
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).1 (hsq.trans hB2)
    _ = (J + 1) * B := by simp

end ArtinPrimitiveRoots.L102L
end

section
/-! # L102L: the large-`x` facts used in Lemma 10.2 -/

namespace ArtinPrimitiveRoots.L102L

open Real Filter

/-- `c u^s ≤ exp(b u)` for large `u`. -/
lemma ev_rpow_le_exp (s c b : ℝ) (hb : 0 < b) : ∀ᶠ u in atTop, c * u ^ s ≤ exp (b * u) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (|c| + 1) by positivity))
  filter_upwards [h, eventually_ge_atTop 0] with u hu hu0
  have hus : 0 ≤ u ^ s := rpow_nonneg hu0 s
  have e : u ^ s * exp (-b * u) * exp (b * u) = u ^ s := by
    rw [mul_assoc, ← exp_add]; simp
  have h1 : u ^ s * (|c| + 1) ≤ exp (b * u) := by
    calc u ^ s * (|c| + 1) = (u ^ s * exp (-b * u)) * (|c| + 1) * exp (b * u) := by
          rw [mul_right_comm, e]
      _ ≤ (1 / (|c| + 1)) * (|c| + 1) * exp (b * u) := by gcongr
      _ = exp (b * u) := by field_simp
  calc c * u ^ s ≤ (|c| + 1) * u ^ s :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hus
    _ ≤ exp (b * u) := by linarith

/-- `c L^{0.2} ≤ b L` for large `L`. -/
lemma ev_small_rpow (c b : ℝ) (hb : 0 < b) : ∀ᶠ L in atTop, c * L ^ (0.2 : ℝ) ≤ b * L := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 0.8 by norm_num)).eventually
    (eventually_ge_atTop (c / b)), eventually_gt_atTop 0] with L hL hL0
  have h1 : c ≤ b * L ^ (0.8 : ℝ) := by
    rw [div_le_iff₀ hb] at hL; linarith
  calc c * L ^ (0.2 : ℝ) ≤ (b * L ^ (0.8 : ℝ)) * L ^ (0.2 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (rpow_nonneg hL0.le _)
    _ = b * L := by rw [mul_assoc, ← rpow_add hL0]; norm_num

/-- The analytic thresholds of the reduction. -/
lemma eventually_bounds (δ E c₁ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (K : ℕ) :
    ∀ᶠ x in atTop, 1 < x ∧ 1 ≤ log x ∧ exp (2 * K * log x ^ (0.2 : ℝ)) ≤ c₁ * x ∧
      6 * K * log x ^ E ≤ exp (log x ^ (0.1 : ℝ)) ∧
      3 * K * log x ^ E * exp (2 * K * log x ^ (0.2 : ℝ)) ≤ x ^ δ := by
  have hL : ∀ᶠ L in atTop, 1 ≤ L ∧ 2 * K * L ^ (0.2 : ℝ) ≤ L + log c₁ ∧
      6 * K * L ^ E ≤ exp (L ^ (0.1 : ℝ)) ∧
      3 * K * L ^ E * exp (2 * K * L ^ (0.2 : ℝ)) ≤ exp (δ * L) := by
    have h3 : ∀ᶠ L in atTop, 6 * K * (L ^ (0.1 : ℝ)) ^ (10 * E) ≤ exp (1 * L ^ (0.1 : ℝ)) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.1)).eventually
        (ev_rpow_le_exp (10 * E) (6 * K) 1 one_pos)
    filter_upwards [eventually_ge_atTop 1, ev_small_rpow (2 * K) (1 / 2) (by norm_num),
      eventually_ge_atTop (-2 * log c₁), h3, ev_rpow_le_exp E (3 * K) (δ / 2) (by positivity),
      ev_small_rpow (2 * K) (δ / 2) (by positivity)] with L h1 h2 h2' h3 h4 h5
    refine ⟨h1, by linarith, ?_, ?_⟩
    · rw [← rpow_mul (by linarith), one_mul] at h3
      convert h3 using 3
      ring_nf
    · calc 3 * K * L ^ E * exp (2 * K * L ^ (0.2 : ℝ)) ≤ exp (δ / 2 * L) * exp (δ / 2 * L) :=
            mul_le_mul h4 (exp_le_exp.2 h5) (exp_pos _).le (exp_pos _).le
        _ = exp (δ * L) := by rw [← exp_add]; ring_nf
  filter_upwards [tendsto_log_atTop.eventually hL, eventually_gt_atTop 1] with x hx hx1
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hx0 : 0 < x := by linarith
  refine ⟨hx1, h1, ?_, h3, ?_⟩
  · calc exp (2 * K * log x ^ (0.2 : ℝ)) ≤ exp (log x + log c₁) := exp_le_exp.2 h2
      _ = c₁ * x := by rw [exp_add, exp_log hx0, exp_log hc₁]; ring
  · rwa [rpow_def_of_pos hx0, mul_comm (log x)]

lemma disjoint_of_lt {x s t : ℝ} (h : 2 * log x ^ s < log x ^ t) :
    Disjoint (primeGroup x s) (primeGroup x t) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  simp only [primeGroup, Finset.mem_filter, Finset.mem_range] at hP hP'
  have h1 : (P : ℝ) ≤ exp (2 * log x ^ s) :=
    (Nat.cast_le.2 (Nat.lt_succ_iff.1 hP.1)).trans (Nat.floor_le (exp_pos _).le)
  linarith [exp_lt_exp.2 h, hP'.2.2]

lemma eventually_groupsDisjoint {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a) :
    ∀ᶠ x in atTop, GroupsDisjoint x a := by
  have key : ∀ i j : Fin K, a i < a j →
      ∀ᶠ x in atTop, 2 * log x ^ (a i) < log x ^ (a j) := by
    intro i j hij
    have := (tendsto_rpow_atTop (sub_pos.2 hij)).eventually (eventually_gt_atTop (2 : ℝ))
    filter_upwards [tendsto_log_atTop.eventually this,
      tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hx hx0
    have e : log x ^ (a j) = log x ^ (a i) * log x ^ (a j - a i) := by
      rw [← rpow_add hx0]; ring_nf
    rw [e]
    nlinarith [rpow_pos_of_pos hx0 (a i)]
  have hall : ∀ᶠ x in atTop, ∀ i j : Fin K, a i < a j → 2 * log x ^ (a i) < log x ^ (a j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    by_cases hij : a i < a j
    · filter_upwards [key i j hij] with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hij
  filter_upwards [hall] with x hx
  intro i j hne
  rcases lt_or_gt_of_ne (ha.injective.ne hne) with h | h
  · exact disjoint_of_lt (hx i j h)
  · exact (disjoint_of_lt (hx j i h)).symm

lemma primeGroup_bounds {x y : ℝ} (hL : 1 ≤ log x) (hy : 0.1 < y ∧ y < 0.2) {P : ℕ}
    (hP : P ∈ primeGroup x y) :
    exp (log x ^ (0.1 : ℝ)) ≤ P ∧ (P : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) := by
  simp only [primeGroup, Finset.mem_filter, Finset.mem_range] at hP
  constructor
  · exact (exp_le_exp.2 (rpow_le_rpow_of_exponent_le hL hy.1.le)).trans hP.2.2
  · refine (Nat.cast_le.2 (Nat.lt_succ_iff.1 hP.1)).trans
      ((Nat.floor_le (exp_pos _).le).trans (exp_le_exp.2 ?_))
    linarith [rpow_le_rpow_of_exponent_le hL hy.2.le]

end ArtinPrimitiveRoots.L102L
end

section
/-! # L102L: Lemma 10.2 from (10.9) and (10.10)

[21] §3.1 and "Completion of Theorem 3.1": expand the mark over label tuples, replace the damping
((3.6), `damping`), split the label product into dyads, apply Cauchy in the cofactor
(`cauchy_square`), and bound each expanded square by (10.9) + (10.10). -/

namespace ArtinPrimitiveRoots

open Real Finset L102L

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real Finset L102L
theorem solution (δ C Dstar q : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hD : 0 < Dstar) (hq0 : 0 < q) (hq1 : q < 1) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (S : Set (ℝ × ℝ × ℝ × (ℕ → ℂ) × (ℕ → ℂ)))
    (hS : ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S →
      x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
      (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
        ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) ∧
      (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
      (∀ m, ‖α m‖ ≤ log x ^ C) ∧ (∀ n, ‖β n‖ ≤ log x ^ C))
    (hα : ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
        ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * log x ^ B →
          ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
              α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A)) :
    ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ A : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
      ∀ F : ℕ → ℂ, (∀ h, 0 < h → ‖F h‖ ≤ 1) →
        (∀ h, 0 < h → ∀ p ∈ groupPrimes x a, F (p * h) = F h) →
      ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
          α m * β n * F (m * n - 1) * (mark q x a (m * n - 1) : ℂ)‖ ≤
        A * (Hm * Hn) * log x ^ (-Dstar) := by
  classical
  have hD1 : 0 < (Dstar + 1) + (Dstar + 1) := by linarith
  obtain ⟨A₀, hA₀, K₀, hrep⟩ := square_major_replacement δ C c₁ c₂ hδ hC hc₁ _ hD1
  refine ⟨K₀, fun K hK1 hK0 a ha_mono ha_range => ?_⟩
  obtain ⟨c_r, x_r, hrep'⟩ := hrep K hK1 hK0 a ha_mono ha_range
  obtain ⟨c_m, x_m, hmaj⟩ :=
    major_square_bound δ C hδ hC c₁ c₂ hc₁ S hS hα A₀ hA₀ _ hD1 K hK1 a ha_mono ha_range
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((eventually_bounds δ (C + C + Dstar) c₁ hδ hc₁ K).and
      (eventually_groupsDisjoint a ha_mono))
  set c : ℝ := |c_r| + |c_m| with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨(3 * K + 1) * Real.sqrt (5 * c) + 2, max (max x_r x_m) x₁, ?_⟩
  intro x Hm Hn α β hmem hx F hFb hFi
  have hxr : x_r ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxm : x_m ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x₁ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨hx1', hL1, hPX, hsmall, hbig⟩, hdisj⟩ := hx₁ x hx1
  obtain ⟨hHm, hHn, hX1, hX2, hJα, hβs, hαb, hβb⟩ := hS x Hm Hn α β hmem
  have hxδ : 1 < x ^ δ := one_lt_rpow hx1' hδ
  have hHm1 : 1 ≤ Hm := by linarith
  have hHn1 : 1 ≤ Hn := by linarith
  have hXpos : 0 < Hm * Hn := by positivity
  have hLpos : 0 < log x := by linarith
  set Pmin := exp (log x ^ (0.1 : ℝ)) with hPmin
  set Pmax := exp (2 * log x ^ (0.2 : ℝ)) with hPmax
  have hgroup : ∀ i, ∀ P ∈ primeGroup x (a i), Pmin ≤ (P : ℝ) ∧ (P : ℝ) ≤ Pmax :=
    fun i P hP => primeGroup_bounds hL1 (ha_range i) hP
  have hPmaxK : Pmax ^ K = exp (2 * K * log x ^ (0.2 : ℝ)) := by
    rw [hPmax, ← exp_nat_mul]; ring_nf
  have hsupp : ∀ m n, α m ≠ 0 → β n ≠ 0 → 2 ≤ m * n := by
    intro m n hm hn
    obtain ⟨J, -, hJsub, hJm⟩ := hJα
    have hm1 : (1 : ℝ) < m := by have := (hJsub (hJm m hm).1).1; linarith
    have hm2 : 2 ≤ m := by
      have : 1 < m := by exact_mod_cast hm1
      omega
    have hn1 : 0 < n := (hβs n hn).2.2.1
    nlinarith
  -- the error of the damping replacement, [21] (3.6)
  have hErr := damping hdisj q hq0 hq1 F hFb hFi α β (log x ^ C) (log x ^ C) hαb hβb hsupp
    ⌊2 * Hm⌋₊ ⌊2 * Hn⌋₊ Pmin Pmax (exp_pos _) (exp_pos _).le hgroup
  have hM : ((⌊2 * Hm⌋₊ : ℕ) : ℝ) + 1 ≤ 3 * Hm := by
    have := Nat.floor_le (show 0 ≤ 2 * Hm by positivity); linarith
  have hN : ((⌊2 * Hn⌋₊ : ℕ) : ℝ) ≤ 2 * Hn := Nat.floor_le (by positivity)
  have hℓ : 0 < log x ^ Dstar := rpow_pos_of_pos hLpos _
  have hlam : 0 < log x ^ C := rpow_pos_of_pos hLpos _
  have hE : log x ^ (C + C + Dstar) = log x ^ C * log x ^ C * log x ^ Dstar := by
    rw [rpow_add hLpos, rpow_add hLpos]
  rw [hE] at hsmall hbig
  rw [← hPmaxK] at hbig hPX
  have hErr2 : log x ^ C * log x ^ C * ((((⌊2 * Hm⌋₊ : ℕ) : ℝ) + 1) * K *
      (((⌊2 * Hn⌋₊ : ℕ) : ℝ) / Pmin + Pmax ^ K)) ≤ 2 * (Hm * Hn) / log x ^ Dstar := by
    have t1 : 6 * K * (log x ^ C * log x ^ C) * (Hm * Hn) / Pmin ≤ (Hm * Hn) / log x ^ Dstar := by
      rw [div_le_div_iff₀ (exp_pos _) hℓ]
      calc 6 * K * (log x ^ C * log x ^ C) * (Hm * Hn) * log x ^ Dstar =
            (Hm * Hn) * (6 * K * (log x ^ C * log x ^ C * log x ^ Dstar)) := by ring
        _ ≤ (Hm * Hn) * Pmin := mul_le_mul_of_nonneg_left hsmall hXpos.le
    have t2 : 3 * K * (log x ^ C * log x ^ C) * Hm * Pmax ^ K ≤ (Hm * Hn) / log x ^ Dstar := by
      rw [le_div_iff₀ hℓ]
      calc 3 * K * (log x ^ C * log x ^ C) * Hm * Pmax ^ K * log x ^ Dstar =
            Hm * (3 * K * (log x ^ C * log x ^ C * log x ^ Dstar) * Pmax ^ K) := by ring
        _ ≤ Hm * Hn := mul_le_mul_of_nonneg_left (hbig.trans hHn) (by linarith)
    calc _ ≤ log x ^ C * log x ^ C * ((3 * Hm) * K * ((2 * Hn) / Pmin + Pmax ^ K)) := by
          gcongr
      _ = 6 * K * (log x ^ C * log x ^ C) * (Hm * Hn) / Pmin +
            3 * K * (log x ^ C * log x ^ C) * Hm * Pmax ^ K := by ring
      _ ≤ (Hm * Hn) / log x ^ Dstar + (Hm * Hn) / log x ^ Dstar := add_le_add t1 t2
      _ = 2 * (Hm * Hn) / log x ^ Dstar := by ring
  -- the dyads
  set J := Nat.log 2 ⌊Pmax ^ K⌋₊ with hJ
  have hPK1 : 1 ≤ Pmax ^ K := one_le_pow₀ (one_le_exp (by positivity))
  have hfl0 : ⌊Pmax ^ K⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Pmax ^ K⌋₊ := Nat.le_floor (by simpa using hPK1)
    omega
  have h2J : (2 : ℝ) ^ J ≤ Pmax ^ K := by
    have := Nat.pow_log_le_self 2 hfl0
    calc (2 : ℝ) ^ J = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊Pmax ^ K⌋₊ : ℝ) := Nat.cast_le.2 this
      _ ≤ Pmax ^ K := Nat.floor_le (by positivity)
  have hb : ∀ p ∈ labelTuples x a,
      2 ≤ ((∏ i, p i : ℕ) : ℝ) ∧ ((∏ i, p i : ℕ) : ℝ) ≤ 2 ^ (J + 1) := by
    intro p hp
    refine ⟨by exact_mod_cast two_le_label_prod hK1 hp, ?_⟩
    have h1 : ∏ i, p i ≤ ⌊Pmax ^ K⌋₊ :=
      Nat.le_floor (label_prod_le (fun i P hP => (hgroup i P hP).2) hp)
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊Pmax ^ K⌋₊
    exact_mod_cast (h1.trans h2.le)
  have hJL : (J : ℝ) + 1 ≤ (3 * K + 1) * log x := by
    have h1 : (J : ℝ) * log 2 ≤ 2 * K * log x := by
      calc (J : ℝ) * log 2 = log ((2 : ℝ) ^ J) := by rw [Real.log_pow]
        _ ≤ log (Pmax ^ K) := Real.log_le_log (by positivity) h2J
        _ = 2 * K * log x ^ (0.2 : ℝ) := by rw [hPmaxK, Real.log_exp]
        _ ≤ 2 * K * log x := by
          have : log x ^ (0.2 : ℝ) ≤ log x := by
            calc log x ^ (0.2 : ℝ) ≤ log x ^ (1 : ℝ) :=
                  rpow_le_rpow_of_exponent_le hL1 (by norm_num)
              _ = log x := rpow_one _
          gcongr
    have hlog2 : (2 : ℝ) / 3 < log 2 := by have := Real.log_two_gt_d9; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hQ : ∀ j ∈ range (J + 1), (2 : ℝ) ^ j ≤ Hm * Hn ∧
      ‖expandedSquare x a (2 ^ j) Hm Hn α β‖ ≤
        c * (Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹) := by
    intro j hj
    have hY1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    refine ⟨?_, ?_⟩
    · calc (2 : ℝ) ^ j ≤ 2 ^ J :=
            pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.1 (mem_range.1 hj))
        _ ≤ Pmax ^ K := h2J
        _ ≤ c₁ * x := hPX
        _ ≤ Hm * Hn := hX1
    · have h1 := hrep' x Hm Hn hxr hHm hHn hX1 hX2 α β hJα hβs hαb hβb (2 ^ j) hY1
      have h2 := hmaj x Hm Hn α β hmem hxm (2 ^ j) hY1
      have e : log x ^ (-((Dstar + 1) + (Dstar + 1))) =
          ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹ := by
        rw [rpow_neg hLpos.le, rpow_add hLpos, rpow_add hLpos, rpow_one]
      rw [e] at h1 h2
      have hW : 0 ≤ Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹ := by
        positivity
      have := norm_le_insert' (expandedSquare x a (2 ^ j) Hm Hn α β)
        (majorSquare x a A₀ (2 ^ j) Hm Hn α β)
      have h3 : c_r * (Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹) ≤
          |c_r| * (Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hW
      have h4 : c_m * (Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹) ≤
          |c_m| * (Hm * Hn * 2 ^ j * ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hW
      rw [hc, add_mul]
      linarith
  have hMain := main_bound (x := x) (a := a) Hm Hn (by linarith) (by linarith) α β
    (damped q x a F) (norm_damped_le q hq0 hq1 F hFb) J hb c
    ((log x ^ Dstar * log x) * (log x ^ Dstar * log x))⁻¹
    (Real.sqrt (5 * c) * (Hm * Hn) / (log x ^ Dstar * log x)) (by positivity) ?_ hQ
  · rw [rpow_neg hLpos.le]
    refine (norm_le_insert' _ _).trans ((add_le_add hMain (hErr.trans hErr2)).trans ?_)
    calc ((J : ℝ) + 1) * (Real.sqrt (5 * c) * (Hm * Hn) / (log x ^ Dstar * log x)) +
          2 * (Hm * Hn) / log x ^ Dstar ≤
        ((3 * K + 1) * log x) * (Real.sqrt (5 * c) * (Hm * Hn) / (log x ^ Dstar * log x)) +
          2 * (Hm * Hn) / log x ^ Dstar := by gcongr
      _ = ((3 * K + 1) * Real.sqrt (5 * c) + 2) * (Hm * Hn) * (log x ^ Dstar)⁻¹ := by
          field_simp
  · rw [div_pow, mul_pow (Real.sqrt (5 * c)) (Hm * Hn), Real.sq_sqrt (by positivity)]
    apply le_of_eq
    field_simp
end
