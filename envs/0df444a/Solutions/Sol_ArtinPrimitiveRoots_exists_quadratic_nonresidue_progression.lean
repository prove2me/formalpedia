-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_quadratic_nonresidue_progression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T08:57:56.842987+00:00
-- url     : https://prove2.me/submissions/a2aa318d-d3e3-4fc2-b018-024165431a09

import Mathlib

namespace ArtinPrimitiveRoots.Lemma24

/-- The Jacobi symbol `J(n | p)` depends only on `p` modulo any `N` divisible by `8`
and by every odd prime factor of `n`. -/
lemma jac_congr_nat (N : ℕ) (h8 : 8 ∣ N) (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hpq : p ≡ q [MOD N]) : ∀ n : ℕ, n ≠ 0 →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ n → ℓ ∣ N) →
    jacobiSym (n : ℤ) p = jacobiSym (n : ℤ) q := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simp [jacobiSym.one_left]
  | prime ℓ hℓ =>
    intro _ hP
    have hℓ' := hℓ
    rcases hℓ'.eq_two_or_odd' with rfl | hodd
    · have h8' : p ≡ q [MOD 8] := Nat.ModEq.of_dvd h8 hpq
      push_cast
      rw [jacobiSym.at_two hp, jacobiSym.at_two hq]
      congr 1
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h8'
    · have hne : ℓ ≠ 2 := by rintro rfl; exact absurd hodd (by decide)
      have hcop : Nat.Coprime 4 ℓ := by
        have : Nat.Coprime 2 ℓ := (Nat.coprime_primes Nat.prime_two hℓ').mpr hne.symm
        simpa using Nat.Coprime.pow_left 2 this
      have hN : 4 * ℓ ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
        (dvd_trans (by norm_num) h8) (hP ℓ hℓ' hne dvd_rfl)
      rw [jacobiSym.mod_right' ℓ hp, jacobiSym.mod_right' ℓ hq]
      congr 1
      exact Nat.ModEq.of_dvd hN hpq
  | mul a b iha ihb =>
    intro hab hP
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.mul_left,
      iha ha (fun ℓ h1 h2 h3 => hP ℓ h1 h2 (dvd_mul_of_dvd_left h3 b)),
      ihb hb (fun ℓ h1 h2 h3 => hP ℓ h1 h2 (dvd_mul_of_dvd_right h3 a))]

lemma jac_congr (a : ℤ) (ha : a ≠ 0) (N : ℕ) (h8 : 8 ∣ N)
    (hP : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ a.natAbs → ℓ ∣ N)
    (p q : ℕ) (hp : Odd p) (hq : Odd q) (hpq : p ≡ q [MOD N]) :
    jacobiSym a p = jacobiSym a q := by
  have hn : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  rcases Int.natAbs_eq a with h | h
  · rw [h]; exact jac_congr_nat N h8 p q hp hq hpq _ hn hP
  · rw [h, neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.at_neg_one hp, jacobiSym.at_neg_one hq,
      jac_congr_nat N h8 p q hp hq hpq _ hn hP]
    congr 2
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hpq)


/-- The odd prime factors of `a`. -/
def oddP (a : ℤ) : Finset ℕ := a.natAbs.primeFactors.filter (· ≠ 2)

lemma mem_oddP {a : ℤ} {ℓ : ℕ} :
    ℓ ∈ oddP a ↔ ℓ.Prime ∧ ℓ ∣ a.natAbs ∧ a.natAbs ≠ 0 ∧ ℓ ≠ 2 := by
  simp [oddP, Finset.mem_filter, Nat.mem_primeFactors, and_assoc]

lemma oddP_facts {a : ℤ} {ℓ : ℕ} (h : ℓ ∈ oddP a) :
    ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ∣ ∏ m ∈ oddP a, m := by
  obtain ⟨hp, -, -, h2⟩ := mem_oddP.mp h
  refine ⟨hp, ?_, Finset.dvd_prod_of_mem _ h⟩
  have := hp.two_le
  omega

lemma prod_odd (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime ∧ 3 ≤ ℓ) : Odd (∏ m ∈ S, m) := by
  rw [Nat.odd_iff]
  have : ¬ 2 ∣ ∏ m ∈ S, m := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨ℓ, hℓ, h2⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hS ℓ hℓ).1).mp h2
    have := (hS ℓ hℓ).2
    omega
  omega

lemma neg_one_facts (ℓ : ℕ) (h : 3 ≤ ℓ) : (-1 : ZMod ℓ) ≠ 0 ∧ (-1 : ZMod ℓ) ≠ 1 := by
  have : Fact (1 < ℓ) := ⟨by omega⟩
  have : Fact (2 < ℓ) := ⟨by omega⟩
  exact ⟨neg_ne_zero.mpr one_ne_zero, ZMod.neg_one_ne_one⟩

lemma gcd_eq_one (a : ℤ) (ha : a ≠ 0) (x : ℕ) (hx : Odd x)
    (h : ∀ ℓ ∈ oddP a, (x : ZMod ℓ) ≠ 0) : a.gcd x = 1 := by
  have : Nat.Coprime a.natAbs x := by
    apply Nat.coprime_of_dvd
    intro k hk hka hkx
    by_cases hk2 : k = 2
    · subst hk2
      exact (Nat.not_even_iff_odd.mpr hx) (even_iff_two_dvd.mpr hkx)
    · exact h k (mem_oddP.mpr ⟨hk, hka, Int.natAbs_ne_zero.mpr ha, hk2⟩)
        ((ZMod.natCast_eq_zero_iff _ _).mpr hkx)
  simpa [Int.gcd] using this

lemma small_val (a₀ : ℤ) (N q r : ℕ) (h8 : 8 ∣ N) (ha0 : a₀ ≠ 0) (hdvd : a₀.natAbs ∣ N)
    (hqo : Odd q) (hro : Odd r) (hq : q % N = r % N) : jacobiSym a₀ q = jacobiSym a₀ r :=
  jac_congr a₀ ha0 N h8 (fun _ _ _ h => h.trans hdvd) q r hqo hro hq

lemma small_char (a₀ : ℤ)
    (h : a₀ = -1 ∨ a₀ = 2 ∨ a₀ = -2 ∨ a₀ = 3 ∨ a₀ = -3 ∨ a₀ = 6 ∨ a₀ = -6) :
    ∃ r8 : ℕ, (r8 = 3 ∨ r8 = 5 ∨ r8 = 7) ∧ ∀ q : ℕ, q % 8 = r8 →
      ((3 : ℤ) ∣ a₀ → q % 3 = 2) → jacobiSym a₀ q = -1 := by
  have hodd : ∀ q : ℕ, q % 2 = 1 → Odd q := fun q hq => Nat.odd_iff.mpr hq
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨3, by norm_num, fun q hq _ => ?_⟩
    rw [small_val _ 8 q 3 (dvd_refl _) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨3, by norm_num, fun q hq _ => ?_⟩
    rw [small_val _ 8 q 3 (dvd_refl _) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨7, by norm_num, fun q hq _ => ?_⟩
    rw [small_val _ 8 q 7 (dvd_refl _) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨5, by norm_num, fun q hq h3 => ?_⟩
    have := h3 (by norm_num)
    rw [small_val _ 24 q 5 (by norm_num) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨5, by norm_num, fun q hq h3 => ?_⟩
    have := h3 (by norm_num)
    rw [small_val _ 24 q 5 (by norm_num) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨3, by norm_num, fun q hq h3 => ?_⟩
    have := h3 (by norm_num)
    rw [small_val _ 24 q 11 (by norm_num) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num
  · refine ⟨7, by norm_num, fun q hq h3 => ?_⟩
    have := h3 (by norm_num)
    rw [small_val _ 24 q 23 (by norm_num) (by norm_num) (by norm_num) (hodd q (by omega))
      (by decide) (by omega)]
    norm_num

/-- A nonsquare modulo a prime `j ≥ 5` that is not `-1`. -/
lemma exists_nonsq (j : ℕ) [Fact j.Prime] (hj5 : 5 ≤ j) :
    ∃ y : ZMod j, ¬ IsSquare y ∧ y ≠ -1 := by
  have hcast : ∀ m : ℕ, 0 < m → m < j → (m : ZMod j) ≠ 0 := by
    intro m hm hmj h
    have := Nat.le_of_dvd hm ((ZMod.natCast_eq_zero_iff _ _).mp h)
    omega
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod j)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  by_cases hx1 : x = -1
  · have h2 : (2 : ZMod j) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
    have h3 : (3 : ZMod j) ≠ 0 := by exact_mod_cast hcast 3 (by norm_num) (by omega)
    refine ⟨4 * x, ?_, ?_⟩
    · rintro ⟨z, hz⟩
      apply hx
      refine ⟨z / 2, ?_⟩
      field_simp
      linear_combination hz
    · intro h
      apply h3
      rw [hx1] at h
      linear_combination -h
  · exact ⟨x, hx, hx1⟩

lemma case_big (a a₀ : ℤ) (ha : a ≠ 0)
    (hgcd : ∀ x : ℕ, a.gcd x = 1 → jacobiSym a x = jacobiSym a₀ x)
    (j : ℕ) (hj : j.Prime) (hj5 : 5 ≤ j) (b : ℤ) (hab : a₀ = j * b) (hb0 : b ≠ 0)
    (hbP : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ b.natAbs → ℓ ∈ oddP a ∧ ℓ ≠ j)
    (hjS : j ∈ oddP a) :
    ∃ q : ℕ, (q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7) ∧
      (∀ ℓ ∈ oddP a, (q : ZMod ℓ) ≠ 0 ∧ (q : ZMod ℓ) ≠ 1) ∧ jacobiSym a q = -1 := by
  set S := oddP a with hSdef
  set L := ∏ m ∈ S, m with hL
  have hLodd : Odd L := prod_odd S fun ℓ hℓ => ⟨(oddP_facts hℓ).1, (oddP_facts hℓ).2.1⟩
  have hL1 : 1 ≤ L := by obtain ⟨t, ht⟩ := hLodd; omega
  set q₀ := 8 * L - 1 with hq₀
  have hq₀8 : q₀ % 8 = 7 := by omega
  have hq₀odd : Odd q₀ := by rw [Nat.odd_iff]; omega
  have hq₀Z : ∀ ℓ ∈ S, (q₀ : ZMod ℓ) = -1 := by
    intro ℓ hℓ
    have hLz : (L : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (oddP_facts hℓ).2.2
    rw [hq₀, Nat.cast_sub (by omega)]
    push_cast
    rw [hLz]; ring
  have hgq₀ : a.gcd q₀ = 1 := gcd_eq_one a ha q₀ hq₀odd fun ℓ hℓ => by
    rw [hq₀Z ℓ hℓ]; exact (neg_one_facts ℓ (oddP_facts hℓ).2.1).1
  by_cases h0 : jacobiSym a q₀ = -1
  · refine ⟨q₀, by omega, fun ℓ hℓ => ?_, h0⟩
    rw [hq₀Z ℓ hℓ]; exact neg_one_facts ℓ (oddP_facts hℓ).2.1
  have h1 : jacobiSym a q₀ = 1 := (jacobiSym.eq_one_or_neg_one hgq₀).resolve_right h0
  have : Fact j.Prime := ⟨hj⟩
  obtain ⟨y, hy, hy1⟩ := exists_nonsq j hj5
  have hy0 : y ≠ 0 := by rintro rfl; exact hy ⟨0, by simp⟩
  set g := y.val with hg
  have hgy : (g : ZMod j) = y := ZMod.natCast_zmod_val y
  -- the complementary modulus
  set L' := ∏ m ∈ S.erase j, m with hL'
  have hLL' : j * L' = L := Finset.mul_prod_erase S id hjS
  have hco : Nat.Coprime (8 * L') j := by
    refine Nat.Coprime.mul_left ?_ (Nat.Coprime.prod_left fun ℓ hℓ => ?_)
    · have : Nat.Coprime 2 j := (Nat.coprime_primes Nat.prime_two hj).mpr (by omega)
      simpa using Nat.Coprime.pow_left 3 this
    · exact (Nat.coprime_primes (oddP_facts (Finset.mem_of_mem_erase hℓ)).1 hj).mpr
        (Finset.ne_of_mem_erase hℓ)
  obtain ⟨r, hr1, hrg⟩ := Nat.chineseRemainder hco 1 g
  have hr8 : r % 8 = 1 := by
    have := Nat.ModEq.of_dvd (dvd_mul_right 8 L') hr1
    unfold Nat.ModEq at this; omega
  have hrodd : Odd r := by rw [Nat.odd_iff]; omega
  have hrj : (r : ZMod j) = y := by
    rw [← hgy]; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hrg
  have hrS : ∀ ℓ ∈ S, ℓ ≠ j → (r : ZMod ℓ) = 1 := by
    intro ℓ hℓ hne
    have hdvd : ℓ ∣ 8 * L' :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hℓ⟩)) 8
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hdvd hr1)
    simpa using this
  have hgr : a.gcd r = 1 := gcd_eq_one a ha r hrodd fun ℓ hℓ => by
    by_cases hne : ℓ = j
    · subst hne; rw [hrj]; exact hy0
    · have : Fact (1 < ℓ) := ⟨by have := (oddP_facts hℓ).2.1; omega⟩
      rw [hrS ℓ hℓ hne]; exact one_ne_zero
  -- the symbol at `r`
  have hJb : jacobiSym b r = 1 := by
    rw [jac_congr b hb0 (8 * L') (dvd_mul_right 8 L') ?_ r 1 hrodd odd_one hr1,
      jacobiSym.one_right]
    intro ℓ hℓ h2 hd
    obtain ⟨hS, hne⟩ := hbP ℓ hℓ h2 hd
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hS⟩)) 8
  have hJj : jacobiSym (j : ℤ) r = -1 := by
    have hr4 : r % 4 = 1 := by omega
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hr4 (hj.odd_of_ne_two (by omega)),
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    simpa [hrj] using hy
  have hJr : jacobiSym a r = -1 := by
    rw [hgcd r hgr, hab, jacobiSym.mul_left, hJj, hJb]; norm_num
  refine ⟨q₀ * r, ?_, fun ℓ hℓ => ?_, ?_⟩
  · rw [Nat.mul_mod, hq₀8, hr8]; norm_num
  · push_cast
    rw [hq₀Z ℓ hℓ]
    by_cases hne : ℓ = j
    · subst hne
      rw [hrj]
      refine ⟨by simpa using hy0, fun h => hy1 ?_⟩
      linear_combination -h
    · rw [hrS ℓ hℓ hne, mul_one]; exact neg_one_facts ℓ (oddP_facts hℓ).2.1
  · rw [jacobiSym.mul_right' a (by rintro h; simp [h] at hq₀odd)
      (by rintro h; simp [h] at hrodd), h1, hJr]; norm_num

lemma exists_q (a : ℤ) (hsq : ¬ IsSquare a) :
    ∃ q : ℕ, (q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7) ∧
      (∀ ℓ ∈ oddP a, (q : ZMod ℓ) ≠ 0 ∧ (q : ZMod ℓ) ≠ 1) ∧ jacobiSym a q = -1 := by
  have ha : a ≠ 0 := by rintro rfl; exact hsq ⟨0, by simp⟩
  have hn0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  obtain ⟨d, k, hd, hk, hkd, hsf⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr ha)
  obtain ⟨s, hs, hsa⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ a = s * a.natAbs := by
    rcases Int.natAbs_eq a with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul]; exact h⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_mul]; exact h⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℤ, a₀ = s * d := ⟨_, rfl⟩
  have haa : a = (k : ℤ) ^ 2 * a₀ := by rw [hsa, ← hkd, ha₀]; push_cast; ring
  have hgcd : ∀ x : ℕ, a.gcd x = 1 → jacobiSym a x = jacobiSym a₀ x := by
    intro x hx
    rw [haa] at hx ⊢
    rw [jacobiSym.mul_left, jacobiSym.sq_one', one_mul]
    have h1 := (Int.isCoprime_iff_gcd_eq_one.mpr hx).of_mul_left_left
    exact Int.isCoprime_iff_gcd_eq_one.mp ((IsCoprime.pow_left_iff (by norm_num)).mp h1)
  have hdvdn : ∀ m : ℕ, m ∣ d → m ∣ a.natAbs := fun m hm =>
    hkd ▸ dvd_mul_of_dvd_right hm _
  by_cases hbig : ∃ j : ℕ, j.Prime ∧ 5 ≤ j ∧ j ∣ d
  · obtain ⟨j, hj, hj5, d', rfl⟩ := hbig
    have hjd' : ¬ j ∣ d' := by
      intro h
      have := hsf j (mul_dvd_mul_left j h)
      rw [Nat.isUnit_iff] at this
      omega
    have hd'0 : d' ≠ 0 := by rintro rfl; simp at hd
    have hsabs : s.natAbs = 1 := by rcases hs with rfl | rfl <;> rfl
    refine case_big a a₀ ha hgcd j hj hj5 (s * d') (by rw [ha₀]; push_cast; ring) ?_ ?_ ?_
    · rcases hs with rfl | rfl <;> simpa using hd'0
    · intro ℓ hℓ h2 hd'
      rw [Int.natAbs_mul, hsabs, one_mul, Int.natAbs_natCast] at hd'
      refine ⟨mem_oddP.mpr ⟨hℓ, hdvdn ℓ (dvd_mul_of_dvd_right hd' j), hn0, h2⟩, ?_⟩
      rintro rfl; exact hjd' hd'
    · exact mem_oddP.mpr ⟨hj, hdvdn j (dvd_mul_right j d'), hn0, by omega⟩
  push Not at hbig
  have hd6 : d ∣ 6 := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    calc ∏ p ∈ d.primeFactors, p ∣ ∏ p ∈ ({2, 3} : Finset ℕ), p := by
          apply Finset.prod_dvd_prod_of_subset
          intro p hp
          obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
          have h5 : p < 5 := by
            by_contra h
            exact hbig p hpp (by omega) hpd
          have := hpp.two_le
          interval_cases p <;> first | (exfalso; norm_num at hpp; done) | simp
      _ = 6 := by decide
  have hd' : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
    have := Nat.le_of_dvd (by norm_num) hd6
    interval_cases d <;> first | (exfalso; norm_num at hd6; done) | simp
  have ha0 : a₀ = -1 ∨ a₀ = 2 ∨ a₀ = -2 ∨ a₀ = 3 ∨ a₀ = -3 ∨ a₀ = 6 ∨ a₀ = -6 := by
    rcases hs with rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl <;> subst ha₀ <;>
      norm_num
    exact hsq ⟨k, by rw [haa]; ring⟩
  obtain ⟨r8, hr8, hchar⟩ := small_char a₀ ha0
  set S := oddP a with hSdef
  set L := ∏ m ∈ S, m with hL
  have hLodd : Odd L := prod_odd S fun ℓ hℓ => ⟨(oddP_facts hℓ).1, (oddP_facts hℓ).2.1⟩
  have hL2 : L ^ 2 % 8 = 1 := by
    have h := Nat.odd_iff.mp hLodd
    have : L % 8 = 1 ∨ L % 8 = 3 ∨ L % 8 = 5 ∨ L % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hL1 : 1 ≤ L ^ 2 := by omega
  set q := (r8 + 1) * L ^ 2 - 1 with hq
  have hq8 : q % 8 = r8 := by rcases hr8 with rfl | rfl | rfl <;> omega
  have hqZ : ∀ ℓ ∈ S, (q : ZMod ℓ) = -1 := by
    intro ℓ hℓ
    have hLz : (L : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (oddP_facts hℓ).2.2
    rw [hq, Nat.cast_sub (by nlinarith)]
    push_cast
    rw [hLz]; ring
  have hqodd : Odd q := by rw [Nat.odd_iff]; rcases hr8 with rfl | rfl | rfl <;> omega
  have hgq : a.gcd q = 1 := gcd_eq_one a ha q hqodd fun ℓ hℓ => by
    rw [hqZ ℓ hℓ]; exact (neg_one_facts ℓ (oddP_facts hℓ).2.1).1
  refine ⟨q, by rw [hq8]; exact hr8, fun ℓ hℓ => ?_, ?_⟩
  · rw [hqZ ℓ hℓ]; exact neg_one_facts ℓ (oddP_facts hℓ).2.1
  · rw [hgcd q hgq]
    refine hchar q hq8 fun h3 => ?_
    have h3a : (3 : ℕ) ∣ a.natAbs := by
      have : (3 : ℤ) ∣ a := haa ▸ dvd_mul_of_dvd_right h3 _
      exact Int.natAbs_dvd_natAbs.mpr this
    have h3S : 3 ∈ S := mem_oddP.mpr ⟨Nat.prime_three, h3a, hn0, by norm_num⟩
    have := hqZ 3 h3S
    have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
    rw [← h2, ZMod.natCast_eq_natCast_iff'] at this
    simpa using this

theorem main (a : ℤ) (hsq : ¬ IsSquare a) :
    let M : ℕ := 8 * ∏ ℓ ∈ a.natAbs.primeFactors.filter (· ≠ 2), ℓ
    ∃ c : ℕ, (c = 2 ∨ c = 4) ∧ ∃ u : ℤ, IsCoprime u M ∧ (c : ℤ) ∣ u - 1 ∧
      IsCoprime ((u - 1) / c) ((M : ℤ) / c) ∧
      ∀ p : ℕ, (hp : p.Prime) → (p : ℤ) ≡ u [ZMOD M] →
        ¬ (p : ℤ) ∣ a ∧ @legendreSym p ⟨hp⟩ a = -1 := by
  intro M
  have ha : a ≠ 0 := by rintro rfl; exact hsq ⟨0, by simp⟩
  obtain ⟨q, hq8, hqS, hJ⟩ := exists_q a hsq
  have hM : M = 8 * ∏ ℓ ∈ oddP a, ℓ := rfl
  set L := ∏ ℓ ∈ oddP a, ℓ with hL
  have hqodd : Odd q := by rw [Nat.odd_iff]; omega
  obtain ⟨c, w, k8, hc, hqw, hw, hck⟩ : ∃ c w k8 : ℕ, (c = 2 ∨ c = 4) ∧ q = c * w + 1 ∧
      Odd w ∧ c * k8 = 8 := by
    rcases hq8 with h | h | h
    · exact ⟨2, q / 2, 4, Or.inl rfl, by omega, by rw [Nat.odd_iff]; omega, rfl⟩
    · exact ⟨4, q / 4, 2, Or.inr rfl, by omega, by rw [Nat.odd_iff]; omega, rfl⟩
    · exact ⟨2, q / 2, 4, Or.inl rfl, by omega, by rw [Nat.odd_iff]; omega, rfl⟩
  have hc0 : (c : ℤ) ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  have hcopL : ∀ x : ℕ, (∀ ℓ ∈ oddP a, (x : ZMod ℓ) ≠ 0) → Nat.Coprime x L := by
    intro x hx
    refine Nat.Coprime.prod_right fun ℓ hℓ => ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (oddP_facts hℓ).1]
    intro hd
    exact hx ℓ hℓ ((ZMod.natCast_eq_zero_iff _ _).mpr hd)
  refine ⟨c, hc, q, ?_, ⟨w, by rw [hqw]; push_cast; ring⟩, ?_, ?_⟩
  · rw [hM, Nat.isCoprime_iff_coprime]
    refine Nat.Coprime.mul_right ?_ (hcopL q fun ℓ hℓ => (hqS ℓ hℓ).1)
    have : Nat.Coprime q 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hqodd)))
    simpa using Nat.Coprime.pow_right 3 this
  · have h1 : (q : ℤ) - 1 = c * w := by rw [hqw]; push_cast; ring
    have h2 : ((M : ℕ) : ℤ) = c * ((k8 * L : ℕ) : ℤ) := by
      rw [hM]; push_cast; rw [← mul_assoc]; exact_mod_cast (congrArg (· * L) hck).symm
    rw [h1, h2, Int.mul_ediv_cancel_left _ hc0, Int.mul_ediv_cancel_left _ hc0,
      Nat.isCoprime_iff_coprime]
    refine Nat.Coprime.mul_right ?_ (hcopL w fun ℓ hℓ hw0 => (hqS ℓ hℓ).2 ?_)
    · have h8 : Nat.Coprime w 8 := by
        have : Nat.Coprime w 2 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
          Nat.prime_two).mpr (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hw)))
        simpa using Nat.Coprime.pow_right 3 this
      exact Nat.Coprime.coprime_dvd_right ⟨c, by rw [← hck]; ring⟩ h8
    · rw [hqw]; push_cast; rw [hw0]; ring
  · intro p hp hpu
    have hpq : p ≡ q [MOD M] := Int.natCast_modEq_iff.mp hpu
    have hpodd : Odd p := by
      have := Nat.ModEq.of_dvd (dvd_mul_right 8 L) hpq
      unfold Nat.ModEq at this
      rw [Nat.odd_iff]; omega
    have hJp : jacobiSym a p = -1 := by
      rw [jac_congr a ha M (dvd_mul_right 8 _) ?_ p q hpodd hqodd hpq, hJ]
      intro ℓ hℓ h2 hd
      exact dvd_mul_of_dvd_right
        (oddP_facts (mem_oddP.mpr ⟨hℓ, hd, Int.natAbs_ne_zero.mpr ha, h2⟩)).2.2 8
    have := Fact.mk hp
    have hleg : legendreSym p a = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJp
    refine ⟨fun hdvd => ?_, hleg⟩
    have : legendreSym p a = 0 :=
      (legendreSym.eq_zero_iff p a).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hdvd)
    rw [hleg] at this
    norm_num at this

end ArtinPrimitiveRoots.Lemma24

theorem solution (a : ℤ) (ha : a ≠ -1) (hsq : ¬ IsSquare a) :
    let M : ℕ := 8 * ∏ ℓ ∈ a.natAbs.primeFactors.filter (· ≠ 2), ℓ
    ∃ c : ℕ, (c = 2 ∨ c = 4) ∧ ∃ u : ℤ, IsCoprime u M ∧ (c : ℤ) ∣ u - 1 ∧
      IsCoprime ((u - 1) / c) ((M : ℤ) / c) ∧
      ∀ p : ℕ, (hp : p.Prime) → (p : ℤ) ≡ u [ZMOD M] →
        ¬ (p : ℤ) ∣ a ∧ @legendreSym p ⟨hp⟩ a = -1 :=
  ArtinPrimitiveRoots.Lemma24.main a hsq
