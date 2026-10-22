-- Prove2me | solution 1 for AKS.prime_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:23:45.701151+00:00
-- url     : https://prove2.me/submissions/077812f5-4beb-4c87-ad2f-4fffe59aec38

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS


open Polynomial in
/-- If X^r - 1 divides f^m - f(X^m) then in AdjoinRoot h (h ∣ X^r - 1) f(ζ)^m = f(ζ^m). -/
theorem g71b_intro_eval {p r : ℕ} (h f : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) {m : ℕ} (hm : introspective p r f m) :
    aeval (AdjoinRoot.root h) f ^ m = aeval (AdjoinRoot.root h ^ m) f := by
  have h1 : h ∣ f ^ m - f.comp (X ^ m) := dvd_trans hdiv hm
  have h2 : aeval (AdjoinRoot.root h) (f ^ m - f.comp (X ^ m)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact h1
  rw [map_sub, map_pow, aeval_comp, map_pow, aeval_X, sub_eq_zero] at h2
  exact h2

open Polynomial in
theorem g71b_root_pow_r {p r : ℕ} (h : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) : AdjoinRoot.root h ^ r = 1 := by
  have h2 : aeval (AdjoinRoot.root h) (X ^ r - 1 : Polynomial (ZMod p)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact hdiv
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h2
  exact h2

theorem g71b_pow_mod {M : Type*} [Monoid M] (x : M) (r m : ℕ) (hx : x ^ r = 1) :
    x ^ m = x ^ (m % r) := by
  conv_lhs => rw [← Nat.mod_add_div m r, pow_add, pow_mul, hx, one_pow, mul_one]

theorem g71b_inj (a p : ℕ) (hp : p.Prime) (ha : 0 < a) (hapow : ∀ c, a ≠ p ^ c)
    (i j i' j' : ℕ) (hlt : i' < i) (heq : a ^ i * p ^ j = a ^ i' * p ^ j') : False := by
  have hai : a ^ i = a ^ i' * a ^ (i - i') := by rw [← pow_add]; congr 1; omega
  rw [hai, mul_assoc] at heq
  have hpos : 0 < a ^ i' := pow_pos ha _
  have h2 : a ^ (i - i') * p ^ j = p ^ j' := Nat.eq_of_mul_eq_mul_left hpos heq
  have h3 : a ∣ p ^ j' := by
    rw [← h2]; exact Dvd.dvd.mul_right (dvd_pow_self a (by omega)) _
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 h3
  exact hapow c hc

theorem g71b_group_upper (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (hpn : p ∣ n) (hn : 0 < n)
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (hnpow : ¬ ∃ k, 0 < k ∧ n = p ^ k)
    (ht : t = (Gfin n p r).card)
    (hcop : Nat.gcd (n / p) r = 1 ∧ Nat.gcd p r = 1) :
    ∃ m₁ m₂ : ℕ, m₂ < m₁ ∧ m₁ ≤ n ^ (Nat.sqrt t) ∧
      ∀ f, inP p ℓ f →
        Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂ := by
  have hp : p.Prime := Fact.out
  set a := n / p with ha_def
  have hna : n = p * a := (Nat.mul_div_cancel' hpn).symm
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at hna; omega
    · exact h0
  have hapow : ∀ c, a ≠ p ^ c := by
    intro c hc
    exact hnpow ⟨c + 1, by omega, by rw [hna, hc, pow_succ, mul_comm]⟩
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · have h2 := hcop.2; rw [h0, Nat.gcd_zero_right] at h2; exact absurd h2 hp.one_lt.ne'
    · exact h0
  set S := Nat.sqrt t with hS
  -- Gfin ⊆ range r so t ≤ r
  have hsub : Gfin n p r ⊆ Finset.range r := by
    intro x hx
    simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, -, j, -, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hr)
  have htr : t ≤ r := by rw [ht]; simpa using Finset.card_le_card hsub
  have hmaps : Set.MapsTo (fun q : ℕ × ℕ => (a ^ q.1 * p ^ q.2) % r)
      ↑(Finset.range (S + 1) ×ˢ Finset.range (S + 1)) ↑(Gfin n p r) := by
    intro q hq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hq
    simp only [Finset.mem_coe, Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    by_cases hSr : S < r
    · exact ⟨q.1, by omega, q.2, by omega, rfl⟩
    · have hSS : S * S ≤ t := Nat.sqrt_le t
      have hr1 : r = 1 := by
        have : r ≤ S := by omega
        nlinarith
      refine ⟨0, by omega, 0, by omega, ?_⟩
      rw [hr1, Nat.mod_one, Nat.mod_one]
  have hcard : (Gfin n p r).card < (Finset.range (S + 1) ×ˢ Finset.range (S + 1)).card := by
    rw [Finset.card_product, Finset.card_range, ← ht]
    exact Nat.lt_succ_sqrt t
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_product, Finset.mem_range] at hx hy
  -- the key consequence
  have key : ∀ m₁ m₂ : ℕ, inI n p m₁ → inI n p m₂ → m₁ % r = m₂ % r → ∀ f, inP p ℓ f →
      Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂ := by
    intro m₁ m₂ h1 h2 hmod f hf
    rw [g71b_intro_eval h f hdiv (hintros m₁ h1 f hf), g71b_intro_eval h f hdiv (hintros m₂ h2 f hf),
      g71b_pow_mod _ r m₁ (g71b_root_pow_r h hdiv), g71b_pow_mod _ r m₂ (g71b_root_pow_r h hdiv), hmod]
  have hbound : ∀ q : ℕ × ℕ, q.1 < S + 1 → q.2 < S + 1 → a ^ q.1 * p ^ q.2 ≤ n ^ S := by
    intro q h1 h2
    rw [hna, mul_pow, mul_comm (p ^ S)]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right ha (by omega))
      (Nat.pow_le_pow_right hp.pos (by omega))
  have hne : a ^ x.1 * p ^ x.2 ≠ a ^ y.1 * p ^ y.2 := by
    intro heq
    rcases lt_trichotomy x.1 y.1 with hlt | heq1 | hgt
    · exact g71b_inj a p hp ha hapow _ _ _ _ hlt heq.symm
    · rw [heq1] at heq
      have := Nat.eq_of_mul_eq_mul_left (pow_pos ha _) heq
      have := Nat.pow_right_injective hp.two_le this
      exact hxy (Prod.ext heq1 this)
    · exact g71b_inj a p hp ha hapow _ _ _ _ hgt heq
  have hIx : inI n p (a ^ x.1 * p ^ x.2) := ⟨x.1, x.2, rfl⟩
  have hIy : inI n p (a ^ y.1 * p ^ y.2) := ⟨y.1, y.2, rfl⟩
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact ⟨_, _, hl, hbound y hy.1 hy.2, key _ _ hIy hIx hfxy.symm⟩
  · exact ⟨_, _, hl, hbound x hx.1 hx.2, key _ _ hIx hIy hfxy⟩

theorem g71b_group_inj (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hprim : ∀ k : ℕ, 0 < k → k < r →
      ¬ h ∣ (Polynomial.X ^ k - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (ht : t ≤ (Gfin n p r).card)
    (f g : Polynomial (ZMod p)) (hf : inP p ℓ f) (hg : inP p ℓ g)
    (hne : f ≠ g) (hft : Polynomial.natDegree f < t)
    (hgt : Polynomial.natDegree g < t) :
    Polynomial.aeval (AdjoinRoot.root h) f
      ≠ Polynomial.aeval (AdjoinRoot.root h) g := by
  intro hfg
  set ζ := AdjoinRoot.root h with hζ
  have hζr : ζ ^ r = 1 := g71b_root_pow_r h hdiv
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have : Gfin n p r = ∅ := by
        rw [h0]; simp [Gfin]
      rw [this] at ht; simp at ht; omega
    · exact h0
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, zero_pow hr.ne'] at hζr; exact zero_ne_one hζr
  have hζk : ∀ k, 0 < k → k < r → ζ ^ k ≠ 1 := by
    intro k hk hkr hk1
    apply hprim k hk hkr
    have h2 : Polynomial.aeval ζ (Polynomial.X ^ k - 1 : Polynomial (ZMod p)) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hk1, sub_self]
    rwa [hζ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k) ↑(Gfin n p r) := by
    have hlt : ∀ k ∈ Gfin n p r, k < r := by
      intro x hx
      simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, -, j, -, rfl⟩ := hx
      exact Nat.mod_lt _ hr
    have key : ∀ k1 k2, k1 < k2 → k2 < r → ζ ^ k1 ≠ ζ ^ k2 := by
      intro k1 k2 h12 h2r heq
      have : ζ ^ k2 = ζ ^ k1 * ζ ^ (k2 - k1) := by rw [← pow_add]; congr 1; omega
      rw [this] at heq
      have h3 : ζ ^ (k2 - k1) = 1 :=
        mul_left_cancel₀ (pow_ne_zero k1 hζ0) (heq.symm.trans (mul_one _).symm)
      exact hζk (k2 - k1) (by omega) (by omega) h3
    intro k1 hk1 k2 hk2 heq
    simp only at heq
    have h1 := hlt k1 hk1
    have h2 := hlt k2 hk2
    rcases lt_trichotomy k1 k2 with hl | he | hl
    · exact absurd heq (key _ _ hl h2)
    · exact he
    · exact absurd heq.symm (key _ _ hl h1)
  set Q : Polynomial (AdjoinRoot h) := (f - g).map (algebraMap (ZMod p) (AdjoinRoot h)) with hQ
  have hQ0 : Q ≠ 0 := by
    rw [hQ, Polynomial.map_ne_zero_iff (algebraMap (ZMod p) (AdjoinRoot h)).injective]
    exact sub_ne_zero.2 hne
  have hQdeg : Q.natDegree < t := by
    calc Q.natDegree ≤ (f - g).natDegree := Polynomial.natDegree_map_le
      _ ≤ max f.natDegree g.natDegree := Polynomial.natDegree_sub_le f g
      _ < t := max_lt hft hgt
  have hsub : ((Gfin n p r).image (fun k : ℕ => ζ ^ k)).val ⊆ Q.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' := hk
    simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hk'
    obtain ⟨i, -, j, -, hkij⟩ := hk'
    have hI : inI n p ((n / p) ^ i * p ^ j) := ⟨i, j, rfl⟩
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ, Polynomial.eval_map_algebraMap,
      ← hkij, ← g71b_pow_mod ζ r _ hζr, map_sub,
      ← g71b_intro_eval h f hdiv (hintros _ hI f hf),
      ← g71b_intro_eval h g hdiv (hintros _ hI g hg), ← hζ, hfg, sub_self]
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  omega



theorem g71a_lcmFirst_succ (m : ℕ) : lcmFirst (m + 1) = Nat.lcm (lcmFirst m) (m + 1) := by
  unfold lcmFirst
  rw [List.range_succ, List.foldl_append]
  rfl

theorem g71a_lcmFirst_pos (m : ℕ) : 0 < lcmFirst m := by
  induction m with
  | zero => decide
  | succ m ih => rw [g71a_lcmFirst_succ]; exact Nat.lcm_pos ih (by omega)

theorem g71a_dvd_lcmFirst {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : j ∣ lcmFirst m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
    · have : j = m + 1 := by omega
      subst this; exact Nat.dvd_lcm_right _ _

theorem g71a_lcmFirst_dvd {m Q : ℕ} (h : ∀ j, 1 ≤ j → j ≤ m → j ∣ Q) : lcmFirst m ∣ Q := by
  induction m with
  | zero => exact one_dvd _
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    exact Nat.lcm_dvd (ih fun j h1 h2 => h j h1 (by omega)) (h _ (by omega) le_rfl)

theorem g71a_lcmFirst_mono {m m' : ℕ} (h : m ≤ m') : lcmFirst m ∣ lcmFirst m' :=
  g71a_lcmFirst_dvd fun _ h1 h2 => g71a_dvd_lcmFirst h1 (le_trans h2 h)

/-- closed form step -/
theorem g71a_step (N k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / (k * (N + 1 + k).choose k) =
      1 / (k * (N + k).choose k) - 1 / ((k + 1 : ℕ) * (N + k + 1).choose (k + 1)) := by
  have hB := Nat.choose_mul_succ_eq (N + k) k
  have hC := Nat.add_one_mul_choose_eq (N + k) k
  have e1 : N + k + 1 - k = N + 1 := by omega
  rw [e1] at hB
  have e2 : N + 1 + k = N + k + 1 := by omega
  rw [e2]
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hB0 : ((N + k + 1).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC0 : ((N + k + 1).choose (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hBq : ((N + k).choose k : ℚ) * (N + k + 1) = ((N + k + 1).choose k) * (N + 1) := by
    exact_mod_cast hB
  have hCq : ((N + k + 1 : ℕ) : ℚ) * ((N + k).choose k) = ((N + k + 1).choose (k + 1)) * (k + 1) := by
    exact_mod_cast hC
  push_cast at hCq ⊢
  have hN1 : (N : ℚ) + 1 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have hB' : ((N + k + 1).choose k : ℚ) = ((N + k).choose k) * (N + k + 1) / (N + 1) := by
    rw [hBq]; field_simp
  have hC' : ((N + k + 1).choose (k + 1) : ℚ) = (N + k + 1) * ((N + k).choose k) / (k + 1) := by
    rw [hCq]; field_simp
  rw [hB', hC']
  field_simp
  ring

theorem g71a_sum_identity (N : ℕ) : ∀ k : ℕ, 1 ≤ k →
    (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
      1 / (k * (N + k).choose k) := by
  induction N with
  | zero => intro k hk; simp
  | succ N ih =>
    intro k hk
    have ih2 := ih (k + 1) (by omega)
    rw [show N + (k + 1) = N + k + 1 by omega] at ih2
    rw [g71a_step N k hk, ← ih k hk, ← ih2]
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (i + 1) * ((N + 1).choose (i + 1) : ℕ) / ((k + (i + 1) : ℕ) : ℚ)
        = -((-1 : ℚ) ^ i * (N.choose i) / ((k + 1 + i : ℕ) : ℚ)) +
          (-1 : ℚ) ^ (i + 1) * (N.choose (i + 1)) / ((k + (i + 1) : ℕ) : ℚ) := by
      intro i _
      rw [Nat.choose_succ_succ', show k + (i + 1) = k + 1 + i by omega]
      push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have h2 : (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
        (∑ i ∈ Finset.range (N + 1 + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) := by
      rw [Finset.sum_range_succ _ (N + 1)]; simp
    rw [h2, Finset.sum_range_succ' _ (N + 1)]
    simp
    ring

theorem g71a_kchoose_dvd (N k : ℕ) (hk : 1 ≤ k) :
    k * (N + k).choose k ∣ lcmFirst (N + k) := by
  set L := lcmFirst (N + k) with hL
  have hdv : ∀ i ∈ Finset.range (N + 1), (k + i) ∣ L := fun i hi =>
    g71a_dvd_lcmFirst (by omega) (by simp at hi; omega)
  set z : ℤ := ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (N.choose i) * ((L / (k + i) : ℕ) : ℤ)
  have hz : (L : ℚ) * (1 / (k * (N + k).choose k)) = z := by
    rw [← g71a_sum_identity N k hk, Finset.mul_sum]
    simp only [z]; rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : ((k + i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : k + i ≠ 0)
    have hq : ((L / (k + i) : ℕ) : ℚ) = (L : ℚ) / ((k + i : ℕ) : ℚ) := Nat.cast_div (hdv i hi) hne
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [hq]; field_simp
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hz2 : (L : ℚ) = (z : ℚ) * (k * (N + k).choose k) := by
    rw [← hz]; field_simp
  have hz3 : (L : ℤ) = z * ((k * (N + k).choose k : ℕ) : ℤ) := by
    push_cast; exact_mod_cast hz2
  have : ((k * (N + k).choose k : ℕ) : ℤ) ∣ (L : ℤ) := ⟨z, by rw [hz3]; ring⟩
  exact_mod_cast this

theorem g71a_lcm_lower (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ lcmFirst m := by
  have odd_case : ∀ t, 2 ≤ t → t * 4 ^ t ≤ lcmFirst (2 * t + 1) := by
    intro t ht
    have h1 : t * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t t (by omega)
      rw [show t + t = 2 * t by ring] at this
      exact dvd_trans this (g71a_lcmFirst_mono (by omega))
    have h2 : (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t (t + 1) (by omega)
      rw [show t + (t + 1) = 2 * t + 1 by ring] at this
      have e := Nat.add_one_mul_choose_eq (2 * t) t
      rw [show (2 * t + 1).choose (t + 1) * (t + 1) = (t + 1) * (2 * t + 1).choose (t + 1) by ring] at e
      rw [e]; exact this
    have hcop : Nat.Coprime t (2 * t + 1) := by
      simp
    have h3 : t * (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := Nat.lcm_dvd h1 h2
      rwa [Nat.lcm_mul_right, hcop.lcm_eq_mul] at this
    have h4 := Nat.le_of_dvd (g71a_lcmFirst_pos _) h3
    have h5 := Nat.four_pow_le_two_mul_add_one_mul_central_binom t
    calc t * 4 ^ t ≤ t * ((2 * t + 1) * (2 * t).choose t) := Nat.mul_le_mul_left _ h5
      _ = t * (2 * t + 1) * (2 * t).choose t := by ring
      _ ≤ _ := h4
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t + 1 ∨ m = 2 * t + 2 := ⟨(m - 1) / 2, by omega⟩
  · have := odd_case t (by omega)
    calc 2 ^ (2 * t + 1) = 2 * 4 ^ t := by rw [pow_succ, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := this
  · rcases Nat.lt_or_ge t 4 with h | h
    · have : t = 3 := by omega
      subst this; decide
    have := odd_case t (by omega)
    have hd := Nat.le_of_dvd (g71a_lcmFirst_pos _) (g71a_lcmFirst_mono (by omega : 2 * t + 1 ≤ 2 * t + 2))
    calc 2 ^ (2 * t + 2) = 4 * 4 ^ t := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ h
      _ ≤ _ := this
      _ ≤ _ := hd

theorem g71a_ordR_spec (r n : ℕ) (hr : 1 < r) (hc : Nat.Coprime n r) :
    0 < ordR r n ∧ n ^ ordR r n % r = 1 % r := by
  have hmem : Nat.totient r ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨Nat.totient_lt r hr, Nat.totient_pos.2 (by omega), Nat.ModEq.pow_totient hc⟩
  unfold ordR
  split
  next h => rw [h] at hmem; simp at hmem
  next k t h =>
    have : k ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
      rw [h]; exact List.mem_cons_self
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at this
    exact this.2

theorem g71a_coprime_part (j n E : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n) (hjE : j < 2 ^ (E + 1)) :
    Nat.Coprime (j / Nat.gcd j (n ^ E)) n := by
  apply Nat.coprime_of_dvd
  intro p hp hpc hpn
  have hg : Nat.gcd j (n ^ E) ∣ j := Nat.gcd_dvd_left _ _
  have hc0 : j / Nat.gcd j (n ^ E) ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (by omega) hg) (Nat.gcd_pos_of_pos_left _ (by omega))
    omega
  have h1 := (hp.dvd_iff_one_le_factorization hc0).1 hpc
  have hnE : n ^ E ≠ 0 := by positivity
  rw [Nat.factorization_div hg, Nat.factorization_gcd (by omega) hnE] at h1
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul] at h1
  have hnp := (hp.dvd_iff_one_le_factorization (by omega)).1 hpn
  have h2 : E + 1 ≤ j.factorization p := by
    rcases le_total (j.factorization p) (E * n.factorization p) with h | h
    · rw [min_eq_left h] at h1; omega
    · rw [min_eq_right h] at h1
      have : E ≤ E * n.factorization p := Nat.le_mul_of_pos_right _ hnp
      omega
  have h3 : p ^ (E + 1) ∣ j := dvd_trans (pow_dvd_pow p h2) (Nat.ordProj_dvd j p)
  have h4 := Nat.le_of_dvd (by omega) h3
  have h5 : 2 ^ (E + 1) ≤ p ^ (E + 1) := Nat.pow_le_pow_left hp.two_le _
  omega

theorem g71a_r_exists_main (n : ℕ) (hn : 1 < n) :
    ∃ r, 1 < r ∧ r ≤ max 3 ((logUp n) ^ 5) ∧ (logUp n) ^ 2 < ordR r n := by
  set L := logUp n with hLdef
  have hnL : n < 2 ^ L := Nat.lt_log2_self
  have hL2 : 2 ≤ L := by
    have : 1 ≤ Nat.log2 n := by
      rw [Nat.log2_eq_log_two]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    simp only [hLdef, logUp]; omega
  set B := L ^ 5 with hB
  have hB32 : 32 ≤ B := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ L ^ 5 := Nat.pow_le_pow_left hL2 5
  have hmax : max 3 B = B := by omega
  rw [hmax]
  by_contra hcon
  push Not at hcon
  set M := L ^ 2 with hM
  set E := Nat.log 2 B with hE
  set P := ∏ i ∈ Finset.range M, (n ^ (i + 1) - 1) with hP
  set Q := n ^ E * P with hQ
  have hPpos : 0 < P := Finset.prod_pos fun i _ => by
    have := Nat.one_lt_pow (by omega : i + 1 ≠ 0) hn; omega
  have hQpos : 0 < Q := Nat.mul_pos (by positivity) hPpos
  -- every j ≤ B divides Q
  have hdiv : lcmFirst B ∣ Q := by
    apply g71a_lcmFirst_dvd
    intro j hj1 hjB
    set a := Nat.gcd j (n ^ E)
    have hjeq : j = a * (j / a) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have hcop : Nat.Coprime (j / a) n :=
      g71a_coprime_part j n E hj1 (by omega)
        (lt_of_le_of_lt hjB (Nat.lt_pow_succ_log_self (by norm_num) B))
    have hc1 : j / a ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hjeq; omega
    have hcP : j / a ∣ P := by
      rcases Nat.lt_or_ge (j / a) 2 with h | h
      · have : j / a = 1 := by
          generalize j / a = c at h hc1
          omega
        rw [this]; exact one_dvd _
      · have hle : j / a ≤ B := le_trans (Nat.div_le_self _ _) hjB
        have hord := hcon (j / a) (by omega) hle
        obtain ⟨hk0, hk⟩ := g71a_ordR_spec (j / a) n (by omega) hcop.symm
        have hdk : j / a ∣ n ^ ordR (j / a) n - 1 :=
          (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 hk.symm
        refine dvd_trans hdk ?_
        have hmem : ordR (j / a) n - 1 ∈ Finset.range M := by
          simp only [Finset.mem_range]; omega
        have := Finset.dvd_prod_of_mem (fun i => n ^ (i + 1) - 1) hmem
        rwa [Nat.sub_add_cancel (by omega)] at this
    rw [hjeq]
    exact mul_dvd_mul (Nat.gcd_dvd_right _ _) hcP
  have hlow : 2 ^ B ≤ lcmFirst B := g71a_lcm_lower B (by omega)
  have hle : lcmFirst B ≤ Q := Nat.le_of_dvd hQpos hdiv
  -- upper bound on Q
  set s := E + ∑ i ∈ Finset.range M, (i + 1) with hs
  have hQs : Q ≤ n ^ s := by
    have : P ≤ ∏ i ∈ Finset.range M, n ^ (i + 1) :=
      Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
    rw [Finset.prod_pow_eq_pow_sum] at this
    rw [hs, pow_add]
    exact Nat.mul_le_mul_left _ this
  have hsum : (∑ i ∈ Finset.range M, (i + 1)) * 2 = M * (M - 1) + 2 * M := by
    rw [Finset.sum_add_distrib, add_mul, Finset.sum_range_id_mul_two]; simp; ring
  have hM4 : 4 ≤ M := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ L ^ 2 := Nat.pow_le_pow_left hL2 2
  have hEb : 2 * E + M ≤ M * M := by
    have h2E : 2 ^ E ≤ B := Nat.pow_log_le_self 2 (by omega)
    rcases Nat.lt_or_ge L 3 with h | h
    · have hL : L = 2 := by omega
      have : E = 5 := by
        rw [hE]; apply Nat.log_eq_of_pow_le_of_lt_pow <;> rw [hB, hL] <;> norm_num
      rw [this, hM, hL]; norm_num
    · have h5 : E < 5 * L := by
        have : B < 2 ^ (5 * L) := by
          rw [hB, pow_mul']
          exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
        have := lt_of_le_of_lt h2E this
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
      rw [hM]
      have hL3 : 9 ≤ L * L := by nlinarith
      nlinarith
  have hsle : s ≤ M * M := by
    have : (M - 1) * M + M = M * M := by
      rcases M with _ | M
      · omega
      · simp; ring
    have h1 : s * 2 = 2 * E + M * (M - 1) + 2 * M := by rw [hs, add_mul, hsum]; ring
    have h2 : M * (M - 1) = (M - 1) * M := by ring
    omega
  have hspos : s ≠ 0 := by
    have : 0 < ∑ i ∈ Finset.range M, (i + 1) :=
      Finset.sum_pos (fun i _ => by omega) ⟨0, by simp; omega⟩
    omega
  have hup : n ^ s < 2 ^ B := by
    calc n ^ s < (2 ^ L) ^ s := Nat.pow_lt_pow_left hnL hspos
      _ = 2 ^ (L * s) := by rw [← pow_mul]
      _ ≤ 2 ^ B := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : L * s ≤ L * (M * M) := Nat.mul_le_mul_left _ hsle
        calc L * s ≤ L * (M * M) := this
          _ = B := by rw [hB, hM]; ring
  omega

theorem g71b_r_exists (n : ℕ) (hn : 1 < n) :
    ∃ r, 1 < r ∧ r ≤ max 3 ((logUp n) ^ 5) ∧ (logUp n) ^ 2 < ordR r n :=
  g71a_r_exists_main n hn

theorem g71b_smallestR_spec (n : ℕ) (hn : 1 < n) :
    1 < smallestR n ∧ logUp n ^ 2 < ordR (smallestR n) n := by
  obtain ⟨r0, hr0, hr0w, hr0o⟩ := g71b_r_exists n hn
  have hmem0 : r0 ∈ (List.range (max 3 ((logUp n) ^ 5) + 1)).filter
      (fun r => decide (1 < r ∧ logUp n ^ 2 < ordR r n)) := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨by omega, by simp [hr0, hr0o]⟩
  unfold smallestR
  split
  next h => rw [h] at hmem0; simp at hmem0
  next r l h =>
    have hm : r ∈ (List.range (max 3 ((logUp n) ^ 5) + 1)).filter
        (fun r => decide (1 < r ∧ logUp n ^ 2 < ordR r n)) := by
      rw [h]; exact List.mem_cons_self
    rw [List.mem_filter] at hm
    simpa using hm.2

theorem g71b_ordR_spec (r n : ℕ) (ho : 0 < ordR r n) :
    ordR r n < r ∧ n ^ ordR r n % r = 1 % r ∧
      ∀ k, 0 < k → k < ordR r n → n ^ k % r ≠ 1 % r := by
  have hsort : ((List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r))).Pairwise
      (· < ·) := List.pairwise_lt_range.filter _
  revert ho hsort
  unfold ordR
  split
  next h => intro ho; omega
  next k l h =>
    intro _ hsort
    rw [h] at hsort
    have hm : k ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
      rw [h]; exact List.mem_cons_self
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
    refine ⟨hm.1, hm.2.2, ?_⟩
    intro k' hk' hk'k heq
    have hm' : k' ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hk', heq⟩
    rw [h, List.mem_cons] at hm'
    rcases hm' with h1 | h1
    · omega
    · have := List.rel_of_pairwise_cons hsort h1
      omega

theorem g71b_Gfin_lt (n p r : ℕ) (hr : 0 < r) : ∀ k ∈ Gfin n p r, k < r := by
  intro x hx
  simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, -, j, -, rfl⟩ := hx
  exact Nat.mod_lt _ hr

theorem g71b_Gfin_le_totient (n p r : ℕ) (hr : 0 < r) (h1 : Nat.Coprime (n / p) r)
    (h2 : Nat.Coprime p r) : (Gfin n p r).card ≤ Nat.totient r := by
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_le_card
  intro x hx
  simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, -, j, -, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ hr, ?_⟩
  have hc : Nat.Coprime ((n / p) ^ i * p ^ j) r := Nat.Coprime.mul_left (h1.pow_left _) (h2.pow_left _)
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
  exact hc

theorem g71b_ord_le_Gfin (n p r : ℕ) (hr : 1 < r) (hpn : p ∣ n) (hc : Nat.Coprime n r)
    (ho : 0 < ordR r n) : ordR r n ≤ (Gfin n p r).card := by
  obtain ⟨hor, -, hmin⟩ := g71b_ordR_spec r n ho
  have hsub : (Finset.range (ordR r n)).image (fun k => n ^ k % r) ⊆ Gfin n p r := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    refine ⟨k, by omega, k, by omega, ?_⟩
    rw [← mul_pow, Nat.div_mul_cancel hpn]
  have hinj : Set.InjOn (fun k => n ^ k % r) ↑(Finset.range (ordR r n)) := by
    have key : ∀ k1 k2, k1 < k2 → k2 < ordR r n → n ^ k1 % r ≠ n ^ k2 % r := by
      intro k1 k2 h12 h2 heq
      have e : n ^ k2 = n ^ k1 * n ^ (k2 - k1) := by rw [← pow_add]; congr 1; omega
      have hm : n ^ k1 * n ^ (k2 - k1) ≡ n ^ k1 * 1 [MOD r] := by
        rw [mul_one, ← e]; exact heq.symm
      have := Nat.ModEq.cancel_left_of_coprime (by
        rw [Nat.gcd_comm]; exact (hc.pow_left k1)) hm
      exact hmin (k2 - k1) (by omega) (by omega) this
    intro k1 hk1 k2 hk2 heq
    simp only [Finset.coe_range, Set.mem_Iio] at hk1 hk2
    rcases lt_trichotomy k1 k2 with h | h | h
    · exact absurd heq (key _ _ h hk2)
    · exact h
    · exact absurd heq.symm (key _ _ h hk1)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at this


open Polynomial in
theorem g71b_closure (p r : ℕ)
    (f g : Polynomial (ZMod p)) (m m' : ℕ)
    (hm : introspective p r f m) (hm' : introspective p r f m')
    (hgm : introspective p r g m) :
    introspective p r f (m * m') ∧ introspective p r (f * g) m := by
  unfold introspective at *
  constructor
  · have h1 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (f ^ m) ^ m' - (f.comp (X ^ m)) ^ m' :=
      dvd_trans hm (sub_dvd_pow_sub_pow _ _ _)
    have h2 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (f.comp (X ^ m)) ^ m' - f.comp (X ^ (m * m')) := by
      obtain ⟨c, hc⟩ := hm'
      have h3 : (f ^ m' - f.comp (X ^ m')).comp (X ^ m)
          = ((X ^ r - 1 : Polynomial (ZMod p)).comp (X ^ m)) * c.comp (X ^ m) := by
        rw [hc, mul_comp]
      have h4 : (X ^ r - 1 : Polynomial (ZMod p)) ∣ (X ^ r - 1 : Polynomial (ZMod p)).comp (X ^ m) := by
        have := sub_dvd_pow_sub_pow (X ^ r : Polynomial (ZMod p)) 1 m
        simpa [sub_comp, pow_comp, ← pow_mul, mul_comm] using this
      have h5 : (f ^ m' - f.comp (X ^ m')).comp (X ^ m)
          = (f.comp (X ^ m)) ^ m' - f.comp (X ^ (m * m')) := by
        rw [sub_comp, pow_comp, comp_assoc, X_pow_comp, ← pow_mul]
      rw [← h5, h3]
      exact dvd_mul_of_dvd_left h4 _
    have := dvd_add h1 h2
    rw [pow_mul]
    convert this using 1
    ring
  · have := dvd_add (dvd_mul_of_dvd_left hm (g ^ m)) (dvd_mul_of_dvd_right hgm (f.comp (X ^ m)))
    rw [mul_pow, mul_comp]
    convert this using 1
    ring

open Polynomial in
theorem g71b_intro_one_m (p r : ℕ) (f : Polynomial (ZMod p)) : introspective p r f 1 := by
  unfold introspective; simp

open Polynomial in
theorem g71b_intro_one_f (p r m : ℕ) : introspective p r (1 : Polynomial (ZMod p)) m := by
  unfold introspective; simp

open Polynomial in
theorem g71b_intro_p (p r : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)) : introspective p r f p := by
  unfold introspective
  rw [← expand_eq_comp_X_pow, ZMod.expand_card, sub_self]; exact dvd_zero _

open Polynomial in
theorem g71b_intro_div (p r k : ℕ) [Fact p.Prime] (hpr : ¬ p ∣ r) (f : Polynomial (ZMod p))
    (h : introspective p r f (p * k)) : introspective p r f k := by
  unfold introspective at *
  have e : f ^ (p * k) - f.comp (X ^ (p * k)) = (f ^ k - f.comp (X ^ k)) ^ p := by
    rw [sub_pow_char, ← pow_mul, mul_comm k p]
    congr 1
    rw [← ZMod.expand_card, expand_eq_comp_X_pow, comp_assoc, X_pow_comp, ← pow_mul]
  rw [e] at h
  have hr0 : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpr
  have hsep : Separable (X ^ r - C (1 : ZMod p)) := separable_X_pow_sub_C 1 hr0 one_ne_zero
  rw [map_one] at hsep
  exact (hsep.squarefree.dvd_pow_iff_dvd (Fact.out : p.Prime).ne_zero).1 h

open Polynomial in
theorem g71b_intro_n_lin (n p r a : ℕ) [Fact p.Prime] (hpn : p ∣ n) (hc : cycCong n r a) :
    introspective p r (X + C (a : ZMod p)) n := by
  unfold cycCong at hc
  unfold introspective
  have := Polynomial.map_dvd (ZMod.castHom hpn (ZMod p)) hc
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_add, map_natCast] at this
  simpa [add_comp] using this

theorem g71b_cycCong_zero (n r : ℕ) : cycCong n r 0 := by
  unfold cycCong; simp

theorem g71b_intro_pow_m (p r : ℕ) (f : Polynomial (ZMod p)) (m : ℕ) (hm : introspective p r f m) :
    ∀ i, introspective p r f (m ^ i) := by
  intro i
  induction i with
  | zero => simpa using g71b_intro_one_m p r f
  | succ i ih => rw [pow_succ]; exact (g71b_closure p r f f _ _ ih hm ih).1

theorem g71b_intro_pow_f (p r : ℕ) (f : Polynomial (ZMod p)) (m : ℕ) (hm : introspective p r f m) :
    ∀ e, introspective p r (f ^ e) m := by
  intro e
  induction e with
  | zero => simpa using g71b_intro_one_f p r m
  | succ e ih => rw [pow_succ]; exact (g71b_closure p r _ f _ _ ih ih hm).2

open Polynomial in
theorem g71b_intros (n p r ℓ : ℕ) [Fact p.Prime] (hpn : p ∣ n) (hpr : ¬ p ∣ r)
    (h5 : ∀ a, 1 ≤ a → a ≤ ℓ → cycCong n r a) :
    ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m := by
  have hlin : ∀ a, a ≤ ℓ → ∀ m, inI n p m → introspective p r (X + C (a : ZMod p)) m := by
    intro a ha m hm
    have hn : introspective p r (X + C (a : ZMod p)) n := by
      apply g71b_intro_n_lin n p r a hpn
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0]; exact g71b_cycCong_zero n r
      · exact h5 a h0 ha
    have hnp : introspective p r (X + C (a : ZMod p)) (n / p) := by
      apply g71b_intro_div p r _ hpr
      rw [Nat.mul_div_cancel' hpn]; exact hn
    obtain ⟨i, j, rfl⟩ := hm
    exact (g71b_closure p r _ _ _ _ (g71b_intro_pow_m p r _ _ hnp i)
      (g71b_intro_pow_m p r _ _ (g71b_intro_p p r _) j) (g71b_intro_one_f p r _)).1
  intro m hm f hf
  obtain ⟨e, rfl⟩ := hf
  apply Finset.prod_induction _ (fun g => introspective p r g m)
  · intro g g' hg hg'; exact (g71b_closure p r g g' m m hg hg hg').2
  · exact g71b_intro_one_f p r m
  · intro a ha
    exact g71b_intro_pow_f p r _ m (hlin a (by simpa [Nat.lt_succ_iff] using ha) m hm) _

open Polynomial in
theorem g71b_field (p r : ℕ) [Fact p.Prime] (hr : 0 < r) (hpr : ¬ p ∣ r) :
    ∃ h : (ZMod p)[X], Irreducible h ∧ h ∣ X ^ r - 1 ∧ ∀ k, 0 < k → k < r → ¬ h ∣ X ^ k - 1 := by
  have hnu : ¬ IsUnit (cyclotomic r (ZMod p)) :=
    not_isUnit_of_degree_pos_of_isReduced _ (degree_cyclotomic_pos r _ hr)
  obtain ⟨h, hirr, hh⟩ := WfDvdMonoid.exists_irreducible_factor hnu (cyclotomic_ne_zero r _)
  refine ⟨h, hirr, dvd_trans hh (cyclotomic.dvd_X_pow_sub_one r _), ?_⟩
  have : Fact (Irreducible h) := ⟨hirr⟩
  intro k hk hkr hdk
  have hr0 : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpr
  have hrK : ((r : ℕ) : AdjoinRoot h) ≠ 0 := by
    rw [← map_natCast (algebraMap (ZMod p) (AdjoinRoot h))]
    exact fun h0 => hr0 ((map_eq_zero_iff _ (algebraMap (ZMod p) (AdjoinRoot h)).injective).1 h0)
  have : NeZero ((r : ℕ) : AdjoinRoot h) := ⟨hrK⟩
  have hroot : IsRoot (cyclotomic r (AdjoinRoot h)) (AdjoinRoot.root h) := by
    rw [← map_cyclotomic r (algebraMap (ZMod p) (AdjoinRoot h)), IsRoot,
      eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hh
  have hprim := (isRoot_cyclotomic_iff.1 hroot)
  have hk1 : AdjoinRoot.root h ^ k = 1 := by
    have h2 : aeval (AdjoinRoot.root h) (X ^ k - 1 : Polynomial (ZMod p)) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact hdk
    rwa [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h2
  have := Nat.le_of_dvd hk (hprim.dvd_of_pow_eq_one k hk1)
  omega

open Polynomial in
theorem g71b_prod_inP (p ℓ : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range (ℓ + 1)) :
    inP p ℓ (∏ a ∈ T, (X + C (a : ZMod p))) := by
  classical
  refine ⟨fun a => if a ∈ T then 1 else 0, ?_⟩
  have : ∀ a ∈ Finset.range (ℓ + 1), (X + C (a : ZMod p)) ^ (if a ∈ T then 1 else 0)
      = if a ∈ T then (X + C (a : ZMod p)) else 1 := by
    intro a _; split_ifs <;> simp
  rw [Finset.prod_congr rfl this, Finset.prod_ite_mem, Finset.inter_eq_right.2 hT]

open Polynomial in
theorem g71b_prod_natDegree (p : ℕ) [Fact p.Prime] (T : Finset ℕ) :
    (∏ a ∈ T, (X + C (a : ZMod p))).natDegree ≤ T.card := by
  refine (natDegree_prod_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun a _ => (natDegree_X_add_C _).le)

open Polynomial in
theorem g71b_prod_mem (p N : ℕ) [Fact p.Prime] (hN : N ≤ p) (T T' : Finset ℕ)
    (hT' : T' ⊆ Finset.range N)
    (he : ∏ a ∈ T, (X + C (a : ZMod p)) = ∏ a ∈ T', (X + C (a : ZMod p))) {a : ℕ} (ha : a ∈ T)
    (haN : a < N) : a ∈ T' := by
  have h1 : eval (-(a : ZMod p)) (∏ a ∈ T, (X + C (a : ZMod p))) = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero ha (by simp)
  rw [he, eval_prod, Finset.prod_eq_zero_iff] at h1
  obtain ⟨b, hb, hb0⟩ := h1
  simp only [eval_add, eval_X, eval_C] at hb0
  have hba : (b : ZMod p) = (a : ZMod p) := by linear_combination hb0
  have hbN := Finset.mem_range.1 (hT' hb)
  have := congrArg ZMod.val hba
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  rwa [← this]

open Polynomial in
theorem g71b_count (n p r ℓ N m₁ m₂ : ℕ) [Fact (Nat.Prime p)]
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hprim : ∀ k : ℕ, 0 < k → k < r →
      ¬ h ∣ (Polynomial.X ^ k - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (hNt : N < (Gfin n p r).card) (hNl : N ≤ ℓ + 1) (hNp : N ≤ p) (hm : m₂ < m₁)
    (hpow : ∀ f, inP p ℓ f →
        Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂) : 2 ^ N ≤ m₁ := by
  classical
  set F : Finset ℕ → Polynomial (ZMod p) := fun T => ∏ a ∈ T, (X + C (a : ZMod p)) with hF
  have hsubl : ∀ T ∈ (Finset.range N).powerset, T ⊆ Finset.range (ℓ + 1) := by
    intro T hT
    exact (Finset.mem_powerset.1 hT).trans (Finset.range_subset_range.2 hNl)
  have hdeg : ∀ T ∈ (Finset.range N).powerset, (F T).natDegree < (Gfin n p r).card := by
    intro T hT
    have := Finset.card_le_card (Finset.mem_powerset.1 hT)
    rw [Finset.card_range] at this
    exact lt_of_le_of_lt ((g71b_prod_natDegree p T).trans this) hNt
  have hinj : Set.InjOn (fun T => aeval (AdjoinRoot.root h) (F T)) ↑(Finset.range N).powerset := by
    intro T hT T' hT' heq
    by_contra hne
    have hFne : F T ≠ F T' := by
      intro hFe
      apply hne
      have s1 := Finset.mem_powerset.1 hT
      have s2 := Finset.mem_powerset.1 hT'
      ext a
      constructor
      · intro ha; exact g71b_prod_mem p N hNp T T' s2 hFe ha (Finset.mem_range.1 (s1 ha))
      · intro ha; exact g71b_prod_mem p N hNp T' T s1 hFe.symm ha (Finset.mem_range.1 (s2 ha))
    exact g71b_group_inj n p r _ ℓ h hdiv hprim hintros le_rfl (F T) (F T')
      (g71b_prod_inP p ℓ T (hsubl T hT)) (g71b_prod_inP p ℓ T' (hsubl T' hT')) hFne
      (hdeg T hT) (hdeg T' hT') heq
  set Q : Polynomial (AdjoinRoot h) := X ^ m₁ - X ^ m₂ with hQ
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := congrArg (fun q => coeff q m₁) h0
    simp only [hQ, coeff_sub, coeff_X_pow, if_neg (Nat.ne_of_gt hm), coeff_zero] at this
    simp at this
  have hQdeg : Q.natDegree ≤ m₁ := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_X_pow_le _
    · exact (natDegree_X_pow_le _).trans hm.le
  have hsub : ((Finset.range N).powerset.image (fun T => aeval (AdjoinRoot.root h) (F T))).val
      ⊆ Q.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨T, hT, rfl⟩ := hx
    rw [mem_roots hQ0, IsRoot, hQ, eval_sub, eval_pow, eval_pow, eval_X,
      hpow _ (g71b_prod_inP p ℓ T (hsubl T hT)), sub_self]
  have hc := card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_range] at hc
  omega


open Polynomial in
theorem g71b_cycCong_prime (n r a : ℕ) (hp : n.Prime) : cycCong n r a := by
  have := Fact.mk hp
  unfold cycCong
  have : ((X + C (a : ZMod n)) ^ n : Polynomial (ZMod n)) = X ^ n + C (a : ZMod n) := by
    rw [add_pow_char, ← C_pow, ZMod.pow_card]
  rw [this, sub_self]; exact dvd_zero _

theorem g71b_prime_not_isPow (n : ℕ) (hp : n.Prime) : ¬ isPow n := by
  rintro ⟨a, b, ha, hb, rfl⟩
  have h1 : a ∣ a ^ b := dvd_pow_self a (by omega)
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · omega
  · have : a ^ 1 < a ^ b := Nat.pow_lt_pow_right ha hb
    rw [pow_one] at this; omega

theorem g71b_hard (n : ℕ) (hn : 1 < n) (hpow : ¬ isPow n)
    (h3 : ¬ ∃ a, a ≤ smallestR n ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n)
    (hnr : smallestR n < n)
    (h5 : ∀ a, 1 ≤ a → a ≤ ell (smallestR n) n → cycCong n (smallestR n) a) : n.Prime := by
  by_contra hnp
  obtain ⟨hr1, ho⟩ := g71b_smallestR_spec n hn
  set r := smallestR n with hrdef
  set L := logUp n with hLdef
  have hbig : ∀ q, q.Prime → q ∣ n → r < q := by
    intro q hq hqn
    by_contra hle
    apply h3
    refine ⟨q, by omega, ?_⟩
    rw [Nat.gcd_eq_left hqn]
    refine ⟨hq.one_lt, lt_of_le_of_ne (Nat.le_of_dvd (by omega) hqn) ?_⟩
    rintro rfl; exact hnp hq
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hrp : r < p := hbig p hp hpn
  have := Fact.mk hp
  have hcn : Nat.Coprime n r := by
    apply Nat.coprime_of_dvd
    intro k hk hkn hkr
    have := hbig k hk hkn
    have := Nat.le_of_dvd (by omega) hkr
    omega
  have hpr : ¬ p ∣ r := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hc1 : Nat.Coprime (n / p) r := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hpn) hcn
  have hc2 : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpn hcn
  have ho0 : 0 < ordR r n := by omega
  set t := (Gfin n p r).card with htdef
  have hot : ordR r n ≤ t := g71b_ord_le_Gfin n p r hr1 hpn hcn ho0
  have htφ : t ≤ Nat.totient r := g71b_Gfin_le_totient n p r (by omega) hc1 hc2
  have hφr : Nat.totient r < r := Nat.totient_lt r hr1
  obtain ⟨h, hirr, hdiv, hprim⟩ := g71b_field p r (by omega) hpr
  have : Fact (Irreducible h) := ⟨hirr⟩
  have hintros := g71b_intros n p r (ell r n) hpn hpr h5
  have hnpow : ¬ ∃ k, 0 < k ∧ n = p ^ k := by
    rintro ⟨k, hk, hnk⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      rw [this, pow_one] at hnk; exact hnp (hnk ▸ hp)
    · exact hpow ⟨p, k, hp.one_lt, by omega, hnk⟩
  obtain ⟨m₁, m₂, hm, hm₁, hpw⟩ := g71b_group_upper n p r t (ell r n) hpn (by omega) h hdiv hintros
    hnpow rfl ⟨hc1, hc2⟩
  set S := Nat.sqrt t with hS
  have hSS : S * S ≤ t := Nat.sqrt_le t
  have hS1 : 1 ≤ S := by
    rw [hS, Nat.le_sqrt]; nlinarith
  have hL2 : L * L < t := by nlinarith
  have hNt : L * S < t := by
    by_contra hle
    push Not at hle
    have h1 : t * t ≤ (L * S) * (L * S) := Nat.mul_le_mul hle hle
    have h2 : (L * L) * (S * S) < t * (S * S) := Nat.mul_lt_mul_of_pos_right hL2 (by nlinarith)
    have h3 : t * (S * S) ≤ t * t := Nat.mul_le_mul_left _ hSS
    nlinarith
  have hNl : L * S ≤ ell r n + 1 := by
    have : L * S ≤ ell r n := by
      unfold ell
      rw [← hLdef, Nat.le_sqrt]
      have : (L * S) * (L * S) = (S * S) * L ^ 2 := by ring
      rw [this]
      exact Nat.mul_le_mul_right _ (hSS.trans htφ)
    omega
  have hNp : L * S ≤ p := by omega
  have hcount := g71b_count n p r (ell r n) (L * S) m₁ m₂ h hdiv hprim hintros hNt hNl hNp hm hpw
  have hn2 : n < 2 ^ L := Nat.lt_log2_self
  have : n ^ S < (2 ^ L) ^ S := Nat.pow_lt_pow_left hn2 (by omega)
  rw [← pow_mul] at this
  omega

theorem solution : ∀ n : ℕ, aksDecide n = AksResult.prime ↔ Nat.Prime n := by
  intro n
  constructor
  · intro hd
    unfold aksDecide at hd
    by_cases hc : 1 < n ∧ ¬ isPow n
    · rw [if_pos hc] at hd
      simp only at hd
      by_cases h3 : ∃ a, a ≤ smallestR n ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n
      · rw [if_pos h3] at hd; cases hd
      · rw [if_neg h3] at hd
        by_cases h4 : n ≤ smallestR n
        · by_contra hnp
          apply h3
          refine ⟨n.minFac, le_trans (Nat.minFac_le (by omega)) h4, ?_⟩
          rw [Nat.gcd_eq_left (Nat.minFac_dvd n)]
          exact ⟨(Nat.minFac_prime (by omega)).one_lt,
            lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun h => hnp (h ▸ Nat.minFac_prime (by omega)))⟩
        · rw [if_neg h4] at hd
          by_cases h5 : ∃ a, 1 ≤ a ∧ a ≤ ell (smallestR n) n ∧ ¬ cycCong n (smallestR n) a
          · rw [if_pos h5] at hd; cases hd
          · push Not at h5
            exact g71b_hard n hc.1 hc.2 h3 (by omega) h5
    · rw [if_neg hc] at hd; cases hd
  · intro hp
    unfold aksDecide
    have hc : 1 < n ∧ ¬ isPow n := ⟨hp.one_lt, g71b_prime_not_isPow n hp⟩
    rw [if_pos hc]
    simp only
    have h3 : ¬ ∃ a, a ≤ smallestR n ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n := by
      rintro ⟨a, -, h1, h2⟩
      rcases (Nat.dvd_prime hp).1 (Nat.gcd_dvd_right a n) with h | h <;> omega
    rw [if_neg h3]
    split_ifs with h4 h5
    · rfl
    · obtain ⟨a, -, -, h⟩ := h5
      exact absurd (g71b_cycCong_prime n _ a hp) h
    · rfl
