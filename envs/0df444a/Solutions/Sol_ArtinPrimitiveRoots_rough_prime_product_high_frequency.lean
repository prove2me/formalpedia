-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_prime_product_high_frequency
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:40:52.958002+00:00
-- url     : https://prove2.me/submissions/6e12bf04-fe0d-4a55-a69a-6931f8ac4e21

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_long_prime_polynomial

section
/-! # Shared tools for prover S (A106): Bonferroni truncation, residue counts, Abel summation -/

namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! ## Bonferroni truncation -/

/-! ## Residue classes in intervals -/

/-! ## Abel summation over tails -/

lemma telescope_Ico (f : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (f (n + 1) - f n) = f b - f a := by
  rw [Finset.sum_Ico_eq_sum_range]
  have := Finset.sum_range_sub (fun i => f (a + i)) (b - a)
  rw [show ∑ k ∈ range (b - a), (f (a + k + 1) - f (a + k)) =
      ∑ k ∈ range (b - a), (f (a + (k + 1)) - f (a + k)) from by
    refine Finset.sum_congr rfl fun k _ => by rw [add_assoc]]
  rw [this, Nat.add_sub_cancel' hab, add_zero]

/-- Discrete Abel summation against tail sums. -/
lemma abel_tail (R n₀ n₁ : ℕ) (a f : ℕ → ℂ)
    (ha : ∀ m ∈ range R, a m ≠ 0 → n₀ ≤ m ∧ m ≤ n₁) :
    ∑ m ∈ range R, a m * f m = f n₀ * ∑ m ∈ range R, a m +
      ∑ n ∈ Ico n₀ n₁, (f (n + 1) - f n) * ∑ m ∈ range R, (if n < m then a m else 0) := by
  have key : ∀ m ∈ range R, a m * f m =
      a m * f n₀ + ∑ n ∈ Ico n₀ n₁, (f (n + 1) - f n) * (if n < m then a m else 0) := by
    intro m hm
    by_cases h0 : a m = 0
    · simp [h0]
    obtain ⟨h1, h2⟩ := ha m hm h0
    have e : ∑ n ∈ Ico n₀ n₁, (f (n + 1) - f n) * (if n < m then a m else 0) =
        a m * ∑ n ∈ Ico n₀ m, (f (n + 1) - f n) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_subset (s₁ := Ico n₀ m) (s₂ := Ico n₀ n₁)
        (fun n hn => by simp only [Finset.mem_Ico] at hn ⊢; omega)
        (fun n hn hn' => by
          simp only [Finset.mem_Ico] at hn hn'
          rw [if_neg (by omega), mul_zero])]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [Finset.mem_Ico] at hn
      rw [if_pos hn.2]; ring
    rw [e, telescope_Ico f n₀ m h1]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]

lemma abel_bound (R n₀ n₁ : ℕ) (a f : ℕ → ℂ)
    (ha : ∀ m ∈ range R, a m ≠ 0 → n₀ ≤ m ∧ m ≤ n₁) (ε : ℝ)
    (h0 : ‖∑ m ∈ range R, a m‖ ≤ ε)
    (ht : ∀ n : ℕ, ‖∑ m ∈ range R, (if n < m then a m else 0)‖ ≤ ε) :
    ‖∑ m ∈ range R, a m * f m‖ ≤ ε * (‖f n₀‖ + ∑ n ∈ Ico n₀ n₁, ‖f (n + 1) - f n‖) := by
  rw [abel_tail R n₀ n₁ a f ha]
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖f n₀ * ∑ m ∈ range R, a m‖ ≤ ε * ‖f n₀‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
  have e2 : ‖∑ n ∈ Ico n₀ n₁, (f (n + 1) - f n) * ∑ m ∈ range R, (if n < m then a m else 0)‖ ≤
      ε * ∑ n ∈ Ico n₀ n₁, ‖f (n + 1) - f n‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (ht n) (norm_nonneg _)
  linarith

/-! ## Exponential sums over progressions -/

/-! ## Brun's pure sieve and character sums -/

/-! ## Dilated intervals -/

/-- The set `{y : d y ∈ J}`. -/
def scaleSet (d : ℕ) (J : Set ℝ) : Set ℝ := (fun y : ℝ => (d : ℝ) * y) ⁻¹' J

lemma scaleSet_ordConnected (d : ℕ) (J : Set ℝ) (hJ : J.OrdConnected) :
    (scaleSet d J).OrdConnected := by
  refine ⟨fun y₁ h₁ y₂ h₂ y hy => ?_⟩
  simp only [scaleSet, Set.mem_preimage] at h₁ h₂ ⊢
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact hJ.out h₁ h₂ ⟨mul_le_mul_of_nonneg_left hy.1 hd, mul_le_mul_of_nonneg_left hy.2 hd⟩

lemma scaleSet_subset (d : ℕ) (hd : 0 < d) (J : Set ℝ) (M : ℝ) (hJ : J ⊆ Set.Icc M (2 * M)) :
    scaleSet d J ⊆ Set.Icc (M / d) (2 * (M / d)) := by
  intro y hy
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have := hJ hy
  simp only [Set.mem_Icc] at this ⊢
  constructor
  · rw [div_le_iff₀ hd']; linarith
  · rw [← mul_div_assoc, le_div_iff₀ hd']; linarith

end ArtinPrimitiveRoots.A106S
end

section
namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! # The high-frequency bound for `R_γ` from `long_prime_polynomial` (prover S)

Write a rough `m = p r` with `p = P⁻(m)`; for fixed `r` the prime `p` runs over an interval,
where the leaf (after partial summation) saves `L^{-A-1}`; the sum over `r ≤ 2M` costs `log 2M`. -/

open Classical in
/-- Partial summation removes the weight `p⁻¹` from a prime sum bounded on all subintervals. -/
lemma prime_cpow_bound (N ε : ℝ) (hN : 0 < N) (k : ℕ) (χ : DirichletCharacter ℂ k) (u : ℝ)
    (Jp : Set ℝ) (hJp : Jp.OrdConnected) (hJpN : Jp ⊆ Set.Icc N (2 * N))
    (hleaf : ∀ J' : Set ℝ, J'.OrdConnected → J' ⊆ Set.Icc N (2 * N) →
      ‖∑ p ∈ (range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
        (if (p : ℝ) ∈ J' then χ (p : ZMod k) * (p : ℂ) ^ (-1 + Complex.I * u) else 0)‖ ≤ ε) :
    ‖∑ p ∈ (range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
        (if (p : ℝ) ∈ Jp then χ (p : ZMod k) * (p : ℂ) ^ (Complex.I * u) else 0)‖ ≤ 2 * N * ε := by
  set R := ⌊2 * N⌋₊ + 1
  set a : ℕ → ℂ := fun m => if m.Prime ∧ (m : ℝ) ∈ Jp then
    χ (m : ZMod k) * (m : ℂ) ^ (-1 + Complex.I * u) else 0
  have e : ∑ p ∈ (range R).filter Nat.Prime,
      (if (p : ℝ) ∈ Jp then χ (p : ZMod k) * (p : ℂ) ^ (Complex.I * u) else 0) =
      ∑ m ∈ range R, a m * (m : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [a]
    by_cases hp : m.Prime
    · by_cases hm : (m : ℝ) ∈ Jp
      · rw [if_pos hp, if_pos hm, if_pos ⟨hp, hm⟩, mul_assoc]
        congr 1
        have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
        conv_lhs => rw [show Complex.I * u = (-1 + Complex.I * u) + 1 by ring]
        rw [Complex.cpow_add _ _ hm0, Complex.cpow_one]
      · rw [if_pos hp, if_neg hm, if_neg (fun h => hm h.2), zero_mul]
    · rw [if_neg hp, if_neg (fun h => hp h.1), zero_mul]
  rw [e]
  have hsum : ∀ J' : Set ℝ, J' ⊆ Jp → J'.OrdConnected →
      ∑ m ∈ range R, (if (m : ℝ) ∈ J' then a m else 0) =
        ∑ p ∈ (range R).filter Nat.Prime,
          (if (p : ℝ) ∈ J' then χ (p : ZMod k) * (p : ℂ) ^ (-1 + Complex.I * u) else 0) := by
    intro J' hsub _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [a]
    by_cases hp : m.Prime
    · by_cases hm : (m : ℝ) ∈ J'
      · rw [if_pos hm, if_pos ⟨hp, hsub hm⟩, if_pos hp, if_pos hm]
      · rw [if_neg hm, if_pos hp, if_neg hm]
    · rw [if_neg hp]; split_ifs <;> simp_all
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hleaf Jp hJp hJpN)
  have ha : ∀ m ∈ range R, a m ≠ 0 → ⌊N⌋₊ ≤ m ∧ m ≤ ⌊2 * N⌋₊ := by
    intro m _ hm
    simp only [a] at hm
    split_ifs at hm with h
    · have := hJpN h.2
      exact ⟨Nat.floor_le_of_le this.1, Nat.le_floor this.2⟩
    · exact absurd rfl hm
  have h0 : ‖∑ m ∈ range R, a m‖ ≤ ε := by
    have := hsum Jp subset_rfl hJp
    rw [show ∑ m ∈ range R, a m = ∑ m ∈ range R, (if (m : ℝ) ∈ Jp then a m else 0) from
      Finset.sum_congr rfl fun m _ => by
        by_cases hm : (m : ℝ) ∈ Jp
        · rw [if_pos hm]
        · rw [if_neg hm]; simp only [a]; rw [if_neg (fun h => hm h.2)]]
    convert hleaf Jp hJp hJpN using 2
  have ht : ∀ n : ℕ, ‖∑ m ∈ range R, (if n < m then a m else 0)‖ ≤ ε := by
    intro n
    set J' := Jp ∩ Set.Ioi (n : ℝ)
    have hJ' : J'.OrdConnected := hJp.inter Set.ordConnected_Ioi
    have hJ'N : J' ⊆ Set.Icc N (2 * N) := fun y hy => hJpN hy.1
    have := hsum J' Set.inter_subset_left hJ'
    rw [show ∑ m ∈ range R, (if n < m then a m else 0) =
        ∑ m ∈ range R, (if (m : ℝ) ∈ J' then a m else 0) from
      Finset.sum_congr rfl fun m _ => by
        by_cases hnm : n < m
        · rw [if_pos hnm]
          by_cases hm : (m : ℝ) ∈ Jp
          · rw [if_pos ⟨hm, by simp only [Set.mem_Ioi]; exact_mod_cast hnm⟩]
          · rw [if_neg (fun h => hm h.1)]; simp only [a]; rw [if_neg (fun h => hm h.2)]
        · rw [if_neg hnm, if_neg]
          intro h; exact hnm (by have := h.2; simp only [Set.mem_Ioi] at this; exact_mod_cast this)]
    convert hleaf J' hJ' hJ'N using 2
    convert this using 3
  have hab := abel_bound R ⌊N⌋₊ ⌊2 * N⌋₊ a (fun m => (m : ℂ)) ha ε h0 ht
  have hle : ⌊N⌋₊ ≤ ⌊2 * N⌋₊ := Nat.floor_mono (by linarith)
  have hw : ‖((⌊N⌋₊ : ℕ) : ℂ)‖ + ∑ n ∈ Ico ⌊N⌋₊ ⌊2 * N⌋₊, ‖((n + 1 : ℕ) : ℂ) - (n : ℂ)‖ =
      (⌊2 * N⌋₊ : ℝ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun n _ => by push_cast; simp),
      Finset.sum_const, Nat.card_Ico, Complex.norm_natCast, nsmul_eq_mul, mul_one,
      Nat.cast_sub hle]
    ring
  rw [hw] at hab
  refine hab.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) hε

lemma minFac_mul_of_le (p r : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hle : ∀ q ∈ r.primeFactors, p ≤ q) : (p * r).minFac = p := by
  have h1 : (p * r).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p r)
  have hpr : p * r ≠ 1 := by
    intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h)
  have hq := Nat.minFac_prime hpr
  rcases (Nat.Prime.dvd_mul hq).1 (Nat.minFac_dvd (p * r)) with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hq hp).1 h
  · exact le_antisymm h1 (hle _ (Nat.mem_primeFactors.2 ⟨hq, h, hr.ne'⟩))

open Classical in
/-- Decomposition of a rough integer by its least prime factor: `m = p r`, `p = P⁻(m)`. -/
lemma minFac_decomp (B : ℕ) (y : ℝ) (J : Set ℝ) (hJ2 : ∀ m : ℕ, (m : ℝ) ∈ J → 2 ≤ m)
    (hJB : ∀ m : ℕ, (m : ℝ) ∈ J → m < B) (F : ℕ → ℂ) :
    ∑ m ∈ range B, (if (m : ℝ) ∈ J ∧ IsRough y m then F m else 0) =
      ∑ r ∈ range B, ∑ p ∈ range B, (if 0 < r ∧ p.Prime ∧ y < p ∧
        (∀ q ∈ r.primeFactors, p ≤ q) ∧ ((p * r : ℕ) : ℝ) ∈ J then F (p * r) else 0) := by
  rw [show (∑ r ∈ range B, ∑ p ∈ range B, (if 0 < r ∧ p.Prime ∧ y < p ∧
        (∀ q ∈ r.primeFactors, p ≤ q) ∧ ((p * r : ℕ) : ℝ) ∈ J then F (p * r) else 0)) =
      ∑ rp ∈ (range B ×ˢ range B).filter (fun rp : ℕ × ℕ => 0 < rp.1 ∧ rp.2.Prime ∧
        y < rp.2 ∧ (∀ q ∈ rp.1.primeFactors, rp.2 ≤ q) ∧ ((rp.2 * rp.1 : ℕ) : ℝ) ∈ J),
        F (rp.2 * rp.1) from by rw [Finset.sum_filter, Finset.sum_product]]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun m => (m / m.minFac, m.minFac)) (fun rp => rp.2 * rp.1)
    ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hm ⊢
    obtain ⟨hmB, hmJ, hm0, hR⟩ := hm
    have h2 := hJ2 m hmJ
    have hm1 : m ≠ 1 := by omega
    have hpm := Nat.minFac_prime hm1
    have hdvd := Nat.minFac_dvd m
    have hle : m.minFac ≤ m := Nat.minFac_le hm0
    refine ⟨⟨lt_of_le_of_lt (Nat.div_le_self _ _) hmB, lt_of_le_of_lt hle hmB⟩,
      Nat.div_pos hle hpm.pos, hpm, hR _ (Nat.mem_primeFactors.2 ⟨hpm, hdvd, hm0.ne'⟩),
      fun q hq => ?_, ?_⟩
    · have hq' := Nat.mem_primeFactors.1 hq
      exact Nat.minFac_le_of_dvd hq'.1.two_le (hq'.2.1.trans (Nat.div_dvd_of_dvd hdvd))
    · rw [Nat.mul_div_cancel' hdvd]; exact hmJ
  · intro rp hrp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hrp ⊢
    obtain ⟨_, hr0, hp, hyp, hle, hJ⟩ := hrp
    refine ⟨hJB _ hJ, hJ, Nat.mul_pos hp.pos hr0, fun q hq => ?_⟩
    have hq' := Nat.mem_primeFactors.1 hq
    rcases (Nat.Prime.dvd_mul hq'.1).1 hq'.2.1 with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq'.1 hp).1 h]; exact hyp
    · have := hle q (Nat.mem_primeFactors.2 ⟨hq'.1, h, hr0.ne'⟩)
      exact lt_of_lt_of_le hyp (by exact_mod_cast this)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    exact Nat.mul_div_cancel' (Nat.minFac_dvd m)
  · intro rp hrp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hrp
    obtain ⟨_, hr0, hp, _, hle, _⟩ := hrp
    rw [minFac_mul_of_le rp.2 rp.1 hp hr0 hle, Nat.mul_div_cancel_left _ hp.pos]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    rw [Nat.mul_div_cancel' (Nat.minFac_dvd m)]

lemma sum_range_inv_le (n : ℕ) : ∑ r ∈ range (n + 1), ((r : ℝ))⁻¹ ≤ 1 + log n := by
  rw [Finset.sum_range_succ', Nat.cast_zero, inv_zero, add_zero]
  have h := harmonic_le_one_add_log n
  have e : (harmonic n : ℝ) = ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ := by
    rw [harmonic]; push_cast; rfl
  rw [e] at h
  simpa using h

/-- The range of the least prime `p` of `m = p r` with `m ∈ J`, for fixed `r`. -/
def slotSet (y : ℝ) (r : ℕ) (J : Set ℝ) : Set ℝ :=
  {z | y < z} ∩ {z | ∀ q ∈ r.primeFactors, z ≤ (q : ℝ)} ∩ scaleSet r J

open Classical in
/-- The high-frequency bound with explicit constants, from a prime-sum bound `ε` valid on
every interval at every scale `N ∈ [y/2, M]`. -/
lemma hf_core (y M ε : ℝ) (hM1 : 1 < M) (hε : 0 ≤ ε) (k : ℕ)
    (χ : DirichletCharacter ℂ k) (J : Set ℝ) (hJ : J.OrdConnected)
    (hJM : J ⊆ Set.Icc M (2 * M)) (u : ℝ)
    (hleaf : ∀ N : ℝ, y / 2 ≤ N → N ≤ M → ∀ J' : Set ℝ, J'.OrdConnected →
      J' ⊆ Set.Icc N (2 * N) →
      ‖∑ p ∈ (range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
        (if (p : ℝ) ∈ J' then χ (p : ZMod k) * (p : ℂ) ^ (-1 + Complex.I * u) else 0)‖ ≤ ε) :
    ‖∑ m ∈ range (⌊2 * M⌋₊ + 1), (if (m : ℝ) ∈ J ∧ IsRough y m then
        χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤ 2 * M * ε * (1 + log (2 * M)) := by
  set B := ⌊2 * M⌋₊ + 1
  have hM0 : 0 < M := by linarith
  have hJ2 : ∀ m : ℕ, (m : ℝ) ∈ J → 2 ≤ m := by
    intro m hm
    have : (1 : ℝ) < m := lt_of_lt_of_le hM1 (hJM hm).1
    exact_mod_cast (show (1 : ℕ) < m by exact_mod_cast this)
  have hJB : ∀ m : ℕ, (m : ℝ) ∈ J → m < B := fun m hm =>
    Nat.lt_succ_of_le (Nat.le_floor (hJM hm).2)
  rw [minFac_decomp B y J hJ2 hJB]
  -- the inner sums
  have hinner : ∀ r ∈ range B, ‖∑ p ∈ range B, (if 0 < r ∧ p.Prime ∧ y < p ∧
      (∀ q ∈ r.primeFactors, p ≤ q) ∧ ((p * r : ℕ) : ℝ) ∈ J then
        χ ((p * r : ℕ) : ZMod k) * ((p * r : ℕ) : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      2 * M * ε * ((r : ℝ))⁻¹ := by
    intro r _
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    set Jr : Set ℝ := slotSet y r J
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hJr : Jr.OrdConnected := by
      refine (Set.ordConnected_Ioi.inter ?_).inter (scaleSet_ordConnected r J hJ)
      refine ⟨fun a ha b hb z hz q hq => ?_⟩
      exact le_trans hz.2 (hb q hq)
    set N := M / r
    have hJrN : Jr ⊆ Set.Icc N (2 * N) := fun z hz => scaleSet_subset r hr J M hJM hz.2
    have e1 : ∑ p ∈ range B, (if 0 < r ∧ p.Prime ∧ y < p ∧
        (∀ q ∈ r.primeFactors, p ≤ q) ∧ ((p * r : ℕ) : ℝ) ∈ J then
          χ ((p * r : ℕ) : ZMod k) * ((p * r : ℕ) : ℂ) ^ (Complex.I * u) else 0) =
        (χ (r : ZMod k) * (r : ℂ) ^ (Complex.I * u)) *
          ∑ p ∈ (range B).filter Nat.Prime, (if (p : ℝ) ∈ Jr then
            χ (p : ZMod k) * (p : ℂ) ^ (Complex.I * u) else 0) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hiff : (0 < r ∧ p.Prime ∧ y < p ∧ (∀ q ∈ r.primeFactors, p ≤ q) ∧
          ((p * r : ℕ) : ℝ) ∈ J) ↔ (p.Prime ∧ (p : ℝ) ∈ Jr) := by
        simp only [Jr, slotSet, scaleSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
        push_cast
        constructor
        · rintro ⟨_, hp, hyp, hle, hJ⟩
          exact ⟨hp, ⟨hyp, fun q hq => by exact_mod_cast hle q hq⟩, by rwa [mul_comm]⟩
        · rintro ⟨hp, ⟨hyp, hle⟩, hJ⟩
          exact ⟨hr, hp, hyp, fun q hq => by exact_mod_cast hle q hq, by rwa [mul_comm]⟩
      by_cases h : p.Prime ∧ (p : ℝ) ∈ Jr
      · rw [if_pos (hiff.2 h), if_pos h.1, if_pos h.2, Nat.cast_mul, map_mul,
          Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        ring
      · rw [if_neg (fun h' => h (hiff.1 h'))]
        by_cases hp : p.Prime
        · rw [if_pos hp, if_neg (fun h' => h ⟨hp, h'⟩), mul_zero]
        · rw [if_neg hp, mul_zero]
    rw [e1, norm_mul]
    have hχr : ‖χ (r : ZMod k) * (r : ℂ) ^ (Complex.I * u)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hr]
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_self, rpow_zero, mul_one]
      exact DirichletCharacter.norm_le_one χ _
    have hbd : ‖∑ p ∈ (range B).filter Nat.Prime, (if (p : ℝ) ∈ Jr then
        χ (p : ZMod k) * (p : ℂ) ^ (Complex.I * u) else 0)‖ ≤ 2 * N * ε := by
      rcases Jr.eq_empty_or_nonempty with hE | ⟨z, hz⟩
      · rw [Finset.sum_eq_zero fun p _ => if_neg (by rw [hE]; exact Set.notMem_empty _),
          norm_zero]
        have : 0 ≤ N := by positivity
        positivity
      have hN1 : y / 2 ≤ N := by
        have h1 : y < z := hz.1.1
        have h2 := (hJrN hz).2
        linarith
      have hNM : N ≤ M := div_le_self hM0.le (by exact_mod_cast hr)
      have hsub : (range (⌊2 * N⌋₊ + 1)).filter Nat.Prime ⊆ (range B).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        refine ⟨?_, hp.2⟩
        have : ⌊2 * N⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_mono (by linarith)
        omega
      rw [← Finset.sum_subset hsub (fun p hp hp' => by
        simp only [Finset.mem_filter, Finset.mem_range] at hp hp'
        rw [if_neg]
        intro hJ'
        exact hp' ⟨Nat.lt_succ_of_le (Nat.le_floor (hJrN hJ').2), hp.2⟩)]
      exact prime_cpow_bound N ε (by positivity) k χ u Jr hJr hJrN (hleaf N hN1 hNM)
    calc ‖χ (r : ZMod k) * (r : ℂ) ^ (Complex.I * u)‖ * _ ≤ 1 * (2 * N * ε) :=
          mul_le_mul hχr hbd (norm_nonneg _) zero_le_one
      _ = 2 * M * ε * ((r : ℝ))⁻¹ := by simp only [N]; field_simp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hinner).trans ?_)
  rw [← Finset.mul_sum]
  have hh := sum_range_inv_le ⌊2 * M⌋₊
  have hlog : log (⌊2 * M⌋₊ : ℝ) ≤ log (2 * M) := by
    have : (1 : ℝ) ≤ ⌊2 * M⌋₊ := by exact_mod_cast Nat.floor_pos.2 (by linarith)
    exact log_le_log (by linarith) (Nat.floor_le (by linarith))
  have : 0 ≤ 2 * M * ε := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) this

end ArtinPrimitiveRoots.A106S

namespace ArtinPrimitiveRoots

open Real A106S

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real A106S
open Classical in
theorem solution (γ wMinus wPlus : ℝ) (hγ : 0 < γ)
    (hγw : γ < wMinus) (hww : wMinus < wPlus) (hwPlus : wPlus < 1) :
    ∀ A₀ A : ℝ, 0 < A₀ → 0 < A →
      ∃ B₀ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
      ∀ u : ℝ, log x ^ B₀ ≤ |u| → |u| ≤ x ^ 2 →
        ‖((1 / M : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
            (if (m : ℝ) ∈ J ∧ IsRough (x ^ γ) m then
              χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) else 0)‖ ≤ K * log x ^ (-A) := by
  intro A₀ A hA₀ hA
  obtain ⟨B₀, K₁, x₁, hleaf⟩ := long_prime_polynomial (γ / 2) ((wPlus + 1) / 2) A₀ (A + 1)
    (by positivity) (by linarith) (by linarith) hA₀ (by linarith)
  refine ⟨B₀, 4 * max K₁ 0, max x₁ (exp 1),
    fun x hx M hM hMlo hMhi k hk hkL χ J hJ hJM u hu1 hu2 => ?_⟩
  have hx1 : x₁ ≤ x := le_of_max_le_left hx
  have hxe : exp 1 ≤ x := le_of_max_le_right hx
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hxe
  have hxone : 1 ≤ x := le_trans (by linarith [add_one_le_exp (1 : ℝ)]) hxe
  set L := log x with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef, ← log_exp 1]; exact log_le_log (exp_pos 1) hxe
  have hL0 : 0 < L := by linarith
  have hlogM : wMinus * L ≤ log M := by rwa [le_div_iff₀ hL0] at hMlo
  have hlog2M : log (2 * M) ≤ wPlus * L := by rwa [div_le_iff₀ hL0] at hMhi
  have hM1 : 1 < M := by
    have : 0 < log M := lt_of_lt_of_le (mul_pos (by linarith) hL0) hlogM
    exact (log_pos_iff hM.le).1 this
  set ε := max K₁ 0 * L ^ (-(A + 1))
  have hε : 0 ≤ ε := by positivity
  have h2M : 2 * M ≤ x ^ wPlus := by
    rw [← exp_log (by positivity : (0 : ℝ) < 2 * M), rpow_def_of_pos hx0]
    apply exp_le_exp.2
    have e : log x * wPlus = wPlus * L := by rw [hLdef]; ring
    rw [e]; exact hlog2M
  have hleaf' : ∀ N : ℝ, x ^ γ / 2 ≤ N → N ≤ M → ∀ J' : Set ℝ, J'.OrdConnected →
      J' ⊆ Set.Icc N (2 * N) →
      ‖∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
        (if (p : ℝ) ∈ J' then χ (p : ZMod k) * (p : ℂ) ^ (-1 + Complex.I * u) else 0)‖ ≤ ε := by
    intro N hN1 hN2 J' hJ' hJ'N
    have hτ : x ^ (γ / 2) / 2 ≤ N := by
      refine le_trans ?_ hN1
      have : x ^ (γ / 2) ≤ x ^ γ := rpow_le_rpow_of_exponent_le hxone (by linarith)
      linarith
    have hη : N ≤ x ^ ((wPlus + 1) / 2) := by
      have : x ^ wPlus ≤ x ^ ((wPlus + 1) / 2) := rpow_le_rpow_of_exponent_le hxone (by linarith)
      linarith
    have := hleaf x hx1 N hτ hη k hk hkL χ u hu1 hu2 J' hJ' hJ'N
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have core := hf_core (x ^ γ) M ε hM1 hε k χ J hJ hJM u hleaf'
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hLA : L ^ (-(A + 1)) * L = L ^ (-A) := by
    conv_lhs => rw [show L ^ (-(A + 1)) * L = L ^ (-(A + 1)) * L ^ (1 : ℝ) by rw [rpow_one]]
    rw [← rpow_add hL0]; ring_nf
  calc 1 / M * ‖_‖ ≤ 1 / M * (2 * M * ε * (1 + log (2 * M))) :=
        mul_le_mul_of_nonneg_left core (by positivity)
    _ = 2 * ε * (1 + log (2 * M)) := by field_simp
    _ ≤ 2 * ε * (2 * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = 4 * max K₁ 0 * (L ^ (-(A + 1)) * L) := by simp only [ε]; ring
    _ = 4 * max K₁ 0 * L ^ (-A) := by rw [hLA]
end
