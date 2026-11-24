-- Prove2me | Definitions.Def_FriezePatterns_chapter3
-- name    : FriezePatterns_chapter3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:13:55.085897+00:00
-- url     : https://prove2.me/theorems/a47de0ce-86e5-4724-add5-92a3f6a9e272
-- title:
--   chapter3
-- statement:
--   Definitions and structural lemmas for chapter3, from Antoine-dSG (Antoine-dSG/frieze_patterns; see pinned Apache-2.0 LICENSE)'s pinned Fibonacci upper bound and attainment for arithmetic frieze patterns development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Antoine-dSG/frieze_patterns/blob/4e921473387f925942f0b95f3853c59b33670282/FriezePatterns/chapter3.lean

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2
import Theorems.Thm_glideSymm
import Theorems.Thm_pattern_nContinuant1
import Theorems.Thm_translationInvariance

set_option autoImplicit true
class arith_fp (f : ℕ × ℕ → ℚ) (n : ℕ) : Prop where
  topBordZeros : ∀ m, f (0,m) = 0
  topBordOnes : ∀ m, f (1,m) = 1
  botBordOnes_n : ∀ m, f (n, m) = 1
  botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (f (i,m) = 0)
  diamond : ∀ i, ∀ m,  i ≤ n-1 → f (i+1,m) * f (i+1,m+1)-1 = f (i+2,m)*f (i,m+1)
  integral: ∀ i, ∀ m, (f (i,m)).den = 1
  positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → f (i,m) > 0
instance [arith_fp f n] : nzPattern_n ℚ f n := {
  topBordZeros := arith_fp.topBordZeros n,
  topBordOnes := arith_fp.topBordOnes n,
  botBordOnes_n := arith_fp.botBordOnes_n,
  botBordZeros_n := arith_fp.botBordZeros_n,
  diamond := arith_fp.diamond,
  non_zero := λ i m ⟨hi1, hi2⟩ => by linarith [@arith_fp.positive f n _ i m hi1 hi2]
}
def flute_f (f : ℕ×ℕ → ℚ) (n m: ℕ) [arith_fp f n] (i:ℕ) : ℕ :=        -- definition only good when n ≥ 2, as otherwise i%0 = i for all i
  ((f (i%(n-1) + 1, m)).num).toNat
def friezeToFlute (f : ℕ×ℕ → ℚ) (n m: ℕ) (hn : 2 ≤ n) [arith_fp f n] : flute n := by
  have pos : ∀ i, flute_f f n m i > 0 := by
    intro i

    have zero_lt_n_sub_one : 0 < n - 1 :=
        calc 0 < 1 := by simp
            _≤ 2 - 1 := by simp
            _≤  n - 1 := Nat.sub_le_sub_right hn 1

    unfold flute_f
    simp
    have a₁ : 1 ≤ i%(n-1) + 1 := by omega
    have a₂ : i%(n-1) + 1 ≤ n :=
        calc i%(n-1) + 1 ≤ (n - 1) + 1 := Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt i zero_lt_n_sub_one)) 1
            _≤ n := by omega

    exact arith_fp.positive (i%(n-1) + 1) m a₁ a₂   --finish if 1 < (n-1) and i%(n-1) ≠ 0

  have hd : flute_f f n m 0 = 1 := by
    unfold flute_f
    simp [arith_fp.topBordOnes n m]

  have period : ∀ i, flute_f f n m i = flute_f f n m (i + (n-1)) := by
    intro i
    unfold flute_f
    simp                  --finish if i%(n-1) ≠ 0

  have div : ∀ i, flute_f f n m (i + 1) ∣ (flute_f f n m (i) + flute_f f n m (i + 2)) := by
    intro i
    unfold flute_f

    by_cases n_eq_two : n=2
    simp [n_eq_two]
    simp [Nat.mod_one]                             --finish if n=2

    by_cases n_eq_three : n=3

    by_cases i_even : i%2 = 0
    have i_plus_one_odd : (i+1)%2 = 1 := by omega
    have i_plus_two_even : (i+2)%2 = 0 := by rw[Nat.add_mod_right i 2, i_even]

    simp [n_eq_three]
    simp [i_even, i_plus_one_odd, i_plus_two_even]
    rw[@pattern_n.topBordOnes ℚ _ f n _ m]
    simp
    have this : f (2, m) * f (2, m + 1) = 2 :=
        calc f (2, m) * f (2, m + 1) = f (2, m) * f (2, m + 1) - 1 + 1 := by simp
              _= f (3, m)*f (1, m + 1) + 1 := by rw[@pattern_n.diamond ℚ _ f n _ 1 (m) (by omega)]
              _= f (3, m) * 1 + 1 := by rw[@pattern_n.topBordOnes ℚ _ f n _ (m+1)]
              _= f (n, m) * 1 + 1 := by rw[n_eq_three]
              _= 1 * 1 + 1 := by rw[@pattern_n.botBordOnes_n ℚ _ f n _ (m)]
              _= 2 := by ring

    have this.num : (f (2, m)).num * (f (2, m + 1)).num = 2 := by
      have key : (f (2, m)).num * (f (2, m + 1)).num = (f (2, m) * f (2, m + 1)).num := by
        simp [Rat.mul_num, arith_fp.integral n, arith_fp.integral n]
      simp [key, this]

    have this.num.toNat : (f (2, m)).num.toNat * (f (2, m + 1)).num.toNat = 2 := by
      have h₃ : 0 ≤ (f (2,m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 m (by omega) (by omega))]
      have h₄ : 0 ≤ (f (2,m+1)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 (m+1) (by omega) (by omega))]
      zify ; rw [Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄, this.num]

    nth_rewrite 2 [← this.num.toNat]
    simp                                              --finish if n=3, i_even

    have i_plus_one_even : (i+1)%2 = 0 := by omega
    simp [n_eq_three, i_plus_one_even]
    rw[@pattern_n.topBordOnes ℚ _ f n _ m]
    simp                                          --finish if n=3, i_odd

    --now do 4 ≤ n
    have four_le_n : 4 ≤ n := by omega
    have one_lt_n_sub_one : 1 < n - 1 := by omega
    have two_lt_n_sub_one : 2 < n - 1 := by omega

    by_cases boundary : (i + 1) % (n - 1) = 0
    simp[boundary, arith_fp.topBordOnes n m]            --finish boundary case if (i + 1) % (n - 1) = 0


    by_cases boundary' : (i + 2) % (n - 1) = 0
    have i_mod_n_sub_one_eq_n_sub_three : (i) % (n - 1) = n - 3 :=  --this now makes sense as n ≥ 4
        calc (i) % (n - 1) = (i + (n - 1)) % (n - 1) :=  by simp
            _= (i + (n - 1) + 2 - 2) % (n - 1) := by simp
            _= (i + 2 + (n - 1) - 2) % (n - 1) := by rw[add_right_comm]
            _= (i + 2 + ((n - 1) - 2)) % (n - 1) := by rw[Nat.add_sub_assoc (Nat.le_of_lt two_lt_n_sub_one) (i+2)]
            _= ((i + 2) % (n - 1) + ((n - 1) - 2) % (n - 1)) % (n - 1) := by rw[Nat.add_mod]
            _= (((n - 1) - 2) % (n - 1)) % (n - 1) := by simp [boundary']
            _= ((n - 1) - 2) % (n - 1) := by rw[Nat.mod_mod]
            _= (n - 3) % (n - 1) := by rw[Nat.sub_sub n 1 2]
            _= n - 3 := by rw[Nat.mod_eq_of_lt (by omega)]

    have i_plus_one_mod_n_sub_one_eq_n_sub_two : (i + 1) % (n - 1) = n - 2 := by
        rw[Nat.add_mod]
        rw[i_mod_n_sub_one_eq_n_sub_three, Nat.mod_eq_of_lt (one_lt_n_sub_one)]
        rw[Nat.mod_eq_of_lt (by omega)]
        omega

    simp [boundary',i_mod_n_sub_one_eq_n_sub_three,i_plus_one_mod_n_sub_one_eq_n_sub_two]
    have BordOnes : f (1,m) = f (n,m) := by
        rw[@pattern_n.topBordOnes ℚ _ f n _ m]
        rw[@pattern_n.botBordOnes_n ℚ _ f n _ m]

    rw[BordOnes]
    have a₁ : n - 3 + 1 = n - 2 := by omega
    have a₂ : n = n - 2 + 2 := by omega
    rw[a₁]
    nth_rewrite 3 [a₂]

    have continuant3 : (f ((n-2), m)) + (f ((n-2) + 1 + 1, m)) = (f (2, m + (n-2))) * (f ((n-2)+ 1,m)) := by
      rw[pattern_nContinuant1 ℚ f n (n-2) (by omega) m]
      simp

    have continuant3.num : (f ((n - 2), m)).num + (f ((n - 2) + 1 + 1, m)).num = (f (2, m + ((n - 2)))).num * (f ((n - 2) + 1,m)).num := by
      have key₁ : (f ((n - 2), m)).num + (f ((n - 2) + 1 + 1, m)).num = (f ((n - 2), m) + f ((n - 2) + 1 + 1, m)).num := by
        have h1 : f ((n - 2), m) = ((f ((n - 2), m)).num : ℚ) := by rw [← Rat.num_div_den (f ((n - 2), m)), arith_fp.integral n (n - 2) m]; simp
        have h2 : f ((n - 2) + 1 + 1, m) = ((f ((n - 2) + 1 + 1, m)).num : ℚ) := by rw [← Rat.num_div_den (f ((n - 2) + 1 + 1, m)), arith_fp.integral n ((n - 2) + 1 + 1) m]; simp
        conv_rhs => rw [h1, h2]
        rw [← Int.cast_add, Rat.num_intCast]
      have key₂ : (f (2, m + ((n - 2)))).num * (f ((n - 2) + 1,m)).num = (f (2, m + ((n - 2))) * f ((n - 2) + 1,m)).num := by
        simp [Rat.mul_num, arith_fp.integral n 2 (m + ((n - 2))), arith_fp.integral n ((n - 2) + 1) m]
      simp [key₁, key₂, continuant3]

    have continuant3.num.toNat : (f ((n - 2), m)).num.toNat + (f ((n - 2) + 1 + 1, m)).num.toNat = (f (2, m + ((n - 2)))).num.toNat * (f ((n - 2) + 1,m)).num.toNat := by
      have h₂ : 0 ≤ (f ((n - 2), m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ ((n - 2)) m (by omega) (by omega))]
      have h₃ : 0 ≤ (f ((n - 2) + 1 + 1, m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ ((n - 2) + 1 + 1) m (by omega) (by omega))]
      have h₄ : 0 ≤ (f (2, m + ((n - 2)))).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 (m + ((n - 2))) (by omega) (by omega))]
      have h₅ : 0 ≤ (f ((n - 2) + 1,m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ ((n - 2) + 1) m (by omega) (by omega))]
      zify ; rw [Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄, Int.toNat_of_nonneg h₅, continuant3.num]

    simp[continuant3.num.toNat]                                           --finish boundary' case if (i + 2) % (n - 1) = 0

    have i_plus_one_mod_n_sub_one_bd_below : 1 ≤ (i + 1) % (n - 1) := by
        rw[Nat.one_le_iff_ne_zero]
        simp[boundary]



    have i_mod_n_sub_one_bd_above : (i) % (n - 1) < (n - 1) := Nat.mod_lt (i) (by omega)
    have i_plus_one_mod_n_sub_one_bd_above : (i + 1) % (n - 1) < (n - 1) := Nat.mod_lt (i+1) (by omega)
    have i_plus_two_mod_n_sub_one_bd_above : (i + 2) % (n - 1) < (n - 1) := Nat.mod_lt (i+2) (by omega)     --These three feed some linarith's below, don't delete

    have a₀₁ : (i) % (n - 1) + (1) % (n - 1) < n - 1 := by
        rw[Nat.mod_eq_of_lt (one_lt_n_sub_one)]
        by_contra hlt
        apply boundary
        have this : i % (n - 1) + 1 = n - 1 := by omega
        rw[Nat.add_mod, Nat.mod_eq_of_lt (one_lt_n_sub_one), this]
        simp

    have a₁ : (i + 1) % (n - 1) = (i) % (n - 1) + 1 := by
        rw[Nat.add_mod_of_add_mod_lt a₀₁]
        simp
        rw[Nat.mod_eq_of_lt (by linarith)]

    have a₀₂ : (i) % (n - 1) + (2) % (n - 1) < n - 1 := by
        rw[Nat.mod_eq_of_lt (two_lt_n_sub_one)]
        by_contra hlt
        apply boundary'
        have h1lt : i % (n - 1) + 1 < n - 1 := by rwa [Nat.mod_eq_of_lt one_lt_n_sub_one] at a₀₁
        have this : n - 1 = i % (n - 1) + 2 := by omega
        rw[Nat.add_mod, Nat.mod_eq_of_lt (two_lt_n_sub_one), ← this]
        simp


    have a₂ : (i + 2) % (n - 1) = (i) % (n - 1) + 2 := by
        rw[Nat.add_mod_of_add_mod_lt (a₀₂)]
        simp
        rw[Nat.mod_eq_of_lt (by omega)]

    rw[a₁,a₂, add_right_comm]
    have h₁ : i % (n - 1) + 1 ≤ n - 1 :=
        calc  i % (n - 1) + 1 ≤ (i) % (n - 1) + (1) % (n - 1) := by rw[Nat.mod_eq_of_lt (one_lt_n_sub_one)]
              _≤ n - 1 := Nat.le_of_lt (a₀₁)

    have continuant : (f (i % (n - 1) + 1, m)) + (f (i % (n - 1) + 1 + 1 + 1, m)) = (f (2, m + (i % (n - 1) + 1))) * (f (i % (n - 1) + 1 + 1,m)) := by
      rw[pattern_nContinuant1 ℚ f n (i % (n - 1) + 1) h₁ m]
      simp

    have continuant.num : (f (i % (n - 1) + 1, m)).num + (f (i % (n - 1) + 1 + 1 + 1, m)).num = (f (2, m + (i % (n - 1) + 1))).num * (f (i % (n - 1) + 1 + 1,m)).num := by
      have key₁ : (f (i % (n - 1) + 1, m)).num + (f (i % (n - 1) + 1 + 1 + 1, m)).num = (f (i % (n - 1) + 1, m) + f (i % (n - 1) + 1 + 1 + 1, m)).num := by
        have h1 : f (i % (n - 1) + 1, m) = ((f (i % (n - 1) + 1, m)).num : ℚ) := by rw [← Rat.num_div_den (f (i % (n - 1) + 1, m)), arith_fp.integral n (i % (n - 1) + 1) m]; simp
        have h2 : f (i % (n - 1) + 1 + 1 + 1, m) = ((f (i % (n - 1) + 1 + 1 + 1, m)).num : ℚ) := by rw [← Rat.num_div_den (f (i % (n - 1) + 1 + 1 + 1, m)), arith_fp.integral n (i % (n - 1) + 1 + 1 + 1) m]; simp
        conv_rhs => rw [h1, h2]
        rw [← Int.cast_add, Rat.num_intCast]
      have key₂ : (f (2, m + (i % (n - 1) + 1))).num * (f (i % (n - 1) + 1 + 1,m)).num = (f (2, m + (i % (n - 1) + 1)) * f (i % (n - 1) + 1 + 1,m)).num := by
        simp [Rat.mul_num, arith_fp.integral n 2 (m + (i % (n - 1) + 1)), arith_fp.integral n (i % (n - 1) + 1 + 1) m]
      simp [key₁, key₂, continuant]

    have continuant.num.toNat : (f (i % (n - 1) + 1, m)).num.toNat + (f (i % (n - 1) + 1 + 1 + 1, m)).num.toNat = (f (2, m + (i % (n - 1) + 1))).num.toNat * (f (i % (n - 1) + 1 + 1,m)).num.toNat := by
      have h₂ : 0 ≤ (f (i % (n - 1) + 1, m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ (i % (n - 1) + 1) m (by omega) (by omega))]
      have h₃ : 0 ≤ (f (i % (n - 1) + 1 + 1 + 1, m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ (i % (n - 1) + 1 + 1 + 1) m (by omega) (by omega))]
      have h₄ : 0 ≤ (f (2, m + (i % (n - 1) + 1))).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ 2 (m + (i % (n - 1) + 1)) (by omega) (by omega))]
      have h₅ : 0 ≤ (f (i % (n - 1) + 1 + 1,m)).num := by linarith [Rat.num_pos.mpr (@arith_fp.positive f n _ (i % (n - 1) + 1 + 1) m (by omega) (by omega))]
      zify ; rw [Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg h₃, Int.toNat_of_nonneg h₄, Int.toNat_of_nonneg h₅, continuant.num]

    simp[continuant.num.toNat]

  exact ⟨flute_f f n m, pos, hd, period, div⟩
def frieze_f {n : ℕ} (g : flute n): ℕ × ℕ → ℚ :=
  λ ⟨i, m⟩ =>
    if i = 0 then 0
    else if i ≥ n+1 then 0
    else if m = 0 then g.a (i-1)
    else (frieze_f g (i+1,m-1) * frieze_f g (i-1, m) + 1) / frieze_f g (i,m-1)
    termination_by x => (x.2, x.1)
def fluteToFrieze {n : ℕ} (g : flute n) (hn : n ≠ 0) : arith_fp (frieze_f g) n := by
  have topBordZeros : ∀ m, frieze_f g (0,m) = 0 := λ m => (by simp [frieze_f])
  have botBordZeros_n : ∀ i, ∀ m,  i ≥ n+1 → (frieze_f g (i,m) = 0) := λ i m h => by simp [frieze_f, h]
  have topBordOnes : ∀ m, frieze_f g (1,m) = 1 := by
    intro m
    induction' m with m ih
    simp [frieze_f, hn, g.hd]
    have : ¬ 1 ≥ n+1 := by omega
    unfold frieze_f ; simp [this, ih]
    right
    exact topBordZeros (m+1)
  have botBordOnes_n : ∀ m, frieze_f g (n, m) = 1 := by
    intro m
    induction' m with m ih
    simp [frieze_f, hn]
    have := g.period 0
    simp [g.hd] at this
    exact this.symm
    have : ¬ n ≥ n+1 := by omega
    unfold frieze_f ; simp [this, ih, hn]
    left
    exact botBordZeros_n (n+1) m (by rfl)
  have positive: ∀ i, ∀ m, 1 ≤ i → i ≤ n → frieze_f g (i,m) > 0 := by
    intro i m
    induction' m with m ih₁ generalizing i
    intro hi₁ hi₂
    have hi₃ : ¬ i = 0 := by omega
    have hi₄ : ¬ i ≥ n+1 := by omega
    unfold frieze_f ; simp [hi₃, hi₄]
    exact g.pos (i-1)
    induction' i with i ih₂
    omega
    intro hi₁ hi₂
    by_cases hi : i = 0
    simp [hi, topBordOnes]
    by_cases hi' : i = n-1
    have : n-1+1 = n := by omega
    simp [this, hi', botBordOnes_n]
    specialize ih₂ (by omega) (by omega)
    have : ¬ n ≤ i := by omega
    unfold frieze_f ; simp +arith [this]
    have h₁ := ih₁ (i+1) (by omega) (by omega)
    have h₂ := ih₁ (i+2) (by omega) (by omega)
    positivity
  have diamond : ∀ i, ∀ m,  i ≤ n-1 → frieze_f g (i+1,m) * frieze_f g (i+1,m+1)-1 = frieze_f g (i+2,m) * frieze_f g (i,m+1) := by
    intro i m hi
    conv =>
      enter [1,1,2]
      unfold frieze_f
    have : ¬ n ≤ i := by omega
    simp +arith [this]
    have hpos : frieze_f g (i+1, m) > 0 := by linarith [positive (i+1) m (by omega) (by omega)]
    have hne : frieze_f g (i+1, m) ≠ 0 := ne_of_gt hpos
    field_simp [hne]; ring
  have non_zero : ∀ i m, 1 ≤ i ∧ i ≤ n → frieze_f g (i,m) ≠ 0 := λ i m ⟨hi₁, hi₂⟩ => by linarith [positive i m hi₁ hi₂]
  have : nzPattern_n ℚ (frieze_f g) n := by
    exact {topBordZeros, topBordOnes, botBordOnes_n, botBordZeros_n, diamond, non_zero}
  have integral: ∀ i, ∀ m, (frieze_f g (i,m)).den = 1 := by
    have key : ∀ m, (frieze_f g (2, m)).den = 1 := by
      intro m
      induction' m using Nat.strong_induction_on with m ih
      by_cases hm : m = 0
      simp [hm, frieze_f]
      norm_cast
      by_cases hm₂ : m ≤ n-2
      have key := pattern_nContinuant1 ℚ (frieze_f g) n m (by omega) 0
      have div : ∃ k : ℕ, (frieze_f g (m,0) + frieze_f g (m+2,0)) = frieze_f g (m+1,0)*k := by
        have hm₃ : ¬ n ≤ m := by omega
        have hm₄ : ¬ n ≤ m+1 := by omega
        have hm₅ : ¬ n+1 ≤ m := by omega
        unfold frieze_f ; simp [hm, hm₃, hm₄, hm₅]
        norm_cast
        have := g.div (m-1)
        have hm₆ : m-1+1 = m := by omega
        have hm₇ : m-1+2 = m+1 := by omega
        simp [hm₆, hm₇] at this
        exact this
      rcases div with ⟨k, hk⟩
      simp at key
      have hne : frieze_f g (m+1, 0) ≠ 0 := by linarith [positive (m+1) 0 (by omega) (by omega)]
      have h2m : frieze_f g (2,m) = k := by
        calc frieze_f g (2,m) = (frieze_f g (m,0) + frieze_f g (m+2,0)) / frieze_f g (m+1,0) := by rw [eq_div_iff hne]; linarith [key]
        _ = k := by rw [hk, mul_div_cancel_left₀ _ hne]
      rw [h2m]; simp
      have : n+1-(n-1)=2 := by omega
      by_cases hm₃ : m = n-1
      have key := glideSymm ℚ (frieze_f g) n (n-1) (by omega) 0
      simp [this] at key
      simp [hm₃, key, frieze_f]
      norm_cast
      by_cases hm₄ : m = n
      have key := glideSymm ℚ (frieze_f g) n (n-1) (by omega) 1
      have hm₅ : 1+(n-1)=n := by omega
      simp [this, hm₅] at key
      rw [hm₄, key] ; rw [hm₄] at ih
      suffices : ∀ i ≤ n-1, (frieze_f g (i,1)).den = 1
      · exact this (n-1) (by omega)
      intro i hi
      induction' i using Nat.twoStepInduction with i ih₁ ih₂
      simp [frieze_f]
      simp [frieze_f, hn, g.hd]
      simp +arith at ih₁ ih₂ hi
      specialize ih₁ (by omega)
      specialize ih₂ (by omega)
      have := pattern_nContinuant1 ℚ (frieze_f g) n i (by omega) 1
      rw [this]
      have := ih (1+i) (by omega)
      -- there should be a tactic to do the following two steps?
      rw [Rat.sub_eq_add_neg, Rat.add_num_den, Rat.neg_den, Rat.mul_den, ih₁, ih₂, this]
      simp ; norm_cast
      have h := translationInvariance ℚ (frieze_f g) n 2 (by omega) (m-(n+1))
      have : m-(n+1)+n+1 = m := by omega
      rw [this] at h
      exact h ▸ ih (m-(n+1)) (by omega)
    intro i
    induction' i using Nat.strong_induction_on with i ih
    match i with
    | 0 => intro ; simp [topBordZeros]
    | 1 => intro ; simp [topBordOnes]
    | 2 => exact key
    | i+3 =>
      by_cases hi : i+2 ≥ n
      intro ; simp [botBordZeros_n (i+3) _ (by omega)]
      intro m
      have key₂ := pattern_nContinuant1 ℚ (frieze_f g) n (i+1) (by omega) m
      simp +arith at key₂
      rw [key₂]
      have h₁ := key (i + m + 1)
      have h₂ := ih (i+1) (by omega) m
      have h₃ := ih (i+2) (by omega) m
      rw [Rat.sub_eq_add_neg, Rat.add_num_den, Rat.neg_den, Rat.mul_den, h₁, h₂, h₃]
      simp
  exact {topBordZeros, topBordOnes, botBordOnes_n, botBordZeros_n, diamond, integral, positive}
def arithFriezePatSet (n: ℕ) : Set (ℕ × ℕ → ℚ) :=
  { f | arith_fp f n}


