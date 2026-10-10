-- Prove2me | solution 1 for ArtinPrimitiveRoots.square_major_replacement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T19:16:23.029979+00:00
-- url     : https://prove2.me/submissions/2bdbc3a1-2134-4663-8c5d-e6813d331abf

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_minor_square_bound

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

open Classical in
/-- The raw inner sum of `expandedSquare` at the label products `a, b`. -/
noncomputable def rawInner (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
  ∑ r ∈ range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ range (⌊2 * Hn⌋₊ + 1),
    if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β else 0

/-- The inner sum of `majorSquare` at the label products `a, b`. -/
noncomputable def majInner (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
  ∑ r ∈ range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ range (⌊2 * Hn⌋₊ + 1),
    sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b

/-- `Q^sh_Y`: the part of `expandedSquare` over label pairs with `gcd(a, b) > 1`. -/
noncomputable def sharedSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) : ℂ :=
  (squareNorm x a : ℂ) * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
    if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else rawInner Y Hm Hn α β (∏ i, p i) (∏ i, p' i)

/-- `Q^{maj,sh}_Y`: the part of `majorSquare` over label pairs with `gcd(a, b) > 1`. -/
noncomputable def sharedMajorSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) : ℂ :=
  (squareNorm x a : ℂ) * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
    if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0
    else majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, p' i)

/-! ## Elementary inputs -/

/-- `∫_{[0,1)} e(θ n) dθ = 1_{n = 0}`. -/
lemma integral_Ico_exp_int (n : ℤ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((θ * n : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [show (fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ : ℂ) * n))) =
        fun θ : ℝ => Complex.exp (2 * π * Complex.I * n * θ) by
      funext θ; ring_nf]
    rw [this]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Ico 0 1 :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma measurableSet_majorArcs (x A₀ Y : ℝ) : MeasurableSet (majorArcs x A₀ Y) := by
  have : majorArcs x A₀ Y = Set.Ico 0 1 ∩ ⋃ k : ℕ, ⋃ c : ℤ,
      {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
    ext θ
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩; exact ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩
    · rintro ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩; exact ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩
  rw [this]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun c => ?_)
  by_cases hP : 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = {θ : ℝ | |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
      ext θ; simp only [Set.mem_ofPred_eq]; tauto
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = ∅ := by
      ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this]; exact MeasurableSet.empty

/-- `H_𝔪 = ψ(t/Y) 1_{t = b − a} − H_𝔐`. -/
lemma minorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    minorKernel x A₀ Y t a b =
      (arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0) - majorKernel x A₀ Y t a b := by
  unfold minorKernel majorKernel
  have hint : IntegrableOn (fun θ : ℝ =>
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) (Set.Ico 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self
  rw [setIntegral_sdiff (measurableSet_majorArcs x A₀ Y) hint (majorArcs_subset x A₀ Y), mul_sub]
  congr 2
  have := integral_Ico_exp_int (t - b + a)
  push_cast at this ⊢
  rw [this]

lemma dyadicBump_ne_zero {u : ℝ} (h : dyadicBump u ≠ 0) : 1 < u ∧ u < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    simp

lemma arcCutoff_eq_one {u : ℝ} (h : |u| ≤ 4) : arcCutoff u = 1 := by
  unfold arcCutoff
  rw [abs_le] at h
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- [21] (3.10): for coprime `a, b > 0` and `mn, rs ≥ 1`, a common `h` exists iff
`b m n − a r s = b − a`. -/
lemma exists_common_iff {a b m n r s : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (hmn : 1 ≤ m * n) (hrs : 1 ≤ r * s) :
    (∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h) ↔ sqDet a b m n r s - b + a = 0 := by
  unfold sqDet
  constructor
  · rintro ⟨h, h1, h2⟩
    have e1 : ((m * n : ℕ) : ℤ) = 1 + a * h := by
      rw [← Nat.sub_add_cancel hmn, h1]; push_cast; ring
    have e2 : ((r * s : ℕ) : ℤ) = 1 + b * h := by
      rw [← Nat.sub_add_cancel hrs, h2]; push_cast; ring
    push_cast at e1 e2
    linear_combination (b : ℤ) * e1 - (a : ℤ) * e2
  · intro heq
    obtain ⟨u, hu⟩ : ∃ u, m * n = u + 1 := ⟨m * n - 1, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, r * s = v + 1 := ⟨r * s - 1, by omega⟩
    have key : b * u = a * v := by
      have : (b : ℤ) * (u : ℤ) = (a : ℤ) * (v : ℤ) := by
        have e1 : ((m : ℤ) * n) = u + 1 := by exact_mod_cast hu
        have e2 : ((r : ℤ) * s) = v + 1 := by exact_mod_cast hv
        linear_combination heq + (-(b : ℤ)) * e1 + (a : ℤ) * e2
      exact_mod_cast this
    have hdvd : a ∣ u := by
      have : a ∣ u * b := ⟨v, by rw [mul_comm u b, key]⟩
      exact hab.dvd_of_dvd_mul_right this
    obtain ⟨h, rfl⟩ := hdvd
    refine ⟨h, by omega, ?_⟩
    have : a * v = a * (b * h) := by rw [← key]; ring
    have := Nat.eq_of_mul_eq_mul_left ha this
    omega

/-- The termwise identity on a coprime pair. -/
lemma term_identity (x A₀ Y : ℝ) (α β : ℕ → ℂ) (hα : α 0 = 0) (hβ : β 0 = 0)
    {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) (m n r s : ℕ) [Decidable
      (∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h)] :
    (if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β else 0) -
        sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b =
      sqWeight Y a b m n r s α β * minorKernel x A₀ Y (sqDet a b m n r s) a b := by
  by_cases hw : sqWeight Y a b m n r s α β = 0
  · simp [hw]
  have hm : m ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hα]
  have hn : n ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hβ]
  have hr : r ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hα]
  have hs : s ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hβ]
  have hηa : dyadicBump ((a : ℝ) / Y) ≠ 0 := by
    intro h0; apply hw; simp [sqWeight, h0]
  have hηb : dyadicBump ((b : ℝ) / Y) ≠ 0 := by
    intro h0; apply hw; simp [sqWeight, h0]
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm hn)
  have hrs : 1 ≤ r * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr hs)
  rw [minorKernel_eq, mul_sub, sub_left_inj]
  have hiff := exists_common_iff ha hab hmn hrs
  by_cases hE : ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h
  · have h0 : sqDet a b m n r s - b + a = 0 := hiff.1 hE
    rw [if_pos hE, if_pos h0]
    obtain ⟨ha1, ha4⟩ := dyadicBump_ne_zero hηa
    obtain ⟨hb1, hb4⟩ := dyadicBump_ne_zero hηb
    have hY : 0 < Y := by
      by_contra hY; push Not at hY
      have : (a : ℝ) / Y ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hY
      linarith
    have ht : (sqDet a b m n r s : ℝ) = b - a := by
      have : sqDet a b m n r s = (b : ℤ) - a := by linarith
      rw [this]; push_cast; ring
    have hψ : arcCutoff ((sqDet a b m n r s : ℝ) / Y) = 1 := by
      apply arcCutoff_eq_one
      rw [ht, sub_div, abs_le]
      constructor <;> linarith
    rw [hψ]; simp
  · have h0 : ¬ (sqDet a b m n r s - b + a = 0) := fun h => hE (hiff.2 h)
    rw [if_neg hE, if_neg h0]; simp

/-! ## The identity -/

/-- **[21] (3.10)–(3.11), exact form.** If `α₀ = β₀ = 0` then
`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`. -/
theorem expandedSquare_sub_majorSquare (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) (hα : α 0 = 0) (hβ : β 0 = 0) :
    expandedSquare x a Y Hm Hn α β - majorSquare x a A₀ Y Hm Hn α β =
      sharedSquare x a Y Hm Hn α β - sharedMajorSquare x a A₀ Y Hm Hn α β +
        minorSquare x a A₀ Y Hm Hn α β := by
  classical
  have hE : expandedSquare x a Y Hm Hn α β = (squareNorm x a : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        rawInner Y Hm Hn α β (∏ i, p i) (∏ i, p' i) := by
    unfold expandedSquare rawInner sqWeight; rfl
  have hM : majorSquare x a A₀ Y Hm Hn α β = (squareNorm x a : ℂ) *
      ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, p' i) := by
    unfold majorSquare majInner sqWeight sqDet; rfl
  rw [hE, hM]
  unfold sharedSquare sharedMajorSquare minorSquare
  rw [← mul_sub, ← mul_sub, ← mul_add]
  congr 1
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p' hp' => ?_
  split_ifs with hcop
  · simp only [sub_self, zero_add]
    have ha : 0 < ∏ i, p i := by
      refine Finset.prod_pos fun i _ => ?_
      have := (Fintype.mem_piFinset.1 hp) i
      unfold primeGroup at this
      exact (Finset.mem_filter.1 this).2.1.pos
    unfold rawInner majInner minInner
    simp only [← sum_sub_distrib]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
      sum_congr rfl fun s _ => ?_
    exact term_identity x A₀ Y α β hα hβ ha hcop m n r s
  · simp

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

/-- **(10.9) from the two cuts.** The shared-label bound `hsh` ([21] (3.9), (4.63); any `A₀`)
and the coprime minor-arc bound `hmin` (the content of [21] §§3.2–4.9) give
`square_major_replacement`, via the exact identity `expandedSquare_sub_majorSquare`. -/
theorem square_major_replacement_of_cuts (δ C c₁ c₂ : ℝ)
    (hsh : ∀ A₀ A : ℝ, 0 < A₀ → 0 < A → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖sharedSquare x a Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) ∧
            ‖sharedMajorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)))
    (hmin : ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A))) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖expandedSquare x a Y Hm Hn α β - majorSquare x a A₀ Y Hm Hn α β‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) := by
  intro A hA
  obtain ⟨A₀, hA₀, K₀, hK⟩ := hmin A hA
  refine ⟨A₀, hA₀, K₀, fun K hK1 hKK a ha hab => ?_⟩
  obtain ⟨c, x₀, hc⟩ := hK K hK1 hKK a ha hab
  obtain ⟨c', x₀', hc'⟩ := hsh A₀ A hA₀ hA K hK1 a ha hab
  refine ⟨c + 2 * c', max x₀ x₀', fun x Hm Hn hx hm hn h1 h2 α β hαs hβs hαb hβb Y hY => ?_⟩
  have hα0 : α 0 = 0 := by
    by_contra h
    obtain ⟨J, -, -, hJ⟩ := hαs
    exact absurd (hJ 0 h).2.1 (lt_irrefl 0)
  have hβ0 : β 0 = 0 := by
    by_contra h
    exact absurd (hβs 0 h).2.2.1 (lt_irrefl 0)
  have e := expandedSquare_sub_majorSquare x a A₀ Y Hm Hn α β hα0 hβ0
  have hmin' := hc x Hm Hn (le_of_max_le_left hx) hm hn h1 h2 α β hαs hβs hαb hβb Y hY
  obtain ⟨hs1, hs2⟩ := hc' x Hm Hn (le_of_max_le_right hx) hm hn h1 h2 α β hαs hβs hαb hβb Y hY
  rw [e]
  calc ‖sharedSquare x a Y Hm Hn α β - sharedMajorSquare x a A₀ Y Hm Hn α β +
        minorSquare x a A₀ Y Hm Hn α β‖
      ≤ ‖sharedSquare x a Y Hm Hn α β‖ + ‖sharedMajorSquare x a A₀ Y Hm Hn α β‖ +
          ‖minorSquare x a A₀ Y Hm Hn α β‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ _ := by linarith

end ArtinPrimitiveRoots.L102D
end

section
/-! # Draft bundle `Def_ArtinMinorOperator`: the operator of [21] §§3.2–3.3 (prover D)

The physical states, the good-position tests, the slot symmetrization `S`, the goodness projection
`G`, the row operation `T` with kernel [21] (3.15), `A = G S T S G`, the moment
`∑_P ⟨u_P, (AA*)^R u_P⟩` of (3.19)/(4.1), and the endpoint vectors `f = g` of (3.16).

Conventions. Lists have `J + 1` slots per group: slots `0, …, J − 1` are the pads (copied along an
edge, product `D`), slot `J` (`Fin.last J`) is the unshared label. The Hilbert-space measure
`∏ Vᵢ^{-(J+1)}` × counting is constant on states, so `σ`-adjoints are conjugate transposes; the
constant `stateNorm` is carried explicitly in `momentSum` and `opPairing`. The auxiliary damping
parameter of (3.15) is fixed to `q = 1/4`, so `q^{(ω(P₁)−KM)/2} = (1/2)^{ω(P₁)−KM}`. Test (i) and
test (ii) use all omission products (no dyad restriction; this only strengthens goodness). -/

namespace ArtinPrimitiveRoots

open Real

/-! ## Good positions ([21] §3.2) -/

/-- `‖t‖_{ℝ/ℤ} = |t − round t|`, the distance to the nearest integer. -/
noncomputable def circNorm (t : ℝ) : ℝ := |t - round t|


/-! ## Parameters, positions and physical states -/

/-! ## The operators -/

/-! ## The objects at the dyad `d₀ = 2^k`, with `J = padCount x`, `R = momentPower x`,
`U = 2^k Y H_m`, `V = H_n` -/

end ArtinPrimitiveRoots
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

lemma circNorm_eq_norm (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

/-- For a nonzero integer `n`, `{r ∈ (0,1] : ‖n r‖ ≤ ε}` has measure at most `2ε`
(multiplication by `n` preserves Haar measure on `ℝ/ℤ`). -/
lemma volume_circNorm_le (n : ℤ) (hn : n ≠ 0) (ε : ℝ) :
    volume ({r : ℝ | circNorm (n * r) ≤ ε} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * ε) := by
  set f : ℝ → UnitAddCircle := fun r => n • (r : UnitAddCircle)
  have hf : MeasurePreserving f (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    have := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn).comp
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
    simpa [f, Function.comp_def] using this
  have hset : {r : ℝ | circNorm (n * r) ≤ ε} = f ⁻¹' Metric.closedBall 0 ε := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, f]
    rw [circNorm_eq_norm, ← AddCircle.coe_zsmul]
    simp
  have hmeas : MeasurableSet (f ⁻¹' Metric.closedBall 0 ε) :=
    hf.measurable measurableSet_closedBall
  rw [hset, ← Measure.restrict_apply hmeas, hf.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

/-! ## Counting and asymptotics -/

/-- `C log L + D ≤ ε L^a` eventually, for `a, ε > 0`. -/
lemma eventually_log_le_rpow {a : ℝ} (ha : 0 < a) (C D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, C * log L + D ≤ ε * L ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := ε / (2 * (|C| + 1))) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * |D| / ε)
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with L hL1 hL2 hL3
  have hpos : 0 ≤ L ^ a := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos] at hL1
  have hlog : 0 ≤ log L := log_nonneg hL3
  rw [abs_of_nonneg hlog] at hL1
  have hC : C * log L ≤ |C| * log L := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hC2 : |C| * log L ≤ |C| * (ε / (2 * (|C| + 1)) * L ^ a) :=
    mul_le_mul_of_nonneg_left hL1 (abs_nonneg C)
  have hC3 : |C| * (ε / (2 * (|C| + 1)) * L ^ a) ≤ ε / 2 * L ^ a := by
    have : |C| / (|C| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc |C| * (ε / (2 * (|C| + 1)) * L ^ a) = (|C| / (|C| + 1)) * (ε / 2 * L ^ a) := by
          field_simp
      _ ≤ 1 * (ε / 2 * L ^ a) := by gcongr
      _ = ε / 2 * L ^ a := one_mul _
  have hD : D ≤ ε / 2 * L ^ a := by
    have : 2 * |D| / ε * ε = 2 * |D| := by field_simp
    have h' : 2 * |D| ≤ ε * L ^ a := by
      calc 2 * |D| = 2 * |D| / ε * ε := this.symm
        _ ≤ L ^ a * ε := by gcongr
        _ = ε * L ^ a := mul_comm _ _
    linarith [le_abs_self D]
  linarith

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harmonic_partial_sum_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `∑_{a,b ≤ X} gcd(a,b)/(ab) ≤ H_X^3`. -/
theorem sum_gcd_div_le (X : ℕ) :
    ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, ((Nat.gcd a b : ℝ) / (a * b)) ≤
      (∑ i ∈ Ioc 0 X, (1 / (i : ℝ))) ^ 3 := by
  rw [← Finset.sum_product']
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
    p.2 / Nat.gcd p.1 p.2) with hφ
  have hinj : Set.InjOn φ ↑(Ioc 0 X ×ˢ Ioc 0 X) := by
    rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have ea : a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ea' : a' = Nat.gcd a' b' * (a' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')).symm
    have eb' : b' = Nat.gcd a' b' * (b' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')).symm
    simp only [Prod.mk.injEq]
    constructor
    · rw [ea, ea']; exact congrArg₂ (· * ·) h1 h2
    · rw [eb, eb']; exact congrArg₂ (· * ·) h1 h3
  have hval : ∀ p ∈ Ioc 0 X ×ˢ Ioc 0 X, ((Nat.gcd p.1 p.2 : ℝ) / (p.1 * p.2)) =
      (fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) (φ p) := by
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_Ioc] at hp
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ hp.1.1
    have ea : (a : ℝ) = Nat.gcd a b * ((a / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : (b : ℝ) = Nat.gcd a b * ((b / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ha0 : ((a / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at ea; exact (Nat.pos_iff_ne_zero.mp hp.1.1) (by exact_mod_cast ea)
    have hb0 : ((b / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at eb; exact (Nat.pos_iff_ne_zero.mp hp.2.1) (by exact_mod_cast eb)
    have hg0 : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [ea, eb]
    field_simp
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) hinj]
  have hsub : (Ioc 0 X ×ˢ Ioc 0 X).image φ ⊆ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Ioc] at ht ⊢
    obtain ⟨⟨a, b⟩, ⟨⟨ha, haX⟩, hb, hbX⟩, rfl⟩ := ht
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
    refine ⟨⟨hg, (Nat.gcd_le_left _ ha).trans haX⟩, ⟨?_, (Nat.div_le_self _ _).trans haX⟩, ?_,
      (Nat.div_le_self _ _).trans hbX⟩
    · exact Nat.div_pos (Nat.gcd_le_left _ ha) hg
    · exact Nat.div_pos (Nat.gcd_le_right _ hb) hg
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)).trans
    (le_of_eq ?_)
  have : ∀ t ∈ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X, 1 / ((t.1 : ℝ) * t.2.1 * t.2.2) =
      (1 / (t.1 : ℝ)) * ((1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) := by
    intro t _; rw [one_div_mul_one_div, one_div_mul_one_div, mul_assoc]
  rw [Finset.sum_congr rfl this, Finset.sum_product]
  simp_rw [Finset.sum_product, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Second moment of the divisor function**: `∑_{n ≤ X} d(n)^2 ≤ X (1 + log X)^3`. -/
theorem sum_card_divisors_sq_le (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 ≤ X * (1 + Real.log X) ^ 3 := by
  have hdiv : ∀ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hd : n.divisors = (Ioc 0 X).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
      · rintro ⟨-, h⟩
        exact ⟨h, hn.1.ne'⟩
    rw [hd, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]
  rw [Finset.sum_congr rfl hdiv, Finset.sum_comm]
  have hinner : ∀ a ∈ Ioc 0 X, ∑ n ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X,
      (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) ≤
        ∑ b ∈ Ioc 0 X, (X : ℝ) * (Nat.gcd a b / (a * b)) := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_Ioc] at ha hb
    have hcount : ∑ n ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) =
        ((X / Nat.lcm a b : ℕ) : ℝ) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Nat.lcm_dvd_iff]
      split_ifs <;> simp
    rw [hcount]
    have hl : 0 < Nat.lcm a b := Nat.lcm_pos ha.1 hb.1
    have h1 : ((X / Nat.lcm a b : ℕ) : ℝ) ≤ (X : ℝ) / Nat.lcm a b := Nat.cast_div_le
    have h2 : (X : ℝ) / Nat.lcm a b = X * (Nat.gcd a b / (a * b)) := by
      have := Nat.gcd_mul_lcm a b
      have hab : (a : ℝ) * b = Nat.gcd a b * Nat.lcm a b := by exact_mod_cast this.symm
      rw [hab]
      have : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ ha.1).ne'
      have : (Nat.lcm a b : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
    linarith
  refine (Finset.sum_le_sum hinner).trans ?_
  simp_rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_gcd_div_le X).trans ?_) (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (harmonic_partial_sum_nonneg X) (harm_le X) 3

end ArtinBV
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- One of four positive integers with product `m³` has fourth power at most `m³`. -/
lemma exists_pow_four_le {a b c d m : ℕ} (h : a * b * c * d = m ^ 3) :
    a ^ 4 ≤ m ^ 3 ∨ b ^ 4 ≤ m ^ 3 ∨ c ^ 4 ≤ m ^ 3 ∨ d ^ 4 ≤ m ^ 3 := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨ha, hb, hc', hd⟩ := hc
  have h1 := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' ha hb (Nat.zero_le _) (Nat.zero_le _)) hc'
    (Nat.zero_le _) (Nat.zero_le _)) hd (Nat.zero_le _) (Nat.zero_le _)
  have h2 : a ^ 4 * b ^ 4 * c ^ 4 * d ^ 4 = (m ^ 3) ^ 4 := by
    rw [← h]; ring
  rw [h2] at h1
  have : m ^ 3 * m ^ 3 * m ^ 3 * m ^ 3 = (m ^ 3) ^ 4 := by ring
  omega

/-- For divisors `d₁, d₂` of `n > 0`, one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)`
has `lcm⁴ ≤ n³`. -/
lemma exists_flip_lcm_le {n d₁ d₂ : ℕ} (hn : 0 < n) (h₁ : d₁ ∣ n) (h₂ : d₂ ∣ n) :
    Nat.lcm d₁ d₂ ^ 4 ≤ n ^ 3 ∨ Nat.lcm (n / d₁) (n / d₂) ^ 4 ≤ n ^ 3 ∨
      Nat.lcm d₁ (n / d₂) ^ 4 ≤ n ^ 3 ∨ Nat.lcm (n / d₁) d₂ ^ 4 ≤ n ^ 3 := by
  have hd₁ : 0 < d₁ := Nat.pos_of_dvd_of_pos h₁ hn
  have hd₂ : 0 < d₂ := Nat.pos_of_dvd_of_pos h₂ hn
  set g := Nat.gcd d₁ d₂ with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd₁
  obtain ⟨u, hu⟩ : g ∣ d₁ := Nat.gcd_dvd_left _ _
  obtain ⟨v, hv⟩ : g ∣ d₂ := Nat.gcd_dvd_right _ _
  have hlcm : Nat.lcm d₁ d₂ = g * u * v := by
    have h := Nat.gcd_mul_lcm d₁ d₂
    rw [← hg] at h
    have : g * Nat.lcm d₁ d₂ = g * (g * u * v) := by
      rw [h]; nth_rewrite 1 [hu]; nth_rewrite 1 [hv]; ring
    exact Nat.eq_of_mul_eq_mul_left hg0 this
  obtain ⟨w, hw⟩ : Nat.lcm d₁ d₂ ∣ n := Nat.lcm_dvd h₁ h₂
  rw [hlcm] at hw
  have hu0 : 0 < u := by rcases Nat.eq_zero_or_pos u with h | h
                         · rw [h, mul_zero] at hu; omega
                         · exact h
  have hv0 : 0 < v := by rcases Nat.eq_zero_or_pos v with h | h
                         · rw [h, mul_zero] at hv; omega
                         · exact h
  have hw0 : 0 < w := by rcases Nat.eq_zero_or_pos w with h | h
                         · rw [h, mul_zero] at hw; omega
                         · exact h
  have hn1 : n / d₁ = v * w := by
    rw [hw, hu]; exact Nat.div_eq_of_eq_mul_right (by positivity) (by ring)
  have hn2 : n / d₂ = u * w := by
    rw [hw, hv]; exact Nat.div_eq_of_eq_mul_right (by positivity) (by ring)
  rw [hn1, hn2, hlcm, hu, hv]
  have b2 : Nat.lcm (v * w) (u * w) ≤ u * v * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨u, by ring⟩ ⟨v, by ring⟩)
  have b3 : Nat.lcm (g * u) (u * w) ≤ g * u * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨w, by ring⟩ ⟨g, by ring⟩)
  have b4 : Nat.lcm (v * w) (g * v) ≤ g * v * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨g, by ring⟩ ⟨w, by ring⟩)
  have hprod : (g * u * v) * (u * v * w) * (g * u * w) * (g * v * w) = n ^ 3 := by
    rw [hw]; ring
  rcases exists_pow_four_le hprod with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((Nat.pow_le_pow_left b2 4).trans h))
  · exact Or.inr (Or.inr (Or.inl ((Nat.pow_le_pow_left b3 4).trans h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.pow_le_pow_left b4 4).trans h)))

/-- The four flips of a divisor pair. -/
def flip4 (n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, q => q
  | 1, q => (n / q.1, n / q.2)
  | 2, q => (q.1, n / q.2)
  | _, q => (n / q.1, q.2)

lemma flip4_mem {n : ℕ} (k : ℕ) {q : ℕ × ℕ} (hq : q ∈ n.divisors ×ˢ n.divisors) :
    flip4 n k q ∈ n.divisors ×ˢ n.divisors := by
  simp only [mem_product, Nat.mem_divisors] at hq ⊢
  obtain ⟨⟨h1, hn⟩, h2, -⟩ := hq
  match k with
  | 0 => exact ⟨⟨h1, hn⟩, h2, hn⟩
  | 1 => exact ⟨⟨Nat.div_dvd_of_dvd h1, hn⟩, Nat.div_dvd_of_dvd h2, hn⟩
  | 2 => exact ⟨⟨h1, hn⟩, Nat.div_dvd_of_dvd h2, hn⟩
  | k + 3 => exact ⟨⟨Nat.div_dvd_of_dvd h1, hn⟩, h2, hn⟩

lemma flip4_flip4 {n : ℕ} (k : ℕ) {q : ℕ × ℕ} (hq : q ∈ n.divisors ×ˢ n.divisors) :
    flip4 n k (flip4 n k q) = q := by
  simp only [mem_product, Nat.mem_divisors] at hq
  obtain ⟨⟨h1, hn⟩, h2, -⟩ := hq
  obtain ⟨q1, q2⟩ := q
  match k with
  | 0 => rfl
  | 1 => simp [flip4, Nat.div_div_self h1 hn, Nat.div_div_self h2 hn]
  | 2 => simp [flip4, Nat.div_div_self h2 hn]
  | k + 3 => simp [flip4, Nat.div_div_self h1 hn]

/-- `τ(n)² ≤ 4 #{(e₁, e₂) : e₁, e₂ ∣ n, lcm(e₁, e₂)⁴ ≤ n³}`. -/
lemma card_divisors_sq_le (n : ℕ) (hn : 0 < n) :
    (n.divisors ×ˢ n.divisors).card ≤
      4 * ((n.divisors ×ˢ n.divisors).filter fun q => Nat.lcm q.1 q.2 ^ 4 ≤ n ^ 3).card := by
  set D := n.divisors ×ˢ n.divisors
  set good : ℕ × ℕ → Prop := fun q => Nat.lcm q.1 q.2 ^ 4 ≤ n ^ 3
  have hsub : D ⊆ (range 4).biUnion fun k => D.filter fun q => good (flip4 n k q) := by
    intro q hq
    have hq' := hq
    simp only [D, mem_product, Nat.mem_divisors] at hq'
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hq'
    simp only [mem_biUnion, mem_range, mem_filter]
    rcases exists_flip_lcm_le hn h1 h2 with h | h | h | h
    · exact ⟨0, by norm_num, hq, h⟩
    · exact ⟨1, by norm_num, hq, h⟩
    · exact ⟨2, by norm_num, hq, h⟩
    · exact ⟨3, by norm_num, hq, h⟩
  have heq : ∀ k, (D.filter fun q => good (flip4 n k q)).card = (D.filter good).card := by
    intro k
    refine Finset.card_nbij' (flip4 n k) (flip4 n k) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq ⊢
      exact ⟨flip4_mem k hq.1, hq.2⟩
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq ⊢
      exact ⟨flip4_mem k hq.1, by rw [flip4_flip4 k hq.1]; exact hq.2⟩
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq
      exact flip4_flip4 k hq.1
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq
      exact flip4_flip4 k hq.1
  calc D.card ≤ ((range 4).biUnion fun k => D.filter fun q => good (flip4 n k q)).card :=
        card_le_card hsub
    _ ≤ ∑ k ∈ range 4, (D.filter fun q => good (flip4 n k q)).card := card_biUnion_le
    _ = 4 * (D.filter good).card := by simp [heq]

/-- The solutions `h ≤ Z` of `e ∣ 1 + l h` form at most one residue class modulo `e`. -/
lemma card_filter_dvd_le (e l Z : ℕ) (_he : 0 < e) :
    ((range (Z + 1)).filter fun h => e ∣ 1 + l * h).card ≤ Z / e + 1 := by
  set S := (range (Z + 1)).filter fun h => e ∣ 1 + l * h
  rcases S.eq_empty_or_nonempty with hS | ⟨h₀, hh₀⟩
  · rw [hS]; simp
  have hcop : Nat.Coprime e l := by
    have h0 := (mem_filter.1 hh₀).2
    have hd : Nat.gcd e l ∣ 1 :=
      (Nat.dvd_add_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right e l) h₀)).1
        ((Nat.gcd_dvd_left e l).trans h0)
    exact Nat.eq_one_of_dvd_one hd
  have hmod : ∀ h ∈ S, ∀ h' ∈ S, h % e = h' % e := by
    intro h hh h' hh'
    have e1 := (Nat.modEq_zero_iff_dvd.2 (mem_filter.1 hh).2)
    have e2 := (Nat.modEq_zero_iff_dvd.2 (mem_filter.1 hh').2)
    have e3 : 1 + l * h ≡ 1 + l * h' [MOD e] := e1.trans e2.symm
    have e4 : l * h ≡ l * h' [MOD e] := Nat.ModEq.add_left_cancel' 1 e3
    exact Nat.ModEq.cancel_left_of_coprime (hcop : Nat.gcd e l = 1) e4
  have hinj : Set.InjOn (fun h => h / e) S := by
    intro h hh h' hh' hq
    simp only at hq
    rw [← Nat.div_add_mod h e, ← Nat.div_add_mod h' e, hq, hmod h hh h' hh']
  have hmaps : Set.MapsTo (fun h => h / e) S (range (Z / e + 1)) := by
    intro h hh
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, S] at hh
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have := card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-- **[21] (3.9).** If every `m` with `m⁴ ≤ (1 + lZ)³` is at most `T`, then
`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³`. -/
theorem sum_card_divisors_sq_progression (l Z T : ℕ)
    (hT : ∀ m : ℕ, m ^ 4 ≤ (1 + l * Z) ^ 3 → m ≤ T) :
    ∑ h ∈ range (Z + 1), (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * ((Z : ℝ) + T) * (1 + Real.log T) ^ 3 := by
  set P := Ioc 0 T ×ˢ Ioc 0 T
  -- pointwise: `τ(n)² ≤ 4 #{(e₁,e₂) ∈ [1,T]² : lcm ≤ T, lcm ∣ n}`
  have hpt : ∀ h ∈ range (Z + 1), (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * ∑ q ∈ P, if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0 := by
    intro h hh
    have hn : 0 < 1 + l * h := by omega
    have hhZ : h ≤ Z := Nat.lt_succ_iff.1 (mem_range.1 hh)
    have h1 := card_divisors_sq_le (1 + l * h) hn
    rw [card_product] at h1
    have h2 : ((((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
        fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3).card : ℝ) ≤
        ∑ q ∈ P, if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0 := by
      rw [sum_boole]
      have hmaps : Set.MapsTo id
          (↑(((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
            fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3) : Set (ℕ × ℕ))
          ↑(P.filter fun q => Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h) := by
        intro q hq
        rw [mem_coe, mem_filter, mem_product, Nat.mem_divisors, Nat.mem_divisors] at hq
        obtain ⟨⟨⟨hq1, -⟩, hq2, -⟩, hq4⟩ := hq
        have hpow : (1 + l * h) ^ 3 ≤ (1 + l * Z) ^ 3 :=
          Nat.pow_le_pow_left (by have := Nat.mul_le_mul_left l hhZ; omega) 3
        have hlt : Nat.lcm q.1 q.2 ≤ T := hT _ (hq4.trans hpow)
        have hq1' : 0 < q.1 := Nat.pos_of_dvd_of_pos hq1 hn
        have hq2' : 0 < q.2 := Nat.pos_of_dvd_of_pos hq2 hn
        have hl1 : q.1 ≤ Nat.lcm q.1 q.2 :=
          Nat.le_of_dvd (Nat.lcm_pos hq1' hq2') (Nat.dvd_lcm_left _ _)
        have hl2 : q.2 ≤ Nat.lcm q.1 q.2 :=
          Nat.le_of_dvd (Nat.lcm_pos hq1' hq2') (Nat.dvd_lcm_right _ _)
        rw [id, mem_coe, mem_filter, mem_product, mem_Ioc, mem_Ioc]
        exact ⟨⟨⟨hq1', hl1.trans hlt⟩, hq2', hl2.trans hlt⟩, hlt, Nat.lcm_dvd hq1 hq2⟩
      exact_mod_cast card_le_card_of_injOn id hmaps (Set.injOn_id _)
    have h1' : ((((1 + l * h).divisors.card * (1 + l * h).divisors.card : ℕ)) : ℝ) ≤
        4 * ((((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
          fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3).card : ℝ) := by exact_mod_cast h1
    push_cast at h1'
    nlinarith
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, sum_comm]
  -- count `h` in one residue class
  have hcount : ∀ q ∈ P, ∑ h ∈ range (Z + 1),
      (if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0) ≤
      ((Z : ℝ) + T) * ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) := by
    intro q hq
    simp only [P, mem_product, mem_Ioc] at hq
    obtain ⟨⟨hq1, -⟩, hq2, -⟩ := hq
    have hl0 : 0 < Nat.lcm q.1 q.2 := Nat.lcm_pos hq1 hq2
    have hgl : ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) = 1 / (Nat.lcm q.1 q.2 : ℝ) := by
      have := Nat.gcd_mul_lcm q.1 q.2
      have h' : ((q.1 : ℝ) * q.2) = Nat.gcd q.1 q.2 * Nat.lcm q.1 q.2 := by exact_mod_cast this.symm
      have hg0 : (Nat.gcd q.1 q.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ hq1).ne'
      rw [h']; field_simp
    rw [hgl]
    by_cases hlT : Nat.lcm q.1 q.2 ≤ T
    · simp only [hlT, true_and]
      rw [sum_boole]
      have hc := card_filter_dvd_le (Nat.lcm q.1 q.2) l Z hl0
      have hc' : (((range (Z + 1)).filter fun h => Nat.lcm q.1 q.2 ∣ 1 + l * h).card : ℝ) ≤
          (Z / Nat.lcm q.1 q.2 : ℕ) + 1 := by exact_mod_cast hc
      have hdiv : ((Z / Nat.lcm q.1 q.2 : ℕ) : ℝ) ≤ (Z : ℝ) / Nat.lcm q.1 q.2 := Nat.cast_div_le
      have hlr : (0 : ℝ) < Nat.lcm q.1 q.2 := by exact_mod_cast hl0
      have h1 : (1 : ℝ) ≤ (T : ℝ) / Nat.lcm q.1 q.2 := by
        rw [le_div_iff₀ hlr]; exact_mod_cast (by simpa using hlT)
      calc _ ≤ ((Z / Nat.lcm q.1 q.2 : ℕ) : ℝ) + 1 := hc'
        _ ≤ (Z : ℝ) / Nat.lcm q.1 q.2 + (T : ℝ) / Nat.lcm q.1 q.2 := by linarith
        _ = ((Z : ℝ) + T) * (1 / (Nat.lcm q.1 q.2 : ℝ)) := by ring
    · simp only [hlT, false_and, if_false, sum_const_zero]
      positivity
  refine (mul_le_mul_of_nonneg_left (sum_le_sum hcount) (by norm_num)).trans ?_
  rw [← mul_sum, ← mul_assoc]
  have hP : ∑ q ∈ P, ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) ≤ (1 + Real.log T) ^ 3 := by
    rw [sum_product]
    refine (ArtinBV.sum_gcd_div_le T).trans ?_
    exact pow_le_pow_left₀ (ArtinBV.harmonic_partial_sum_nonneg T) (ArtinBV.harm_le T) 3
  have h0 : (0 : ℝ) ≤ 4 * ((Z : ℝ) + T) := by positivity
  exact mul_le_mul_of_nonneg_left hP h0

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

lemma dyadicBump_nonneg (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_dyadicBump_le_one (u : ℝ) : |dyadicBump u| ≤ 1 := by
  rw [abs_of_nonneg (dyadicBump_nonneg u)]; exact dyadicBump_le_one u

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

/-- The number of factorizations `m n = k` with `m, n` in given finite sets is at most `τ(k)`. -/
lemma card_mul_eq_le (A B : Finset ℕ) (k : ℕ) (hk : 0 < k) :
    ((A ×ˢ B).filter fun q => q.1 * q.2 = k).card ≤ k.divisors.card := by
  refine card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq q' hq' h => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq] at hq
    rw [mem_coe, Nat.mem_divisors]
    exact ⟨⟨q.2, hq.2.symm⟩, hk.ne'⟩
  · simp only [coe_filter, Set.mem_ofPred_eq] at hq hq'
    have h1 := hq.2
    have h2 := hq'.2
    have hq1 : 0 < q.1 := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at h1; omega)
    have : q.2 = q'.2 := by
      rw [h] at h1
      exact Nat.eq_of_mul_eq_mul_left (h ▸ hq1) (h1.trans h2.symm)
    exact Prod.ext h this

/-- Regrouping a sum over pairs `(m, n)` by the product `k = m n`. -/
lemma sum_prod_le_sum_tau (A B : Finset ℕ) (N : ℕ) (G : ℕ → ℝ) (hG : ∀ k, 0 ≤ G k)
    (hA : ∀ m ∈ A, 0 < m) (hB : ∀ n ∈ B, 0 < n) (hN : ∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) :
    ∑ m ∈ A, ∑ n ∈ B, G (m * n) ≤ ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) * G k := by
  rw [← sum_product']
  rw [← sum_fiberwise_of_maps_to (s := A ×ˢ B) (t := Ioc 0 N) (g := fun q => q.1 * q.2)
    (fun q hq => by
      rw [mem_product] at hq
      exact mem_Ioc.2 ⟨Nat.mul_pos (hA _ hq.1) (hB _ hq.2), hN _ hq.1 _ hq.2⟩)]
  refine sum_le_sum fun k hk => ?_
  have hk0 : 0 < k := (mem_Ioc.1 hk).1
  rw [sum_congr rfl (fun q hq => by rw [(mem_filter.1 hq).2]), sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_mul_eq_le A B k hk0) (hG k)

/-- An open window of length `< 10 a` contains at most `10` multiples-indices: if `Y < a` then
`#{l ∈ S : |c − a l| < 5Y} ≤ 10`. -/
lemma card_window_le (S : Finset ℕ) (a : ℕ) (Y c : ℝ) (hY : 0 < Y) (ha : Y < a) :
    (S.filter fun l : ℕ => |c - a * (l : ℝ)| < 5 * Y).card ≤ 10 := by
  set F := S.filter fun l : ℕ => |c - a * (l : ℝ)| < 5 * Y
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF]; simp
  set l₀ := F.min' hF
  have hl₀ : l₀ ∈ F := F.min'_mem hF
  have hsub : F ⊆ Icc l₀ (l₀ + 9) := by
    intro l hl
    rw [mem_Icc]
    refine ⟨F.min'_le l hl, ?_⟩
    have h1 := (mem_filter.1 hl).2
    have h2 := (mem_filter.1 hl₀).2
    rw [abs_lt] at h1 h2
    have hapos : (0 : ℝ) < a := hY.trans ha
    have : (a : ℝ) * ((l : ℝ) - l₀) < 10 * a := by nlinarith
    have : (l : ℝ) - l₀ < 10 := by nlinarith
    have : (l : ℝ) < l₀ + 10 := by linarith
    have : l < l₀ + 10 := by exact_mod_cast this
    omega
  calc F.card ≤ (Icc l₀ (l₀ + 9)).card := card_le_card hsub
    _ = 10 := by simp only [Nat.card_Icc]; omega

/-- `|α m| ≤ L^C · 1_{m ≠ 0}` when `α₀ = 0`. -/
lemma norm_coeff_le (α : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (m : ℕ) :
    ‖α m‖ ≤ B * (if m ≠ 0 then 1 else 0) := by
  by_cases hm : m = 0
  · subst hm; simp [hα0]
  · simp [hm, hαB m]

/-! ## The measure of the major arcs -/

/-- `vol 𝔐 ≤ 4 L^{3A₀}/Y` (`L = log x ≥ 1`, `A₀ ≥ 0`, `Y > 0`). -/
lemma volume_majorArcs_le (x A₀ Y : ℝ) (hL : 1 ≤ log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    volume (majorArcs x A₀ Y) ≤ ENNReal.ofReal (4 * log x ^ (3 * A₀) / Y) := by
  set Q := log x ^ A₀
  set K₀ := ⌊Q⌋₊
  set ρ := 2 * Q / Y
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL hA₀
  have hsub : majorArcs x A₀ Y ⊆ {0} ∪ ⋃ k ∈ Icc 1 K₀,
      ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩ Set.Ioc 0 1) := by
    rintro θ ⟨h0, h1, k, hk1, hkQ, c, -, hc⟩
    rcases h0.lt_or_eq with h0 | h0
    · right
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨k, ⟨hk1, Nat.le_floor hkQ⟩, ?_, h0, h1.le⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc circNorm (((k : ℤ) : ℝ) * θ) ≤ |((k : ℤ) : ℝ) * θ - c| := round_le _ c
        _ = k * |θ - c / k| := by
            have e : ((k : ℤ) : ℝ) * θ - c = k * (θ - c / k) := by
              push_cast; field_simp
            rw [e, abs_mul, abs_of_pos hk0]
        _ ≤ k * ρ := by gcongr
    · left; exact h0.symm
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ k ∈ Icc 1 K₀, volume ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩
      Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (k * ρ)) := fun k hk =>
    volume_circNorm_le k (by have := (mem_Icc.1 hk).1; omega) _
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK₀ : (K₀ : ℝ) ≤ Q := Nat.floor_le (by positivity)
  have hsum : ∑ k ∈ Icc 1 K₀, 2 * ((k : ℝ) * ρ) ≤ ∑ _k ∈ Icc 1 K₀, 2 * (Q * ρ) := by
    refine sum_le_sum fun k hk => ?_
    have : (k : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hk).2).trans hK₀
    gcongr
  refine hsum.trans ?_
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  have h3 : log x ^ (3 * A₀) = Q * Q * Q := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  rw [h3]
  have hρ : 0 ≤ ρ := by positivity
  calc (K₀ : ℝ) * (2 * (Q * ρ)) ≤ Q * (2 * (Q * ρ)) := by gcongr
    _ = 4 * (Q * Q * Q) / Y := by simp only [ρ]; ring

/-! ## The raw inner sum at one pair of label products -/

lemma norm_sqWeight_le (Y : ℝ) (a b m n r s : ℕ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) :
    ‖sqWeight Y a b m n r s α β‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      ((if m ≠ 0 then 1 else 0) * (if n ≠ 0 then 1 else 0) * (if r ≠ 0 then 1 else 0) *
        (if s ≠ 0 then 1 else 0)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  unfold sqWeight
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have h1 := norm_coeff_le α B hα0 hαB m
  have h2 := norm_coeff_le α B hα0 hαB r
  have h3 := norm_coeff_le β B hβ0 hβB n
  have h4 := norm_coeff_le β B hβ0 hβB s
  rw [abs_mul]
  have hη : 0 ≤ |dyadicBump (a / Y)| * |dyadicBump (b / Y)| := by positivity
  calc |dyadicBump (a / Y)| * |dyadicBump (b / Y)| * ‖α m‖ * ‖α r‖ * ‖β n‖ * ‖β s‖
      ≤ |dyadicBump (a / Y)| * |dyadicBump (b / Y)| * (B * (if m ≠ 0 then 1 else 0)) *
          (B * (if r ≠ 0 then 1 else 0)) * (B * (if n ≠ 0 then 1 else 0)) *
          (B * (if s ≠ 0 then 1 else 0)) := by gcongr
    _ = _ := by ring

/-- **The raw inner sum** at label products `Y < a, b`: `‖rawInner‖ ≤ |η η| B⁴ · 4(Z + T)(1 + log T)³`
with `Z = ⌊4 H_m H_n / Y⌋`, by `∑_h τ(1+ah) τ(1+bh)` and (3.9). -/
lemma norm_rawInner_le (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (hY : 0 < Y)
    (a b : ℕ) (ha : Y < a) (_hb : Y < b) (T : ℕ)
    (hTa : ∀ m : ℕ, m ^ 4 ≤ (1 + a * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ T)
    (hTb : ∀ m : ℕ, m ^ 4 ≤ (1 + b * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ T) :
    ‖rawInner Y Hm Hn α β a b‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      (4 * ((⌊4 * Hm * Hn / Y⌋₊ : ℝ) + T) * (1 + log T) ^ 3) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  set Z := ⌊4 * Hm * Hn / Y⌋₊
  set E := |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4
  have hE : 0 ≤ E := by positivity
  set R1 := range (⌊2 * Hm⌋₊ + 1)
  set R2 := range (⌊2 * Hn⌋₊ + 1)
  set f : ℕ → ℕ → ℕ → ℝ := fun m n h => if m * n = 1 + a * h then 1 else 0
  set g : ℕ → ℕ → ℕ → ℝ := fun r s h => if r * s = 1 + b * h then 1 else 0
  have hapos : (0 : ℝ) < a := hY.trans ha
  -- pointwise
  have hpt : ∀ m ∈ R1, ∀ n ∈ R2, ∀ r ∈ R1, ∀ s ∈ R2,
      ‖(if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β
        else 0)‖ ≤ E * ∑ h ∈ range (Z + 1), f m n h * g r s h := by
    intro m hm n hn r hr s hs
    have hsum0 : 0 ≤ ∑ h ∈ range (Z + 1), f m n h * g r s h :=
      sum_nonneg fun h _ => by simp only [f, g]; split_ifs <;> norm_num
    split_ifs with hE'
    · obtain ⟨h₀, hh1, hh2⟩ := hE'
      have hw := norm_sqWeight_le Y a b m n r s α β B hα0 hβ0 hαB hβB
      by_cases hz : m ≠ 0 ∧ n ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0
      · obtain ⟨hm0, hn0, hr0, hs0⟩ := hz
        simp only [hm0, hn0, hr0, hs0, ne_eq, not_false_eq_true, if_true, mul_one] at hw
        have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm0 hn0)
        have hrs : 1 ≤ r * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr0 hs0)
        have e1 : m * n = 1 + a * h₀ := by omega
        have e2 : r * s = 1 + b * h₀ := by omega
        have hh₀ : h₀ ∈ range (Z + 1) := by
          rw [mem_range, Nat.lt_succ_iff]
          apply Nat.le_floor
          have hm' : (m : ℝ) ≤ 2 * Hm :=
            (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hm))).trans (Nat.floor_le (by positivity))
          have hn' : (n : ℝ) ≤ 2 * Hn :=
            (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hn))).trans (Nat.floor_le (by positivity))
          have hprod : (a : ℝ) * h₀ < 4 * Hm * Hn := by
            have : ((m * n : ℕ) : ℝ) = 1 + a * h₀ := by exact_mod_cast e1
            push_cast at this
            have : (m : ℝ) * n ≤ 2 * Hm * (2 * Hn) :=
              mul_le_mul hm' hn' (Nat.cast_nonneg _) (by positivity)
            linarith
          rw [le_div_iff₀ hY]
          have : (h₀ : ℝ) * Y ≤ h₀ * a := by gcongr
          linarith [mul_comm (a : ℝ) h₀]
        have h1 : 1 ≤ ∑ h ∈ range (Z + 1), f m n h * g r s h := by
          have hle := single_le_sum (f := fun h => f m n h * g r s h)
            (fun h _ => by simp only [f, g]; split_ifs <;> norm_num) hh₀
          have hval : f m n h₀ * g r s h₀ = 1 := by simp only [f, g, e1, e2, if_true, mul_one]
          calc (1 : ℝ) = f m n h₀ * g r s h₀ := hval.symm
            _ ≤ _ := hle
        calc ‖sqWeight Y a b m n r s α β‖ ≤ E := hw
          _ = E * 1 := (mul_one E).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hE
      · have hzero : (if m ≠ 0 then (1 : ℝ) else 0) * (if n ≠ 0 then 1 else 0) *
            (if r ≠ 0 then 1 else 0) * (if s ≠ 0 then 1 else 0) = 0 := by
          simp only [not_and_or, not_not] at hz
          rcases hz with h | h | h | h <;> simp [h]
        rw [hzero, mul_zero] at hw
        exact hw.trans (mul_nonneg hE hsum0)
    · rw [norm_zero]; exact mul_nonneg hE hsum0
  -- sum the pointwise bound
  have hstep1 : ‖rawInner Y Hm Hn α β a b‖ ≤
      ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, E * ∑ h ∈ range (Z + 1), f m n h * g r s h := by
    unfold rawInner
    refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
    exact hpt m hm n hn r hr s hs
  have hstep2 : ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2,
      E * ∑ h ∈ range (Z + 1), f m n h * g r s h =
      E * ∑ h ∈ range (Z + 1), (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h) := by
    set H := range (Z + 1)
    have hprod : ∀ h, (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h) =
        ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h := by
      intro h
      rw [sum_mul]; refine sum_congr rfl fun m _ => ?_
      rw [sum_mul]; refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
    have hcomm : ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, ∑ h ∈ H, f m n h * g r s h =
        ∑ h ∈ H, ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h := by
      calc _ = ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ h ∈ H, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ => sum_comm
        _ = ∑ m ∈ R1, ∑ n ∈ R2, ∑ h ∈ H, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_comm
        _ = ∑ m ∈ R1, ∑ h ∈ H, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_comm
        _ = _ := sum_comm
    simp only [← mul_sum]
    rw [hcomm]
    simp only [hprod]
  have hfib : ∀ (c : ℕ), ∀ k : ℕ, 0 < k → ∀ (A' B' : Finset ℕ),
      ∑ m ∈ A', ∑ n ∈ B', (if m * n = k then (1 : ℝ) else 0) ≤ (k.divisors.card : ℝ) := by
    intro _ k hk A' B'
    rw [← sum_product', sum_boole]
    exact_mod_cast card_mul_eq_le A' B' k hk
  have hstep3 : ∑ h ∈ range (Z + 1), (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h)
      ≤ ∑ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
          (((1 + b * h).divisors.card : ℕ) : ℝ) := by
    refine sum_le_sum fun h _ => mul_le_mul (hfib 0 _ (by omega) R1 R2) (hfib 0 _ (by omega) R1 R2)
      (sum_nonneg fun r _ => sum_nonneg fun s _ => by simp only [g]; split_ifs <;> norm_num)
      (Nat.cast_nonneg _)
  have hstep4 : ∑ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
      (((1 + b * h).divisors.card : ℕ) : ℝ) ≤ 4 * ((Z : ℝ) + T) * (1 + log T) ^ 3 := by
    have ha3 := sum_card_divisors_sq_progression a Z T hTa
    have hb3 := sum_card_divisors_sq_progression b Z T hTb
    have : ∀ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
        (((1 + b * h).divisors.card : ℕ) : ℝ) ≤ ((((1 + a * h).divisors.card : ℕ) : ℝ) ^ 2 +
          (((1 + b * h).divisors.card : ℕ) : ℝ) ^ 2) / 2 := fun h _ => by
      nlinarith [sq_nonneg ((((1 + a * h).divisors.card : ℕ) : ℝ) -
        (((1 + b * h).divisors.card : ℕ) : ℝ))]
    refine (sum_le_sum this).trans ?_
    rw [← sum_div, sum_add_distrib]
    linarith
  calc ‖rawInner Y Hm Hn α β a b‖ ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ E * (4 * ((Z : ℝ) + T) * (1 + log T) ^ 3) :=
        mul_le_mul_of_nonneg_left (hstep3.trans hstep4) hE

/-! ## The major inner sum at one pair of label products -/

lemma norm_majorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖majorKernel x A₀ Y t a b‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (volume (majorArcs x A₀ Y)).toReal := by
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hfin : volume (majorArcs x A₀ Y) < ⊤ :=
    (measure_mono (majorArcs_subset x A₀ Y)).trans_lt (by simp)
  have hint : ‖∫ θ in majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
      1 * volume.real (majorArcs x A₀ Y) := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun θ _ => ?_
    rw [Complex.norm_exp]
    simp
  rw [one_mul] at hint
  exact mul_le_mul (abs_arcCutoff_le _) hint (norm_nonneg _) (by split_ifs <;> norm_num)

/-- `∑_{k,l ≤ N} τ(k)τ(l) 1_{|bk − al| < 5Y} ≤ 10 ∑_{k ≤ N} τ(k)²` for `Y < a, b`. -/
lemma sum_tau_window_le (N a b : ℕ) (Y : ℝ) (hY : 0 < Y) (ha : Y < a) (hb : Y < b) :
    ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) * ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) *
      (if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0) ≤
      10 * ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) ^ 2 := by
  set W : ℕ → ℕ → ℝ := fun k l => if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0
  have hW0 : ∀ k l, 0 ≤ W k l := fun k l => by simp only [W]; split_ifs <;> norm_num
  have hWiff : ∀ k l : ℕ, |((b : ℝ) * k - a * l) / Y| < 5 ↔ |(b : ℝ) * k - a * l| < 5 * Y := by
    intro k l; rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY]
  have hrow : ∀ k, ∑ l ∈ Ioc 0 N, W k l ≤ 10 := by
    intro k
    simp only [W]
    rw [sum_boole]
    have := card_window_le (Ioc 0 N) a Y (b * k) hY ha
    have heq : ((Ioc 0 N).filter fun l : ℕ => |((b : ℝ) * k - a * l) / Y| < 5) =
        (Ioc 0 N).filter fun l : ℕ => |(b : ℝ) * k - a * (l : ℝ)| < 5 * Y := by
      ext l; simp only [mem_filter, hWiff]
    rw [heq]; exact_mod_cast this
  have hcol : ∀ l, ∑ k ∈ Ioc 0 N, W k l ≤ 10 := by
    intro l
    simp only [W]
    rw [sum_boole]
    have := card_window_le (Ioc 0 N) b Y (a * l) hY hb
    have heq : ((Ioc 0 N).filter fun k : ℕ => |((b : ℝ) * k - a * l) / Y| < 5) =
        (Ioc 0 N).filter fun k : ℕ => |(a : ℝ) * l - b * (k : ℝ)| < 5 * Y := by
      ext k; simp only [mem_filter, hWiff, abs_sub_comm]
    rw [heq]; exact_mod_cast this
  set τ : ℕ → ℝ := fun k => (k.divisors.card : ℝ)
  have hpt : ∀ k l, τ k * (τ l * W k l) ≤ (τ k ^ 2 * W k l + τ l ^ 2 * W k l) / 2 := by
    intro k l
    have := hW0 k l
    nlinarith [sq_nonneg (τ k - τ l), mul_nonneg this (sq_nonneg (τ k - τ l))]
  calc ∑ k ∈ Ioc 0 N, τ k * ∑ l ∈ Ioc 0 N, τ l * W k l
      = ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ k * (τ l * W k l) := by simp only [mul_sum]
    _ ≤ ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, (τ k ^ 2 * W k l + τ l ^ 2 * W k l) / 2 :=
        sum_le_sum fun k _ => sum_le_sum fun l _ => hpt k l
    _ = (∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ k ^ 2 * W k l +
          ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ l ^ 2 * W k l) / 2 := by
        simp only [add_div, sum_add_distrib, sum_div]
    _ = (∑ k ∈ Ioc 0 N, τ k ^ 2 * ∑ l ∈ Ioc 0 N, W k l +
          ∑ l ∈ Ioc 0 N, τ l ^ 2 * ∑ k ∈ Ioc 0 N, W k l) / 2 := by
        congr 2
        · simp only [mul_sum]
        · rw [sum_comm]; simp only [mul_sum]
    _ ≤ (∑ k ∈ Ioc 0 N, τ k ^ 2 * 10 + ∑ l ∈ Ioc 0 N, τ l ^ 2 * 10) / 2 := by
        gcongr with k _ l _
        · exact hrow k
        · exact hcol l
    _ = 10 * ∑ k ∈ Ioc 0 N, τ k ^ 2 := by
        rw [← sum_mul, mul_comm]; ring

/-- **The major inner sum** at label products `Y < a, b`:
`‖majInner‖ ≤ |η η| B⁴ vol(𝔐) · 10 N (1 + log N)³`, `N = ⌊2H_m⌋ ⌊2H_n⌋` ((4.61)). -/
lemma norm_majInner_le (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) (hY : 0 < Y)
    (a b : ℕ) (ha : Y < a) (hb : Y < b) :
    ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      (volume (majorArcs x A₀ Y)).toReal *
        (10 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) *
          (1 + log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ^ 3) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  set N := ⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊
  set E := |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4
  set μ := (volume (majorArcs x A₀ Y)).toReal
  have hE : 0 ≤ E := by positivity
  have hμ : 0 ≤ μ := ENNReal.toReal_nonneg
  set R1 := range (⌊2 * Hm⌋₊ + 1)
  set R2 := range (⌊2 * Hn⌋₊ + 1)
  set W : ℕ → ℕ → ℝ := fun k l => if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0
  have hW0 : ∀ k l, 0 ≤ W k l := fun k l => by simp only [W]; split_ifs <;> norm_num
  set χ : ℕ → ℝ := fun m => if m ≠ 0 then 1 else 0
  -- pointwise
  have hpt : ∀ m n r s, ‖sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b‖
      ≤ E * μ * (χ m * (χ n * (χ r * (χ s * W (m * n) (r * s))))) := by
    intro m n r s
    rw [norm_mul]
    have h1 := norm_sqWeight_le Y a b m n r s α β B hα0 hβ0 hαB hβB
    have h2 := norm_majorKernel_le x A₀ Y (sqDet a b m n r s) a b
    have hdet : ((sqDet a b m n r s : ℤ) : ℝ) = (b : ℝ) * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ) := by
      unfold sqDet; push_cast; ring
    rw [hdet] at h2
    have hχ : 0 ≤ χ m * χ n * χ r * χ s := by simp only [χ]; split_ifs <;> norm_num
    calc _ ≤ (E * (χ m * χ n * χ r * χ s)) * (W (m * n) (r * s) * μ) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hE hχ)
      _ = _ := by ring
  have hstep1 : ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ E * μ *
      ∑ m ∈ R1, χ m * ∑ n ∈ R2, χ n * ∑ r ∈ R1, χ r * ∑ s ∈ R2, χ s * W (m * n) (r * s) := by
    unfold majInner
    simp only [mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
    exact hpt m n r s
  -- restrict to nonzero variables
  set A := R1.filter (· ≠ 0)
  set B' := R2.filter (· ≠ 0)
  have hχsum : ∀ (S : Finset ℕ) (F : ℕ → ℝ), ∑ m ∈ S, χ m * F m = ∑ m ∈ S.filter (· ≠ 0), F m := by
    intro S F
    rw [sum_filter]
    refine sum_congr rfl fun m _ => ?_
    simp only [χ]; split_ifs <;> simp
  have hstep2 : ∑ m ∈ R1, χ m * ∑ n ∈ R2, χ n * ∑ r ∈ R1, χ r * ∑ s ∈ R2, χ s * W (m * n) (r * s)
      = ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) := by
    rw [hχsum]
    refine sum_congr rfl fun m _ => ?_
    rw [hχsum]
    refine sum_congr rfl fun n _ => ?_
    rw [hχsum]
    refine sum_congr rfl fun r _ => ?_
    rw [hχsum]
  have hApos : ∀ m ∈ A, 0 < m := fun m hm => Nat.pos_of_ne_zero (mem_filter.1 hm).2
  have hBpos : ∀ n ∈ B', 0 < n := fun n hn => Nat.pos_of_ne_zero (mem_filter.1 hn).2
  have hAB : ∀ m ∈ A, ∀ n ∈ B', m * n ≤ N := by
    intro m hm n hn
    exact Nat.mul_le_mul (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hm).1))
      (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hn).1))
  have hstep3 : ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) ≤
      ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) *
        ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W k l := by
    calc ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s)
        ≤ ∑ m ∈ A, ∑ n ∈ B', ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W (m * n) l :=
          sum_le_sum fun m _ => sum_le_sum fun n _ =>
            sum_prod_le_sum_tau A B' N (W (m * n)) (hW0 _) hApos hBpos hAB
      _ ≤ _ := sum_prod_le_sum_tau A B' N
          (fun k => ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W k l)
          (fun k => sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (hW0 _ _))
          hApos hBpos hAB
  have hstep4 := sum_tau_window_le N a b Y hY ha hb
  have hstep5 := ArtinBV.sum_card_divisors_sq_le N
  calc ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ _ := hstep1
    _ = E * μ * ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) := by rw [hstep2]
    _ ≤ E * μ * (10 * ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hstep3.trans hstep4) (mul_nonneg hE hμ)
    _ ≤ E * μ * (10 * ((N : ℝ) * (1 + log N) ^ 3)) := by gcongr
    _ = _ := by ring

/-! ## The mass of label pairs with a common prime -/

/-- The harmonic weight `∏ᵢ 1/(pᵢ Vᵢ)` of a label tuple. -/
noncomputable def labelWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) : ℝ :=
  ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i))

lemma groupReciprocalSum_nonneg (x b : ℝ) : 0 ≤ groupReciprocalSum x b :=
  sum_nonneg fun p _ => by positivity

lemma labelWeight_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) :
    0 ≤ labelWeight x a p :=
  prod_nonneg fun i _ => by have := groupReciprocalSum_nonneg x (a i); positivity

lemma sum_inv_mul_groupReciprocalSum_le (x b : ℝ) :
    ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) ≤ 1 := by
  have hV : groupReciprocalSum x b = ∑ q ∈ primeGroup x b, 1 / (q : ℝ) := rfl
  rw [show ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) =
      (∑ q ∈ primeGroup x b, 1 / (q : ℝ)) / groupReciprocalSum x b by
    rw [sum_div]; exact sum_congr rfl fun q _ => by rw [div_div], ← hV]
  exact div_self_le_one _

lemma sum_labelWeight_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∑ p ∈ labelTuples x a, labelWeight x a p ≤ 1 := by
  unfold labelTuples labelWeight
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i))
    (fun i (q : ℕ) => 1 / ((q : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_le_one (fun i _ => sum_nonneg fun q _ => ?_) fun i _ =>
    sum_inv_mul_groupReciprocalSum_le x (a i)
  have := groupReciprocalSum_nonneg x (a i); positivity

/-- The `j`-marginal of the harmonic weight: `∑_{p : p_j = q} w(p) ≤ 1/(q V_j)`. -/
lemma sum_labelWeight_eq_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (j : Fin K) (q : ℕ) :
    ∑ p ∈ labelTuples x a, labelWeight x a p * (if p j = q then 1 else 0) ≤
      1 / ((q : ℝ) * groupReciprocalSum x (a j)) := by
  classical
  set g : (i : Fin K) → ℕ → ℝ := fun i y =>
    1 / ((y : ℝ) * groupReciprocalSum x (a i)) * (if i = j then (if y = q then 1 else 0) else 1)
  have hrw : ∀ p : Fin K → ℕ, labelWeight x a p * (if p j = q then 1 else 0) = ∏ i, g i (p i) := by
    intro p
    simp only [g, labelWeight, prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ j (fun i => if p i = q then (1 : ℝ) else 0)]
    simp
  simp only [hrw]
  unfold labelTuples
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i)) g]
  have hV := fun i => groupReciprocalSum_nonneg x (a i)
  calc ∏ i, ∑ y ∈ primeGroup x (a i), g i y
      ≤ ∏ i, (if i = j then 1 / ((q : ℝ) * groupReciprocalSum x (a j)) else 1) := by
        refine prod_le_prod (fun i _ => sum_nonneg fun y _ => ?_) fun i _ => ?_
        · simp only [g]; have := hV i; split_ifs <;> positivity
        · by_cases hij : i = j
          · subst hij
            simp only [g, if_true]
            calc ∑ y ∈ primeGroup x (a i), 1 / ((y : ℝ) * groupReciprocalSum x (a i)) *
                  (if y = q then 1 else 0)
                ≤ ∑ y ∈ primeGroup x (a i), (if y = q then
                    1 / ((q : ℝ) * groupReciprocalSum x (a i)) else 0) :=
                  sum_le_sum fun y _ => by split_ifs with h <;> simp [h]
              _ ≤ 1 / ((q : ℝ) * groupReciprocalSum x (a i)) := by
                  rw [sum_ite_eq']; split_ifs <;> [rfl; (have := hV i; positivity)]
          · simp only [g, hij, if_false, mul_one]
            exact sum_inv_mul_groupReciprocalSum_le x (a i)
    _ = _ := by rw [Finset.prod_ite_eq']; simp

/-- Label products with a common prime share a label. -/
lemma exists_eq_of_not_coprime {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p p' : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) (hp' : p' ∈ labelTuples x a)
    (h : ¬ Nat.Coprime (∏ i, p i) (∏ i, p' i)) : ∃ i j, p i = p' j := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
  have hpr : ∀ (r : Fin K → ℕ), r ∈ labelTuples x a → ∀ i, (r i).Prime := by
    intro r hr i
    have := (Fintype.mem_piFinset.1 hr) i
    unfold primeGroup at this
    exact (mem_filter.1 this).2.1
  obtain ⟨i, -, hi⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h1
  obtain ⟨j, -, hj⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h2
  exact ⟨i, j, ((Nat.prime_dvd_prime_iff_eq hq (hpr p hp i)).1 hi).symm.trans
    ((Nat.prime_dvd_prime_iff_eq hq (hpr p' hp' j)).1 hj)⟩

lemma abs_dyadicBump_le_div (u : ℕ) (Y : ℝ) (hY : 0 < Y) (hu : 0 < u) :
    |dyadicBump (u / Y)| ≤ 4 * Y / u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases h : dyadicBump (u / Y) = 0
  · rw [h, abs_zero]; positivity
  · have := (dyadicBump_ne_zero h).2
    rw [div_lt_iff₀ hY] at this
    rw [le_div_iff₀ hu']
    have := mul_le_of_le_one_left hu'.le (abs_dyadicBump_le_one (u / Y))
    linarith

/-- **The shared-label mass.** If all `Vⱼ ≥ 1/2` and all group primes are `≥ P`, then
`∏Vᵢ⁻² ∑_{(a,b) > 1} |η(a/Y) η(b/Y)| ≤ 32 K² Y²/P`. -/
lemma shared_mass_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y P : ℝ) (hY : 0 < Y) (hP : 0 < P)
    (hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j))
    (hPp : ∀ i, ∀ q ∈ primeGroup x (a i), P ≤ q) :
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      32 * K ^ 2 * Y ^ 2 / P := by
  classical
  have hVpos : ∀ j, 0 < groupReciprocalSum x (a j) := fun j => by linarith [hV j]
  have hpos : ∀ r ∈ labelTuples x a, ∀ i, 0 < r i := by
    intro r hr i
    exact pos_of_mem_primeGroup ((Fintype.mem_piFinset.1 hr) i)
  -- pointwise: `sqN |η η| ≤ 16 Y² w(p) w(p')`
  have hpt : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| ≤
        16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p') := by
    intro p hp p' hp'
    have ha : 0 < ∏ i, p i := prod_pos fun i _ => hpos p hp i
    have hb : 0 < ∏ i, p' i := prod_pos fun i _ => hpos p' hp' i
    have h1 := abs_dyadicBump_le_div _ Y hY ha
    have h2 := abs_dyadicBump_le_div _ Y hY hb
    have hsq : 0 ≤ squareNorm x a := prod_nonneg fun i _ => by positivity
    rw [abs_mul]
    calc squareNorm x a * (|dyadicBump ((∏ i, p i : ℕ) / Y)| *
          |dyadicBump ((∏ i, p' i : ℕ) / Y)|)
        ≤ squareNorm x a * ((4 * Y / (∏ i, p i : ℕ)) * (4 * Y / (∏ i, p' i : ℕ))) := by
          gcongr
      _ = 16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p') := by
          have hpi : ∀ i, (p i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos p hp i).ne'
          have hpi' : ∀ i, (p' i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos p' hp' i).ne'
          have hVi : ∀ i, groupReciprocalSum x (a i) ≠ 0 := fun i => (hVpos i).ne'
          have hPi : (∏ i, (p i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hpi i
          have hPi' : (∏ i, (p' i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hpi' i
          have h_aux : ∏ i, (groupReciprocalSum x (a i))⁻¹ ^ 2 =
              labelWeight x a p * labelWeight x a p' * ((∏ i, (p i : ℝ)) * ∏ i, (p' i : ℝ)) := by
            unfold labelWeight
            rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
            refine prod_congr rfl fun i _ => ?_
            have := hpi i; have := hpi' i; have := hVi i
            field_simp
          unfold squareNorm
          push_cast
          rw [h_aux]
          field_simp
          ring
  -- `[¬cop] ≤ ∑_{i,j} [p i = p' j]`
  have hind : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then (0 : ℝ) else 1) ≤
        ∑ i, ∑ j, (if p' j = p i then (1 : ℝ) else 0) := by
    intro p hp p' hp'
    split_ifs with hc
    · exact sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> norm_num
    · obtain ⟨i, j, hij⟩ := exists_eq_of_not_coprime hp hp' hc
      calc (1 : ℝ) = if p' j = p i then 1 else 0 := by rw [if_pos hij.symm]
        _ ≤ ∑ j', (if p' j' = p i then (1 : ℝ) else 0) :=
            single_le_sum (f := fun j' => if p' j' = p i then (1 : ℝ) else 0)
              (fun j' _ => by split_ifs <;> norm_num) (mem_univ j)
        _ ≤ ∑ i', ∑ j', (if p' j' = p i' then (1 : ℝ) else 0) :=
            single_le_sum (f := fun i' => ∑ j', (if p' j' = p i' then (1 : ℝ) else 0))
              (fun i' _ => sum_nonneg fun j' _ => by split_ifs <;> norm_num) (mem_univ i)
  have hstep : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      16 * Y ^ 2 * (labelWeight x a p * ∑ i, ∑ j,
        (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)) := by
    intro p hp p' hp'
    have hw := labelWeight_nonneg x a p
    have hw' := labelWeight_nonneg x a p'
    have e : (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) =
        (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then (0 : ℝ) else 1) *
        (squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) := by
      split_ifs <;> simp
    rw [e]
    have hsq : 0 ≤ squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) *
        dyadicBump ((∏ i, p' i : ℕ) / Y)| :=
      mul_nonneg (prod_nonneg fun i _ => by positivity) (abs_nonneg _)
    have hind0 : (0 : ℝ) ≤ if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else 1 := by
      split_ifs <;> norm_num
    calc _ ≤ (∑ i, ∑ j, (if p' j = p i then (1 : ℝ) else 0)) *
          (16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p')) :=
          mul_le_mul (hind p hp p' hp') (hpt p hp p' hp') hsq
            (sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> norm_num)
      _ = _ := by simp only [sum_mul, mul_sum]; refine sum_congr rfl fun i _ =>
            sum_congr rfl fun j _ => by ring
  refine (sum_le_sum fun p hp => sum_le_sum fun p' hp' => hstep p hp p' hp').trans ?_
  -- sum over `p'` with the marginal bound, then over `p`
  have hmarg : ∀ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a, 16 * Y ^ 2 *
      (labelWeight x a p * ∑ i, ∑ j, (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)) ≤
      16 * Y ^ 2 * (labelWeight x a p * (K ^ 2 * (2 / P))) := by
    intro p hp
    rw [← mul_sum, ← mul_sum]
    gcongr
    · exact labelWeight_nonneg x a p
    rw [sum_comm]
    calc ∑ i, ∑ p' ∈ labelTuples x a, ∑ j, (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)
        = ∑ i, ∑ j, ∑ p' ∈ labelTuples x a,
            (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0) :=
          sum_congr rfl fun i _ => sum_comm
      _ ≤ ∑ _i : Fin K, ∑ _j : Fin K, 2 / P := by
          refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
          refine (sum_labelWeight_eq_le x a j (p i)).trans ?_
          have hq : P ≤ (p i : ℝ) := hPp i _ ((Fintype.mem_piFinset.1 hp) i)
          have hVj := hV j
          have hpi0 : (0 : ℝ) < p i := by exact_mod_cast hpos p hp i
          rw [div_le_div_iff₀ (mul_pos hpi0 (hVpos j)) hP]
          nlinarith
      _ = K ^ 2 * (2 / P) := by
          rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
  refine (sum_le_sum hmarg).trans ?_
  rw [← mul_sum, ← sum_mul]
  have hsum := sum_labelWeight_le_one x a
  have h0 : (0 : ℝ) ≤ K ^ 2 * (2 / P) := by positivity
  calc 16 * Y ^ 2 * ((∑ p ∈ labelTuples x a, labelWeight x a p) * (K ^ 2 * (2 / P)))
      ≤ 16 * Y ^ 2 * (1 * (K ^ 2 * (2 / P))) := by gcongr
    _ = 32 * K ^ 2 * Y ^ 2 / P := by ring

/-! ## Inputs about the groups for large `x` -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

lemma prod_le_of_mem_labelTuples {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) : ((∏ i, p i : ℕ) : ℝ) ≤ ∏ i, exp (2 * log x ^ a i) := by
  push_cast
  exact prod_le_prod (fun i _ => Nat.cast_nonneg _)
    fun i _ => (le_of_mem_primeGroup ((Fintype.mem_piFinset.1 hp) i)).2

lemma dyadicBump_eq_zero_of_le_one {u : ℝ} (hu : u ≤ 1) : dyadicBump u = 0 := by
  by_contra h
  linarith [(dyadicBump_ne_zero h).1]

lemma rawInner_eq_zero (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ)
    (h : dyadicBump (a / Y) * dyadicBump (b / Y) = 0) : rawInner Y Hm Hn α β a b = 0 := by
  unfold rawInner sqWeight
  rcases mul_eq_zero.1 h with h | h <;> simp [h]

lemma majInner_eq_zero (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ)
    (h : dyadicBump (a / Y) * dyadicBump (b / Y) = 0) : majInner x A₀ Y Hm Hn α β a b = 0 := by
  unfold majInner sqWeight
  rcases mul_eq_zero.1 h with h | h <;> simp [h]

/-- Bounding `Q^sh`-type sums by the shared mass times a uniform bound for the inner sums. -/
lemma norm_shared_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y : ℝ) (F : ℕ → ℕ → ℂ) (M₀ : ℝ)
    (hF : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a, ‖F (∏ i, p i) (∏ i, p' i)‖ ≤
      |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| * M₀) :
    ‖(squareNorm x a : ℂ) * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else F (∏ i, p i) (∏ i, p' i))‖ ≤
      (∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
          squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) *
            dyadicBump ((∏ i, p' i : ℕ) / Y)|)) * M₀ := by
  have hsq : 0 ≤ squareNorm x a := prod_nonneg fun i _ => by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq]
  calc squareNorm x a * ‖∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else F (∏ i, p i) (∏ i, p' i))‖
      ≤ squareNorm x a * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        ‖(if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else F (∏ i, p i) (∏ i, p' i))‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (sum_le_sum fun p _ => norm_sum_le _ _)) hsq
    _ ≤ squareNorm x a * ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
        (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
          |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| * M₀) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun p hp => sum_le_sum fun p' hp' => ?_) hsq
        split_ifs
        · simp
        · exact hF p hp p' hp'
    _ = _ := by
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun p' _ => ?_
        split_ifs <;> ring

/-! ## Numerics -/

lemma rpow_combine {L : ℝ} (hL : 0 < L) (D : ℝ) (hD : 0 < D) (s t : ℝ)
    (h : log D + s * log L ≤ t) : D * L ^ s ≤ exp t := by
  rw [Real.rpow_def_of_pos hL, ← exp_log hD, ← exp_add]
  exact exp_le_exp.2 (by linarith)

lemma numeric_raw (K : ℕ) (hK : 1 ≤ K) (L X Y C A Z T : ℝ) (hL : 1 ≤ L) (hX : 0 < X)
    (hY : 0 < Y) (_hZ : 0 ≤ Z) (hZX : Z ≤ 4 * X / Y) (_hT0 : 0 ≤ T) (hTX : T ≤ X / Y)
    (hlogT : 0 ≤ 1 + log T) (hlogT2 : 1 + log T ≤ 2 * L)
    (hE : log (5120 * K ^ 2) + (4 * C + 3 + A) * log L ≤ L ^ (0.1 : ℝ)) :
    32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
      (4 * (Z + T) * (1 + log T) ^ 3)) ≤ 1 * (X * Y * L ^ (-A)) := by
  have hL0 : 0 < L := by linarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hZT : Z + T ≤ 5 * X / Y := by
    have : 4 * X / Y + X / Y = 5 * X / Y := by ring
    linarith
  have h3 : (1 + log T) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hlogT hlogT2 3
  have hcomb := rpow_combine hL0 (5120 * K ^ 2) (by positivity) (4 * C + 3 + A) _ hE
  have hpow : (L ^ C) ^ 4 * L ^ 3 * L ^ A = L ^ (4 * C + 3 + A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 3,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num; ring_nf
  have hLA : L ^ (-A) * L ^ A = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have hLAp : 0 < L ^ A := by positivity
  have hP : 0 < exp (L ^ (0.1 : ℝ)) := exp_pos _
  have hLC : 0 ≤ (L ^ C) ^ 4 := by positivity
  calc 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
        (4 * (Z + T) * (1 + log T) ^ 3))
      ≤ 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
        (4 * (5 * X / Y) * (2 * L) ^ 3)) := by gcongr
    _ = (5120 * K ^ 2 * ((L ^ C) ^ 4 * L ^ 3 * L ^ A)) / exp (L ^ (0.1 : ℝ)) *
          (X * Y * L ^ (-A)) := by
        field_simp
        rw [show L ^ (-A) = (L ^ A)⁻¹ by rw [Real.rpow_neg hL0.le]]
        field_simp
        ring
    _ ≤ 1 * (X * Y * L ^ (-A)) := by
        gcongr
        rw [div_le_one hP, hpow]
        exact hcomb

lemma numeric_major (K : ℕ) (hK : 1 ≤ K) (L X Y C A A₀ μ N : ℝ) (hL : 1 ≤ L) (hX : 0 < X)
    (hY : 0 < Y) (_hμ0 : 0 ≤ μ) (hμ : μ ≤ 4 * L ^ (3 * A₀) / Y) (hN0 : 0 ≤ N) (hN : N ≤ 4 * X)
    (hlogN : 0 ≤ 1 + log N) (hlogN2 : 1 + log N ≤ 2 * L)
    (hE : log (40960 * K ^ 2) + (4 * C + 3 * A₀ + 3 + A) * log L ≤ L ^ (0.1 : ℝ)) :
    32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * μ *
      (10 * N * (1 + log N) ^ 3)) ≤ 1 * (X * Y * L ^ (-A)) := by
  have hL0 : 0 < L := by linarith
  have h3 : (1 + log N) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hlogN hlogN2 3
  have hcomb := rpow_combine hL0 (40960 * K ^ 2) (by positivity) (4 * C + 3 * A₀ + 3 + A) _ hE
  have hpow : (L ^ C) ^ 4 * L ^ (3 * A₀) * L ^ 3 * L ^ A = L ^ (4 * C + 3 * A₀ + 3 + A) := by
    rw [← Real.rpow_natCast (L ^ C), ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 3,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num; ring_nf
  have hP : 0 < exp (L ^ (0.1 : ℝ)) := exp_pos _
  have hLAp : 0 < L ^ A := by positivity
  calc 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * μ *
        (10 * N * (1 + log N) ^ 3))
      ≤ 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * (4 * L ^ (3 * A₀) / Y) *
        (10 * (4 * X) * (2 * L) ^ 3)) := by gcongr
    _ = (40960 * K ^ 2 * ((L ^ C) ^ 4 * L ^ (3 * A₀) * L ^ 3 * L ^ A)) /
          exp (L ^ (0.1 : ℝ)) * (X * Y * L ^ (-A)) := by
        field_simp
        rw [show L ^ (-A) = (L ^ A)⁻¹ by rw [Real.rpow_neg hL0.le]]
        field_simp
        ring
    _ ≤ 1 * (X * Y * L ^ (-A)) := by
        gcongr
        rw [div_le_one hP, hpow]
        exact hcomb


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x

lemma SharedSetting.mass {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {Y Hm Hn : ℝ} {α β : ℕ → ℂ} {C : ℝ}
    (S : SharedSetting x a Y Hm Hn α β C) :
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      32 * K ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) := by
  refine shared_mass_le x a Y _ (by linarith [S.hY]) (exp_pos _) S.hV fun i q hq => ?_
  refine le_trans (exp_le_exp.2 ?_) (le_of_mem_primeGroup hq).1
  exact Real.rpow_le_rpow_of_exponent_le S.hL1 (S.hab i).le

/-- The raw half of D1b, given `(17X)^{3/4} Y ≤ X` and the logarithmic budget. -/
lemma shared_raw_le {x : ℝ} {K : ℕ} (hK : 1 ≤ K) {a : Fin K → ℝ} {Y Hm Hn : ℝ}
    {α β : ℕ → ℂ} {C : ℝ} (A : ℝ) (S : SharedSetting x a Y Hm Hn α β C)
    (hTY : (17 * (Hm * Hn)) ^ (3 / 4 : ℝ) * Y ≤ Hm * Hn)
    (hc5 : log (5120 * K ^ 2) + (4 * C + 3 + A) * log (log x) ≤ log x ^ (0.1 : ℝ)) :
    ‖sharedSquare x a Y Hm Hn α β‖ ≤ 1 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hY0 : 0 < Y := by linarith [S.hY]
  have hX0 : 0 < Hm * Hn := mul_pos S.hHm S.hHn
  have hZ : (⌊4 * Hm * Hn / Y⌋₊ : ℝ) ≤ 4 * (Hm * Hn) / Y := by
    have := Nat.floor_le (show 0 ≤ 4 * Hm * Hn / Y by have := S.hHm; have := S.hHn; positivity)
    rw [show 4 * (Hm * Hn) / Y = 4 * Hm * Hn / Y by ring]; exact this
  have hT17 : ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (17 * (Hm * Hn)) ^ (3 / 4 : ℝ) :=
    Nat.floor_le (by positivity)
  have hTgen : ∀ a' : ℕ, (a' : ℝ) < 4 * Y → ∀ m : ℕ,
      m ^ 4 ≤ (1 + a' * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ := by
    intro a' ha' m hm
    apply Nat.le_floor
    have h1aZ : ((1 + a' * ⌊4 * Hm * Hn / Y⌋₊ : ℕ) : ℝ) ≤ 17 * (Hm * Hn) := by
      push_cast
      have : (a' : ℝ) * ⌊4 * Hm * Hn / Y⌋₊ ≤ 4 * Y * (4 * (Hm * Hn) / Y) :=
        mul_le_mul ha'.le hZ (Nat.cast_nonneg _) (by positivity)
      have e : 4 * Y * (4 * (Hm * Hn) / Y) = 16 * (Hm * Hn) := by field_simp; ring
      linarith [S.hX1]
    have hm' : ((m : ℝ) ^ 4) ≤ (17 * (Hm * Hn)) ^ 3 := by
      have : ((m ^ 4 : ℕ) : ℝ) ≤ (((1 + a' * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast hm
      rw [Nat.cast_pow, Nat.cast_pow] at this
      exact this.trans (pow_le_pow_left₀ (by positivity) h1aZ 3)
    have := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast (17 * (Hm * Hn)), ← Real.rpow_mul (by positivity)] at this
    norm_num at this
    exact this
  have hraw : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      ‖rawInner Y Hm Hn α β (∏ i, p i) (∏ i, p' i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| *
          ((log x ^ C) ^ 4 * (4 * ((⌊4 * Hm * Hn / Y⌋₊ : ℝ) +
            (⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ)) *
            (1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ)) ^ 3)) := by
    intro p hp p' hp'
    by_cases hη : dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) = 0
    · rw [rawInner_eq_zero Y Hm Hn α β _ _ hη, hη]; simp
    · obtain ⟨hηa, hηb⟩ := mul_ne_zero_iff.1 hη
      obtain ⟨ha1, ha4⟩ := dyadicBump_ne_zero hηa
      obtain ⟨hb1, hb4⟩ := dyadicBump_ne_zero hηb
      rw [one_lt_div hY0] at ha1 hb1
      rw [div_lt_iff₀ hY0] at ha4 hb4
      have := norm_rawInner_le Y Hm Hn α β (log x ^ C) S.hα0 S.hβ0 S.hαb S.hβb S.hHm.le
        S.hHn.le hY0 (∏ i, p i) (∏ i, p' i) ha1 hb1 _ (hTgen _ (by linarith))
        (hTgen _ (by linarith))
      calc _ ≤ _ := this
        _ = _ := by ring
  refine (norm_shared_le x a Y (rawInner Y Hm Hn α β) _ hraw).trans ?_
  have hlog17pos : 0 ≤ log (17 * (Hm * Hn)) := log_nonneg (by linarith [S.hX1])
  have hlogT : 0 ≤ 1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊; linarith
  have hlogT2 : 1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ 2 * log x := by
    rcases Nat.eq_zero_or_pos ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ with hT0 | hT0
    · rw [hT0]; simp only [Nat.cast_zero, log_zero]; linarith [S.hL1]
    · have hTr : (0 : ℝ) < (⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) := by exact_mod_cast hT0
      have : log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ log (17 * (Hm * Hn)) := by
        calc _ ≤ log ((17 * (Hm * Hn)) ^ (3 / 4 : ℝ)) := log_le_log hTr hT17
          _ = 3 / 4 * log (17 * (Hm * Hn)) := Real.log_rpow (by positivity) _
          _ ≤ log (17 * (Hm * Hn)) := by nlinarith
      linarith [S.hlog]
  have hTX : ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Hm * Hn / Y := by
    rw [le_div_iff₀ hY0]
    exact (mul_le_mul_of_nonneg_right hT17 hY0.le).trans hTY
  calc _ ≤ 32 * K ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) * ((log x ^ C) ^ 4 *
        (4 * ((⌊4 * Hm * Hn / Y⌋₊ : ℝ) + (⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ)) *
          (1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ)) ^ 3)) :=
        mul_le_mul_of_nonneg_right S.mass (by positivity)
    _ ≤ 1 * (Hm * Hn * Y * log x ^ (-A)) :=
        numeric_raw K hK (log x) (Hm * Hn) Y C A _ _ S.hL1 hX0 hY0 (Nat.cast_nonneg _) hZ
          (Nat.cast_nonneg _) hTX hlogT hlogT2 hc5

/-- The major half of D1b. -/
lemma shared_major_le {x : ℝ} {K : ℕ} (hK : 1 ≤ K) {a : Fin K → ℝ} {Y Hm Hn : ℝ}
    {α β : ℕ → ℂ} {C : ℝ} (A₀ A : ℝ) (hA₀ : 0 ≤ A₀) (S : SharedSetting x a Y Hm Hn α β C)
    (hc6 : log (40960 * K ^ 2) + (4 * C + 3 * A₀ + 3 + A) * log (log x) ≤
      log x ^ (0.1 : ℝ)) :
    ‖sharedMajorSquare x a A₀ Y Hm Hn α β‖ ≤ 1 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hY0 : 0 < Y := by linarith [S.hY]
  have hX0 : 0 < Hm * Hn := mul_pos S.hHm S.hHn
  have hmaj : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      ‖majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, p' i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| *
          ((log x ^ C) ^ 4 * (volume (majorArcs x A₀ Y)).toReal *
            (10 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) *
              (1 + log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ^ 3)) := by
    intro p hp p' hp'
    by_cases hη : dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) = 0
    · rw [majInner_eq_zero x A₀ Y Hm Hn α β _ _ hη, hη]; simp
    · obtain ⟨hηa, hηb⟩ := mul_ne_zero_iff.1 hη
      have ha1 := (dyadicBump_ne_zero hηa).1
      have hb1 := (dyadicBump_ne_zero hηb).1
      rw [one_lt_div hY0] at ha1 hb1
      have := norm_majInner_le x A₀ Y Hm Hn α β (log x ^ C) S.hα0 S.hβ0 S.hαb S.hβb hY0
        (∏ i, p i) (∏ i, p' i) ha1 hb1
      calc _ ≤ _ := this
        _ = _ := by ring
  refine (norm_shared_le x a Y (majInner x A₀ Y Hm Hn α β) _ hmaj).trans ?_
  have hμ : (volume (majorArcs x A₀ Y)).toReal ≤ 4 * log x ^ (3 * A₀) / Y :=
    ENNReal.toReal_le_of_le_ofReal (by have := S.hL1; positivity)
      (volume_majorArcs_le x A₀ Y S.hL1 hA₀ hY0)
  have hN : (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ 4 * (Hm * Hn) := by
    push_cast
    have h1 : (⌊2 * Hm⌋₊ : ℝ) ≤ 2 * Hm := Nat.floor_le (by linarith [S.hHm])
    have h2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := Nat.floor_le (by linarith [S.hHn])
    calc (⌊2 * Hm⌋₊ : ℝ) * ⌊2 * Hn⌋₊ ≤ 2 * Hm * (2 * Hn) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith [S.hHm])
      _ = 4 * (Hm * Hn) := by ring
  have hlogN : 0 ≤ 1 + log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) := by
    have := Real.log_natCast_nonneg (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊); linarith
  have hlogN2 : 1 + log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ 2 * log x := by
    rcases Nat.eq_zero_or_pos (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊) with hN0 | hN0
    · rw [hN0]; simp only [Nat.cast_zero, log_zero]; linarith [S.hL1]
    · have hNr : (0 : ℝ) < ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN0
      have : log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ log (17 * (Hm * Hn)) :=
        log_le_log hNr (by linarith)
      linarith [S.hlog]
  calc _ ≤ 32 * K ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) * ((log x ^ C) ^ 4 *
        (volume (majorArcs x A₀ Y)).toReal *
          (10 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) *
            (1 + log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ^ 3)) :=
        mul_le_mul_of_nonneg_right S.mass (by positivity)
    _ ≤ 1 * (Hm * Hn * Y * log x ^ (-A)) :=
        numeric_major K hK (log x) (Hm * Hn) Y C A A₀ _ _ S.hL1 hX0 hY0 ENNReal.toReal_nonneg hμ
          (Nat.cast_nonneg _) hN hlogN hlogN2 hc6

/-- If `Y` exceeds every label product, both shared sums vanish. -/
lemma shared_eq_zero_of_large {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {Y : ℝ} (A₀ Hm Hn : ℝ)
    (α β : ℕ → ℂ) (hY : 0 < Y) (hYm : ∏ i, exp (2 * log x ^ a i) ≤ Y) :
    ‖sharedSquare x a Y Hm Hn α β‖ ≤ 0 ∧ ‖sharedMajorSquare x a A₀ Y Hm Hn α β‖ ≤ 0 := by
  have hz : ∀ p ∈ labelTuples x a, dyadicBump ((∏ i, p i : ℕ) / Y) = 0 := by
    intro p hp
    apply dyadicBump_eq_zero_of_le_one
    rw [div_le_one hY]
    exact (prod_le_of_mem_labelTuples hp).trans hYm
  constructor
  · have := norm_shared_le x a Y (rawInner Y Hm Hn α β) 0 (fun p hp p' _ => by
      rw [rawInner_eq_zero Y Hm Hn α β _ _ (by rw [hz p hp, zero_mul])]; simp)
    rwa [mul_zero] at this
  · have := norm_shared_le x a Y (majInner x A₀ Y Hm Hn α β) 0 (fun p hp p' _ => by
      rw [majInner_eq_zero x A₀ Y Hm Hn α β _ _ (by rw [hz p hp, zero_mul])]; simp)
    rwa [mul_zero] at this


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D1b, the shared-label bound (uses Mertens through the stub for `Vⱼ ≥ 1/2`) -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-- `Vⱼ ≥ 1/2` for large `x` (Mertens: `Vⱼ → log 2`). -/
lemma eventually_groupReciprocalSum_ge {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j) := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 : ℝ) / 2 < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have hev := hm.eventually (lt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  filter_upwards [hy.eventually hev] with x hx
  refine hx.le.trans ?_
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, Real.rpow_one] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.le⟩

/-- **D1b ([21] (3.9), (4.61), (4.63)).** The parts of `Q_Y` and `Q_Y^maj` over label pairs with
a common prime are `≤ H_m H_n Y L^{-A}` for large `x`, for every `A₀, A > 0`. This is exactly the
hypothesis `hsh` of `square_major_replacement_of_cuts`. -/
theorem shared_bound (δ C c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∀ A₀ A : ℝ, 0 < A₀ → 0 < A → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖sharedSquare x a Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) ∧
            ‖sharedMajorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A)) := by
  intro A₀ A hA₀ hA K hK a _ha hab
  have hapos : ∀ i, 0 < a i := fun i => (by norm_num : (0 : ℝ) < 0.1).trans (hab i).1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- eventual conditions on `L = log x`
  have hE2 : ∀ᶠ L : ℝ in Filter.atTop, 2 * K * L ^ (0.2 : ℝ) + log 17 - log c₁ / 4 ≤ L / 4 := by
    have e1 := eventually_rpow_le_rpow (b := 0.2) (c := 1) (by norm_num) (ε := 1 / (16 * K))
      (by positivity)
    have e2 := Filter.tendsto_id.eventually_ge_atTop (8 * (log 17 - log c₁ / 4))
    filter_upwards [e1, e2, Filter.eventually_gt_atTop 0] with L h1 h2 h3
    rw [Real.rpow_one] at h1
    have : 2 * K * L ^ (0.2 : ℝ) ≤ L / 8 := by
      calc 2 * K * L ^ (0.2 : ℝ) ≤ 2 * K * (1 / (16 * K) * L) := by gcongr
        _ = L / 8 := by field_simp; ring
    simp only [id] at h2
    linarith
  have hE3 : ∀ᶠ L : ℝ in Filter.atTop, 1 + log (17 * c₂) ≤ L ∧ 1 ≤ L ∧ log (1 / c₁) ≤ L := by
    filter_upwards [Filter.eventually_ge_atTop (1 + log (17 * c₂)), Filter.eventually_ge_atTop 1,
      Filter.eventually_ge_atTop (log (1 / c₁))] with L h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hE5 : ∀ᶠ L : ℝ in Filter.atTop,
      log (5120 * K ^ 2) + (4 * C + 3 + A) * log L ≤ L ^ (0.1 : ℝ) := by
    filter_upwards [eventually_log_le_rpow (a := 0.1) (by norm_num) (4 * C + 3 + A)
      (log (5120 * K ^ 2)) (ε := 1) one_pos] with L h
    linarith
  have hE6 : ∀ᶠ L : ℝ in Filter.atTop,
      log (40960 * K ^ 2) + (4 * C + 3 * A₀ + 3 + A) * log L ≤ L ^ (0.1 : ℝ) := by
    filter_upwards [eventually_log_le_rpow (a := 0.1) (by norm_num) (4 * C + 3 * A₀ + 3 + A)
      (log (40960 * K ^ 2)) (ε := 1) one_pos] with L h
    linarith
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (hE2.and (hE3.and (hE5.and hE6)))
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (eventually_groupReciprocalSum_ge a hapos)
  refine ⟨1, max x₁ (exp L₀), fun x Hm Hn hx hm hn h1 h2 α β hαs hβs hαb hβb Y hY => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos _) (le_of_max_le_right hx)
  have hLL : L₀ ≤ log x := (Real.le_log_iff_exp_le hxpos).2 (le_of_max_le_right hx)
  obtain ⟨hc2, ⟨hc3, hL1, hc7⟩, hc5, hc6⟩ := hL₀ (log x) hLL
  have hV := hx₁ x (le_of_max_le_left hx)
  have hY0 : 0 < Y := by linarith
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hm
  have hHn : 0 < Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hn
  have hX0 : 0 < Hm * Hn := mul_pos hHm hHn
  have hc₂ : 0 < c₂ := by
    by_contra h; push Not at h
    have : c₂ * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hxpos.le
    nlinarith
  have hcx : c₁ * x = exp (log c₁ + log x) := by
    rw [exp_add, exp_log hc₁, exp_log hxpos]
  have hX1 : 1 ≤ Hm * Hn := by
    have : 1 ≤ c₁ * x := by
      rw [hcx]; apply one_le_exp
      have : log (1 / c₁) = - log c₁ := by rw [one_div, log_inv]
      linarith
    linarith
  have hα0 : α 0 = 0 := by
    by_contra h
    obtain ⟨J, -, -, hJ⟩ := hαs
    exact absurd (hJ 0 h).2.1 (lt_irrefl 0)
  have hβ0 : β 0 = 0 := by
    by_contra h
    exact absurd (hβs 0 h).2.2.1 (lt_irrefl 0)
  have hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x := by
    have : log (17 * (Hm * Hn)) ≤ log (17 * c₂) + log x := by
      rw [← log_mul (by positivity) hxpos.ne']
      exact log_le_log (by positivity) (by nlinarith)
    linarith
  have S : SharedSetting x a Y Hm Hn α β C :=
    ⟨hL1, hxpos, hHm, hHn, hY, hX1, hα0, hβ0, hαb, hβb, hV, fun i => (hab i).1, hlog⟩
  have hRHS : 0 ≤ 1 * (Hm * Hn * Y * log x ^ (-A)) := by
    have : 0 < log x := by linarith
    positivity
  by_cases hYm : ∏ i, exp (2 * log x ^ a i) ≤ Y
  · obtain ⟨h1', h2'⟩ := shared_eq_zero_of_large A₀ Hm Hn α β hY0 hYm
    exact ⟨h1'.trans hRHS, h2'.trans hRHS⟩
  push Not at hYm
  refine ⟨shared_raw_le hK A S ?_ hc5, shared_major_le hK A₀ A hA₀.le S hc6⟩
  -- `(17X)^{3/4} Y ≤ X`
  have hYmax : ∏ i, exp (2 * log x ^ a i) ≤ exp (2 * K * log x ^ (0.2 : ℝ)) := by
    rw [← exp_sum]
    apply exp_le_exp.2
    calc ∑ i, 2 * log x ^ a i ≤ ∑ _i : Fin K, 2 * log x ^ (0.2 : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).2.le
          linarith
      _ = 2 * K * log x ^ (0.2 : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hX4 : Hm * Hn = (Hm * Hn) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have h17' : (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 := by
    calc (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 17 := Real.rpow_one 17
  have hXq : exp ((log c₁ + log x) / 4) ≤ (Hm * Hn) ^ (1 / 4 : ℝ) := by
    rw [show (log c₁ + log x) / 4 = log (c₁ * x) * (1 / 4) by
      rw [log_mul hc₁.ne' hxpos.ne']; ring, Real.exp_mul, exp_log (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hkey : (17 : ℝ) ^ (3 / 4 : ℝ) * Y ≤ (Hm * Hn) ^ (1 / 4 : ℝ) := by
    calc (17 : ℝ) ^ (3 / 4 : ℝ) * Y ≤ 17 * exp (2 * K * log x ^ (0.2 : ℝ)) :=
          mul_le_mul h17' (hYm.le.trans hYmax) hY0.le (by norm_num)
      _ = exp (log 17 + 2 * K * log x ^ (0.2 : ℝ)) := by rw [exp_add, exp_log (by norm_num)]
      _ ≤ exp ((log c₁ + log x) / 4) := exp_le_exp.2 (by linarith)
      _ ≤ _ := hXq
  rw [Real.mul_rpow (by norm_num) hX0.le]
  calc (17 : ℝ) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (3 / 4 : ℝ) * Y
      = (Hm * Hn) ^ (3 / 4 : ℝ) * ((17 : ℝ) ^ (3 / 4 : ℝ) * Y) := by ring
    _ ≤ (Hm * Hn) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Hm * Hn := hX4.symm

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: (10.9) from the coprime minor-arc bound alone

`square_major_replacement` follows from the bound for `minorSquare` (the coprime minor-arc part of
the expanded square; the content of [21] §§3.2–4.9), since the shared-label parts are bounded
unconditionally (`shared_bound`) and the difference is an exact identity
(`expandedSquare_sub_majorSquare`). -/

namespace ArtinPrimitiveRoots.L102D

open Real

/-- **(10.9) modulo D1c.** -/
theorem square_major_replacement_of_minor (δ C c₁ c₂ : ℝ) (_hδ : 0 < δ) (_hC : 0 < C)
    (hc₁ : 0 < c₁)
    (hmin : ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-A))) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖expandedSquare x a Y Hm Hn α β - majorSquare x a A₀ Y Hm Hn α β‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) :=
  square_major_replacement_of_cuts δ C c₁ c₂ (shared_bound δ C c₁ c₂ hc₁) hmin

end ArtinPrimitiveRoots.L102D
end

section
/-! # Check: (10.9) `square_major_replacement` from D1c `minor_square_bound` -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖expandedSquare x a Y Hm Hn α β - majorSquare x a A₀ Y Hm Hn α β‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) :=
  L102D.square_major_replacement_of_minor δ C c₁ c₂ hδ hC hc₁
    (minor_square_bound δ C c₁ c₂ hδ hC hc₁)
end
