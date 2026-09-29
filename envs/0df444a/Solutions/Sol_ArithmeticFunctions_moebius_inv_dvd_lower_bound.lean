-- Prove2me | solution 1 for ArithmeticFunctions.moebius_inv_dvd_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:51:45.785893+00:00
-- url     : https://prove2.me/submissions/bd955073-c98c-436c-8d61-f18b51874a2e

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Brun.SelbergPort =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude

The definitions and results in this file are adapted from Arend Mellendijk's
SelbergSieve project (https://github.com/amellendijk/selberg-sieve4,
`SelbergSieve/Selberg.lean`, Copyright (c) 2023 Arend Mellendijk, Apache 2.0),
whose sieve-foundation layer is already part of mathlib as
`Mathlib/NumberTheory/SelbergSieve.lean`.
-/

/-!
# Selberg weights (blueprint N1.1 — the M1 port layer)

The truncated optimal weights of the Selberg Λ² sieve, against mathlib's
`SelbergSieve` structure: the bounding sum `S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ)`
(positive, since `g > 0` on divisors of `P` and `ℓ = 1` qualifies), the
weights themselves, their support (`d ∣ P`, `d² ≤ y`), and `w 1 = 1`.

N1.2 (`|w d| ≤ 1`), N1.3 (`mainSum = 1/S`), and N1.4 (the fundamental
theorem) continue the port in later work; see the guide's R1/A1.
-/

open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

namespace Salt.SelbergPort

variable (s : SelbergSieve)

open Classical in
/-- The Selberg bounding sum `S = Σ_{ℓ ∣ P, ℓ² ≤ y} g(ℓ)` — the `G(√y)` of
the classical fundamental theorem (blueprint N1.3 convention). -/
noncomputable def selbergBoundingSum : ℝ :=
  ∑ l ∈ s.prodPrimes.divisors, if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0

theorem selbergBoundingSum_pos : 0 < selbergBoundingSum s := by
  rw [selbergBoundingSum, ← Finset.sum_filter]
  apply Finset.sum_pos
  · intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    exact BoundingSieve.selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, ?_⟩
    simpa using s.one_le_level

theorem selbergBoundingSum_ne_zero : selbergBoundingSum s ≠ 0 :=
  ne_of_gt (selbergBoundingSum_pos s)

open Classical in
/-- N1.1: the truncated optimal Selberg weights. Classically
`λ_d = μ(d) · (g-weighted partial sums) / S`; here in the arithmetic form of
the reference formalization. -/
noncomputable def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * ((μ d : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ *
      ∑ m ∈ s.prodPrimes.divisors,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬d ∣ s.prodPrimes) :
    selbergWeights s d = 0 := by
  rw [selbergWeights, if_neg hd]

/-- N1.1 (support): the weights vanish beyond the truncation `d² ≤ y`. -/
theorem selbergWeights_eq_zero {d : ℕ} (hd : ¬(d : ℝ) ^ 2 ≤ s.level) :
    selbergWeights s d = 0 := by
  rw [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    rintro ⟨hym, -⟩
    apply hd
    calc ((d : ℝ)) ^ 2 ≤ ((d * m : ℕ) : ℝ) ^ 2 := by
          have h1 : (d : ℝ) ≤ ((d * m : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_mul_of_pos_right d (Nat.pos_of_mem_divisors hm)
          have h0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith
      _ ≤ s.level := hym
  · rfl

/-- N1.1: `w 1 = 1` — the normalization the Λ² machinery requires
(`upperMoebius_lambdaSquared` consumes exactly this). -/
theorem selbergWeights_one : selbergWeights s 1 = 1 := by
  rw [selbergWeights, if_pos (one_dvd _)]
  rw [s.nu_mult.1, BoundingSieve.selbergTerms_isMultiplicative.1]
  simp only [inv_one, one_mul, moebius_apply_one, Int.cast_one]
  have hsum : (∑ m ∈ s.prodPrimes.divisors,
      if (m : ℝ) ^ 2 ≤ s.level ∧ m.Coprime 1 then s.selbergTerms m else 0)
      = selbergBoundingSum s := by
    rw [selbergBoundingSum]
    exact Finset.sum_congr rfl fun m _ => by simp
  rw [hsum, inv_mul_cancel₀ (selbergBoundingSum_ne_zero s)]

/-! ## Helper lemmas (Aux-layer of the reference) -/

/-- Restrict a sum over `n.divisors` to a sum over `P.divisors` with a divisibility guard. -/
theorem sum_over_dvd_ite {α} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 := by
  rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

/-- Introduce a single term as a guarded sum. -/
theorem sum_intro {M} [AddCommMonoid M] (t : Finset ℕ) {f : ℕ → M} (d : ℕ) (hd : d ∈ t) :
    f d = ∑ k ∈ t, if k = d then f k else 0 := by
  trans (∑ k ∈ t, if k = d then f d else 0)
  · rw [Finset.sum_eq_single_of_mem d hd]
    · rw [if_pos rfl]
    · intro _ _ h; rw [if_neg h]
  apply Finset.sum_congr rfl; intro k _
  apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h; rw [h]

/-- Möbius inversion identity: for `m` squarefree,
`∑_{d ∣ m} [l ∣ d] μ d = [l = m] μ l`. -/
theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) = if l = m then (μ l : ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm; revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • if l = y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, Finset.sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply Nat.coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw [Nat.mem_divisors] at h; exact absurd ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩ h
  · rw [if_neg hl, Finset.sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]; by_contra h; rw [← h] at hd; exact hl (Nat.dvd_of_mem_divisors hd)

/-- Real-valued form of `moebius_inv_dvd_lower_bound`, restricted to divisors of squarefree `P`. -/
theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0)
      = if l = m then (μ l : ℝ) else 0 := by
  have : (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℤ) else 0)
      = if l = m then (μ l : ℤ) else 0 := by
    rw [← moebius_inv_dvd_lower_bound l m (hP.squarefree_of_dvd hm), sum_over_dvd_ite hP.ne_zero hm]
    simp_rw [ite_and, ← Finset.sum_filter, Finset.filter_comm]
  exact_mod_cast this

/-- A multiplicative function respects division by a coprime cofactor on squarefree numbers. -/
theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : f.IsMultiplicative)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply Nat.coprime_of_squarefree_mul; convert hl using 1; exact Nat.div_mul_cancel hdl

/-! ## The Selberg weight identities (reference lines 94-275) -/

/-- `w d · μ d ≥ 0` for `d ∣ P`: the sign of `μ d` cancels against the `μ d` in `w d`. -/
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ selbergWeights s d * ((μ d : ℤ) : ℝ) := by
  rw [selbergWeights, if_pos hdP]
  have hmm : (s.nu d)⁻¹ * s.selbergTerms d * ((μ d : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ *
        (∑ m ∈ s.prodPrimes.divisors,
          if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) *
        ((μ d : ℤ) : ℝ)
      = ((μ d : ℤ) : ℝ) ^ 2 * ((s.nu d)⁻¹ * s.selbergTerms d * (selbergBoundingSum s)⁻¹ *
          (∑ m ∈ s.prodPrimes.divisors,
            if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0)) := by
    ring
  rw [hmm]
  refine mul_nonneg (sq_nonneg _) ?_
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · exact inv_nonneg.mpr (le_of_lt (s.nu_pos_of_dvd_prodPrimes hdP))
  · exact le_of_lt (s.selbergTerms_pos hdP)
  · exact inv_nonneg.mpr (le_of_lt (selbergBoundingSum_pos s))
  · apply Finset.sum_nonneg; intro m hm
    split_ifs with h
    · exact le_of_lt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hm))
    · rfl

/-- Change of variables `l = k·m` in a sum over divisors: if `f` is supported on multiples of `k`,
the sum over `n.divisors` equals the guarded sum over `m` of `f (k·m)`. -/
theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬k ∣ l → f l = 0) :
    ∑ l ∈ n.divisors, f l = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro hc
      exact hkn ((Nat.dvd_mul_right k m).trans hc)
    · intro l hl; apply h l (Nat.dvd_of_mem_divisors hl)
      exact fun hkl => hkn (hkl.trans (Nat.dvd_of_mem_divisors hl))
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l = k * m then f l else 0)
  · rw [Finset.sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (Nat.dvd_of_mem_divisors hl) hkl, Finset.sum_eq_zero]
      intro m _; rw [ite_id]
    rw [Finset.sum_eq_single (l / k)]
    · rw [if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel _ hk0]
    · contrapose!; intro _
      rw [Nat.mem_divisors]
      exact ⟨(Nat.div_dvd_of_dvd hkl).trans (Nat.dvd_of_mem_divisors hl), hn⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl]; intro m _
    split_ifs with hdvd
    · exact (sum_intro _ (k * m) (Nat.mem_divisors.mpr ⟨hdvd, hn⟩)).symm
    · apply Finset.sum_eq_zero; intro l hl
      apply if_neg
      intro heq; rw [heq] at hl
      exact hdvd (Nat.dvd_of_mem_divisors hl)

/-- The weights, weighted by `ν`, expand as a Möbius-weighted partial sum of `selbergTerms`. -/
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * selbergWeights s d =
      (selbergBoundingSum s)⁻¹ * ((μ d : ℤ) : ℝ) *
        ∑ l ∈ s.prodPrimes.divisors,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · rw [selbergWeights, if_neg h_dvd]
    rw [Finset.sum_eq_zero]
    · ring
    intro l hl; rw [Nat.mem_divisors] at hl
    rw [if_neg (fun hc => absurd (dvd_trans hc.1 hl.left) h_dvd)]
  rw [selbergWeights, if_pos h_dvd]
  repeat rw [Finset.mul_sum]
  -- change of variables l = d * m
  apply symm
  rw [sum_mul_subst d s.prodPrimes]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ← ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [Nat.coprime_comm]
      constructor
      · intro h
        exact ⟨h.2.2, Nat.coprime_of_squarefree_mul
          (Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree)⟩
      · intro h
        exact ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (Nat.dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * s.nu d * s.selbergTerms d * ((μ d : ℤ) : ℝ) / selbergBoundingSum s *
          s.selbergTerms m)
      · rw [inv_mul_cancel₀ (s.nu_ne_zero h_dvd),
          s.selbergTerms_isMultiplicative.map_mul_of_coprime (Nat.coprime_comm.mp h.2)]
        ring
      ring
  · intro l _ hdl
    rw [if_neg (fun hc => hdl hc.1), mul_zero]

/-- Diagonalisation: `∑_{l ∣ d} ν d · w d = [l² ≤ y] · g l · μ l · S⁻¹`. -/
theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ s.prodPrimes.divisors) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeights s d else 0) =
      if (l : ℝ) ^ 2 ≤ s.level then
        s.selbergTerms l * ((μ l : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * selbergWeights s d else 0) =
        ∑ d ∈ s.prodPrimes.divisors, ∑ k ∈ s.prodPrimes.divisors,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ s.level then
            s.selbergTerms k * (selbergBoundingSum s)⁻¹ * ((μ d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum s d, ← boole_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro _; ring
    _ = ∑ k ∈ s.prodPrimes.divisors, if (k : ℝ) ^ 2 ≤ s.level then
            (∑ d ∈ s.prodPrimes.divisors, if l ∣ d ∧ d ∣ k then ((μ d : ℤ) : ℝ) else 0) *
              s.selbergTerms k * (selbergBoundingSum s)⁻¹
          else 0 := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if (l : ℝ) ^ 2 ≤ s.level then
          s.selbergTerms l * ((μ l : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ else 0 := by
      rw [sum_intro (f := fun _ => if (l : ℝ) ^ 2 ≤ s.level then
        s.selbergTerms l * ((μ l : ℤ) : ℝ) * (selbergBoundingSum s)⁻¹ else 0)
        s.prodPrimes.divisors l hl]
      apply Finset.sum_congr rfl; intro k hk
      rw [moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l k (Nat.dvd_of_mem_divisors hk),
        ← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

/-! ## N1.3: the main term equals `1 / S` -/

/-- **N1.3.** The main sum of the Selberg Λ² sieve equals `S⁻¹`. -/
theorem mainSum_eq_inv_selbergBoundingSum :
    s.mainSum (lambdaSquared (selbergWeights s)) = (selbergBoundingSum s)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  -- factor `(S⁻¹)²` out of the sum
  have key : ∀ c : ℝ, (∑ l ∈ s.prodPrimes.divisors,
        if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l * c else 0)
      = selbergBoundingSum s * c := by
    intro c
    rw [selbergBoundingSum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro l _
    rw [ite_zero_mul]
  trans (∑ l ∈ s.prodPrimes.divisors,
      if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l * ((selbergBoundingSum s)⁻¹) ^ 2 else 0)
  · apply Finset.sum_congr rfl; intro l hl
    rw [selbergWeights_diagonalisation s l hl, ite_pow, zero_pow (by norm_num), mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans ((s.selbergTerms l)⁻¹ * s.selbergTerms l * s.selbergTerms l *
        ((μ l : ℤ) : ℝ) ^ 2 * ((selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    have hμ : ((μ l : ℤ) : ℝ) ^ 2 = 1 := by
      rw [← Int.cast_pow,
        moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hl), Int.cast_one]
    rw [hμ, inv_mul_cancel₀ (ne_of_gt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)))]
    ring
  · rw [key (((selbergBoundingSum s)⁻¹) ^ 2), sq, ← mul_assoc,
      mul_inv_cancel₀ (selbergBoundingSum_ne_zero s), one_mul]

/-! ## N1.2: the weights are bounded by 1 -/

/-- If `k ∣ d` and `m` is coprime to `d`, then `k = gcd d (k·m)`. -/
theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : m.Coprime d) (hk : k ≠ 0) :
    k = d.gcd (k * m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := ⟨k, by rw [mul_comm]; exact hr⟩
  apply symm
  rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  exact Nat.Coprime.coprime_dvd_right hrdvd hmd

/-- Bookkeeping identity underlying `selbergBoundingSum_ge`. -/
theorem boundingSum_ge_helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ s.prodPrimes.divisors)
    (hm : m ∈ s.prodPrimes.divisors) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ↔
    ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d := by
  constructor
  · intro h
    refine ⟨h.2.2, ?_⟩
    obtain ⟨r, hr⟩ := hkd
    rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (Nat.pos_of_mem_divisors hk).ne'] at h
    rw [hr, Nat.coprime_comm]
    apply Nat.Coprime.mul_left
    · exact Nat.coprime_of_squarefree_mul (Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree)
    · exact h.2.1
  · intro h
    refine ⟨?_, ?_, h.1⟩
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [Nat.coprime_comm]; exact Nat.Coprime.coprime_dvd_right hkd h.2
      · exact Nat.dvd_of_mem_divisors hk
      · exact Nat.dvd_of_mem_divisors hm
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (Nat.pos_of_mem_divisors hk).ne'

/-- Lower bound `S ≥ (w d · μ d) · S` for `d ∣ P`; the engine behind `|w d| ≤ 1`. -/
theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    selbergBoundingSum s ≥ selbergWeights s d * ((μ d : ℤ) : ℝ) * selbergBoundingSum s := by
  calc
    selbergBoundingSum s
      = (∑ k ∈ s.prodPrimes.divisors, ∑ l ∈ s.prodPrimes.divisors,
          if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) := by
        rw [selbergBoundingSum, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        simp_rw [ite_and]
        rw [← sum_intro]
        rw [Nat.mem_divisors]
        exact ⟨(Nat.gcd_dvd_left d l).trans hdP, s.prodPrimes_ne_zero⟩
    _ = (∑ k ∈ s.prodPrimes.divisors,
          if k ∣ d then
            s.selbergTerms k * ∑ m ∈ s.prodPrimes.divisors,
              if ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0) := by
        apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mul_sum]
        split_ifs with hkd
        · rw [sum_mul_subst k s.prodPrimes]
          · apply Finset.sum_congr rfl; intro m hm
            rw [mul_ite_zero, ← ite_and]
            apply if_ctx_congr _ _ fun _ => rfl
            · exact boundingSum_ge_helper s hkd hk hm
            · intro h
              apply s.selbergTerms_isMultiplicative.2
              rw [Nat.coprime_comm]; exact h.2.coprime_dvd_right hkd
          · intro l _ hkl
            apply if_neg
            rintro ⟨heq, -⟩
            exact hkl (by rw [heq]; exact Nat.gcd_dvd_right d l)
        · apply Finset.sum_eq_zero; intro l _
          apply if_neg
          rintro ⟨heq, -⟩
          exact hkd (by rw [heq]; exact Nat.gcd_dvd_left d l)
    _ ≥ (∑ k ∈ s.prodPrimes.divisors,
          if k ∣ d then
            s.selbergTerms k * ∑ m ∈ s.prodPrimes.divisors,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0) := by
        apply Finset.sum_le_sum; intro k _
        split_ifs with hkd
        · apply mul_le_mul le_rfl _ _ (le_of_lt (s.selbergTerms_pos (hkd.trans hdP)))
          · apply Finset.sum_le_sum; intro m hm
            split_ifs with h h'
            · exact le_rfl
            · exfalso; apply h'
              have hkd_le : (k : ℝ) ≤ d := by
                exact_mod_cast Nat.le_of_dvd
                  (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP)) hkd
              refine ⟨le_trans ?_ h.1, h.2⟩
              push_cast
              have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
              have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
              nlinarith [mul_le_mul_of_nonneg_right hkd_le hm0, mul_nonneg hk0 hm0]
            · exact le_of_lt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hm))
            · exact le_rfl
          · apply Finset.sum_nonneg; intro m hm
            split_ifs
            · exact le_of_lt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hm))
            · exact le_rfl
        · exact le_rfl
    _ = selbergWeights s d * ((μ d : ℤ) : ℝ) * selbergBoundingSum s := by
        have step : (∑ k ∈ s.prodPrimes.divisors,
              if k ∣ d then s.selbergTerms k *
                (∑ m ∈ s.prodPrimes.divisors,
                  if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0)
              else 0)
            = (∑ k ∈ s.prodPrimes.divisors, if k ∣ d then s.selbergTerms k else 0) *
              (∑ m ∈ s.prodPrimes.divisors,
                if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _
          rw [ite_zero_mul]
        rw [step, s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
        trans (selbergBoundingSum s * (selbergBoundingSum s)⁻¹ * ((μ d : ℤ) : ℝ) ^ 2 *
            (s.nu d)⁻¹ * s.selbergTerms d *
            (∑ m ∈ s.prodPrimes.divisors,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0))
        · have hsq := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
          rw [mul_inv_cancel₀ (ne_of_gt (selbergBoundingSum_pos s)), ← Int.cast_pow,
            moebius_sq_eq_one_of_squarefree hsq, Int.cast_one]
          ring
        rw [selbergWeights, if_pos hdP]
        ring

/-- **N1.2.** The Selberg weights are bounded by 1 in absolute value. -/
theorem selbergWeights_le_one : ∀ d, |selbergWeights s d| ≤ 1 := by
  intro d
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [selbergWeights_eq_zero_of_not_dvd s hdP, abs_zero]; exact zero_le_one
  have h1 : selbergWeights s d * ((μ d : ℤ) : ℝ) * selbergBoundingSum s ≤
      1 * selbergBoundingSum s := by
    rw [one_mul]; exact selbergBoundingSum_ge s hdP
  have h2 : selbergWeights s d * ((μ d : ℤ) : ℝ) ≤ 1 :=
    le_of_mul_le_mul_right h1 (selbergBoundingSum_pos s)
  convert h2 using 1
  rw [← abs_of_nonneg (selbergWeights_mul_mu_nonneg s d hdP), abs_mul, ← Int.cast_abs,
    abs_moebius_eq_one_of_squarefree (s.prodPrimes_squarefree.squarefree_of_dvd hdP),
    Int.cast_one, mul_one]

/-! ## N1.4: the fundamental theorem -/

/-- Pairwise vanishing of the Selberg weights beyond the truncation, `wlog` half. -/
private theorem selbergWeights_mul_eq_zero_of_wlog {d : ℕ} (hd : ¬(d : ℝ) ≤ s.level)
    {d1 d2 : ℕ} (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    selbergWeights s d1 * selbergWeights s d2 = 0 := by
  have hnat : d ≤ d2 ^ 2 := by
    calc d = d1.lcm d2 := h
      _ ≤ d1 * d2 := Nat.div_le_self _ _
      _ ≤ d2 * d2 := Nat.mul_le_mul hle le_rfl
      _ = d2 ^ 2 := by rw [sq]
  have hd2 : ¬(d2 : ℝ) ^ 2 ≤ s.level := by
    intro hyp
    apply hd
    calc (d : ℝ) ≤ ((d2 ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (d2 : ℝ) ^ 2 := by push_cast; ring
      _ ≤ s.level := hyp
  rw [selbergWeights_eq_zero s hd2, mul_zero]

/-- The Λ² coefficients vanish beyond the sieve level: `d > y ⇒ μ⁺ d = 0`. -/
theorem selbergMuPlus_eq_zero {d : ℕ} (hd : ¬(d : ℝ) ≤ s.level) :
    lambdaSquared (selbergWeights s) d = 0 := by
  dsimp only [lambdaSquared]
  apply Finset.sum_eq_zero; intro d1 _
  apply Finset.sum_eq_zero; intro d2 _
  split_ifs with h
  · rcases Nat.le_total d1 d2 with hle | hle
    · exact selbergWeights_mul_eq_zero_of_wlog s hd h hle
    · rw [mul_comm]
      exact selbergWeights_mul_eq_zero_of_wlog s hd (Nat.lcm_comm d1 d2 ▸ h) hle
  · rfl

/-- **Fundamental error bound.** `|μ⁺ n| ≤ 3^ω n` for `n ∣ P`. -/
theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ s.prodPrimes.divisors) :
    |lambdaSquared (selbergWeights s) n| ≤ (3 : ℝ) ^ ω n := by
  dsimp only [lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
        if n = Nat.lcm d1 d2 then selbergWeights s d1 * selbergWeights s d2 else 0|
      ≤ ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors,
          if n = Nat.lcm d1 d2 then selbergWeights s d1 * selbergWeights s d2 else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
          |if n = Nat.lcm d1 d2 then selbergWeights s d1 * selbergWeights s d2 else 0| := by
        gcongr; apply abs_sum_le_sum_abs
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = Nat.lcm d1 d2 then (1 : ℝ) else 0 := by
        gcongr with d1 _ d2
        rw [apply_ite abs, abs_zero, abs_mul]
        split_ifs with h
        · exact mul_le_one₀ (selbergWeights_le_one s d1) (abs_nonneg _) (selbergWeights_le_one s d2)
        · exact le_rfl
    _ = ∑ p ∈ n.divisors ×ˢ n.divisors, if n = Nat.lcm p.1 p.2 then (1 : ℝ) else 0 := by
        rw [← Finset.sum_product']
    _ = (((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = Nat.lcm p.1 p.2).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, Nat.smul_one_eq_cast]
    _ = (((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = n).card : ℝ) := by
        norm_cast
        congr 1; ext p; simp only [Finset.mem_filter, eq_comm]
    _ = (3 : ℝ) ^ ω n := by
        rw [Nat.card_pair_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn)]
        push_cast; ring

/-- The error sum for the Selberg μ⁺ is bounded by the simple `3^ω` error term. -/
theorem selberg_bound_simple_errSum :
    s.errSum (lambdaSquared (selbergWeights s)) ≤
      ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · refine mul_le_mul (selberg_bound_muPlus s d hd) le_rfl (abs_nonneg (s.rem d)) ?_
    positivity
  · rw [selbergMuPlus_eq_zero s h, abs_zero, zero_mul]

/-- **N1.4.** The simple form of the Selberg sieve fundamental theorem. -/
theorem selberg_bound_simple :
    s.siftedSum ≤ s.totalMass / selbergBoundingSum s +
      ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  have hmain : s.totalMass * s.mainSum (lambdaSquared (selbergWeights s)) =
      s.totalMass / selbergBoundingSum s := by
    rw [mainSum_eq_inv_selbergBoundingSum s, div_eq_mul_inv]
  calc
    s.siftedSum ≤ s.totalMass * s.mainSum (lambdaSquared (selbergWeights s)) +
        s.errSum (lambdaSquared (selbergWeights s)) :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius (lambdaSquared (selbergWeights s))
        (upperMoebius_lambdaSquared (selbergWeights s) (selbergWeights_one s))
    _ = s.totalMass / selbergBoundingSum s + s.errSum (lambdaSquared (selbergWeights s)) := by
        rw [hmain]
    _ ≤ s.totalMass / selbergBoundingSum s +
          ∑ d ∈ s.prodPrimes.divisors,
            if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
        gcongr
        exact selberg_bound_simple_errSum s

end Salt.SelbergPort

end




section
open Finset ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega
variable (s : SelbergSieve)

theorem solution (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) = if l = m then (μ l : ℤ) else 0 := by
  apply Salt.SelbergPort.moebius_inv_dvd_lower_bound <;> assumption

end

