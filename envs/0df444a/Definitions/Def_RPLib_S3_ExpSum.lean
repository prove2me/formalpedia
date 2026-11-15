-- Prove2me | Definitions.Def_RPLib_S3_ExpSum
-- name    : RPLib_S3_ExpSum
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:35.179968+00:00
-- url     : https://prove2.me/theorems/dafed3aa-9cd0-46a0-9a8f-d6fe73b4776b
-- title:
--   Weight-two Ramanujan-Petersson library: Exponential polynomials: uniqueness, growth and sign lemmas
-- statement:
--   Exponential polynomials: uniqueness, growth and sign lemmas.
--
--   Unit S3-ExpSum of the Ramanujan-Petersson project. Import Mathlib only.
--
--   For `s : Finset ℂ` and `c : ℂ → ℂ` the exponential polynomial is `m ↦ ∑ z ∈ s, c z * z ^ m`.
--
--   * (a) `expSum_coeff_eq_zero` (the exact statement of S4_DESIGN.md §6 (III)),
--     `expSum_coeff_eq_zero_of_ne_zero` (0 allowed in `s`), arithmetic-progression form
--     `expSum_ap_coeff_eq_zero` (grouped coefficients).
--   * (b) `norm_le_of_expSum_isBigO`, its converse `expSum_comp_isBigO`, the iff `expSum_isBigO_iff`,
--     arithmetic-progression form `norm_le_of_expSum_isBigO_ap` (grouped coefficients; the ungrouped
--     single-residue form is false, see `sanity_ap_cancel`).
--   * (c) multisets: `powerSum_eq_sum_count`, `count_eq_of_powerSum_eq`, `multiset_eq_of_powerSum_eq`,
--     signed integer form `count_sub_eq_of_trace_identity` (`n(λ) - e(λ) = h1(λ) - h2(λ)`).
--   * (d) sign forms: `coeff_eq_zero_of_nonneg(_ap)`, `sign_form(_ap)`, `sign_form_int`,
--     `multiset_norm_le_of_powerSum_isBigO(_ap)`, and the N4 matching conclusion
--     `multiset_norm_le_of_trace_identity(_ap)` (S4_DESIGN.md §6 (IV), both k ≥ 3 and k = 2).
--
--   Method: the isolation polynomial `∏_{w ∈ s, w ≠ z₀} (X - w)` (the Vandermonde argument in
--   polynomial form) turns a finite combination of shifts of the sequence into `c z₀ P(z₀) z₀ ^ m`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib

/-!
# Exponential polynomials: uniqueness, growth and sign lemmas

Unit S3-ExpSum of the Ramanujan-Petersson project. Import Mathlib only.

For `s : Finset ℂ` and `c : ℂ → ℂ` the exponential polynomial is `m ↦ ∑ z ∈ s, c z * z ^ m`.

* (a) `expSum_coeff_eq_zero` (the exact statement of S4_DESIGN.md §6 (III)),
  `expSum_coeff_eq_zero_of_ne_zero` (0 allowed in `s`), arithmetic-progression form
  `expSum_ap_coeff_eq_zero` (grouped coefficients).
* (b) `norm_le_of_expSum_isBigO`, its converse `expSum_comp_isBigO`, the iff `expSum_isBigO_iff`,
  arithmetic-progression form `norm_le_of_expSum_isBigO_ap` (grouped coefficients; the ungrouped
  single-residue form is false, see `sanity_ap_cancel`).
* (c) multisets: `powerSum_eq_sum_count`, `count_eq_of_powerSum_eq`, `multiset_eq_of_powerSum_eq`,
  signed integer form `count_sub_eq_of_trace_identity` (`n(λ) - e(λ) = h1(λ) - h2(λ)`).
* (d) sign forms: `coeff_eq_zero_of_nonneg(_ap)`, `sign_form(_ap)`, `sign_form_int`,
  `multiset_norm_le_of_powerSum_isBigO(_ap)`, and the N4 matching conclusion
  `multiset_norm_le_of_trace_identity(_ap)` (S4_DESIGN.md §6 (IV), both k ≥ 3 and k = 2).

Method: the isolation polynomial `∏_{w ∈ s, w ≠ z₀} (X - w)` (the Vandermonde argument in
polynomial form) turns a finite combination of shifts of the sequence into `c z₀ P(z₀) z₀ ^ m`.
-/

set_option autoImplicit false

open Filter Asymptotics Polynomial

namespace RamanujanPetersson.ExpSum

/-! ### The isolation polynomial -/

/-- `isoPoly s z₀ = ∏_{w ∈ s, w ≠ z₀} (X - w)`. -/
noncomputable def isoPoly (s : Finset ℂ) (z₀ : ℂ) : ℂ[X] :=
  ∏ w ∈ s.erase z₀, (X - C w)

theorem isoPoly_eval_of_ne (s : Finset ℂ) (z₀ z : ℂ) (hz : z ∈ s) (hne : z ≠ z₀) :
    (isoPoly s z₀).eval z = 0 := by
  unfold isoPoly
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, hz⟩) (by simp)

theorem isoPoly_eval_self_ne_zero (s : Finset ℂ) (z₀ : ℂ) : (isoPoly s z₀).eval z₀ ≠ 0 := by
  unfold isoPoly
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro w hw
  rw [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hw).1 h.symm

/-- Evaluating a polynomial against an exponential polynomial is a finite combination of shifts. -/
theorem sum_mul_eval_mul_pow (s : Finset ℂ) (c : ℂ → ℂ) (P : ℂ[X]) (m : ℕ) :
    ∑ z ∈ s, c z * P.eval z * z ^ m =
      ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ∑ z ∈ s, c z * z ^ (m + k) := by
  simp_rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem sum_isoPoly (s : Finset ℂ) (c : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ s) (m : ℕ) :
    ∑ z ∈ s, c z * (isoPoly s z₀).eval z * z ^ m = c z₀ * (isoPoly s z₀).eval z₀ * z₀ ^ m := by
  refine Finset.sum_eq_single_of_mem z₀ hz₀ fun z hz hne => ?_
  rw [isoPoly_eval_of_ne s z₀ z hz hne, mul_zero, zero_mul]

/-- Isolation identity: `c z₀ P(z₀) z₀ ^ m` is a fixed finite combination of shifted sums. -/
theorem isolate (s : Finset ℂ) (c : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ s) (m : ℕ) :
    c z₀ * (isoPoly s z₀).eval z₀ * z₀ ^ m =
      ∑ k ∈ Finset.range ((isoPoly s z₀).natDegree + 1),
        (isoPoly s z₀).coeff k * ∑ z ∈ s, c z * z ^ (m + k) := by
  rw [← sum_isoPoly s c hz₀ m, sum_mul_eval_mul_pow]

/-! ### (a) Vanishing -/

/-- **(a)**, `0 ∈ s` allowed: an exponential polynomial vanishing for all `m ≥ 1` has zero
coefficients at all nonzero bases. -/
theorem expSum_coeff_eq_zero_of_ne_zero (s : Finset ℂ) (c : ℂ → ℂ)
    (h : ∀ m : ℕ, 1 ≤ m → ∑ z ∈ s, c z * z ^ m = 0) : ∀ z ∈ s, z ≠ 0 → c z = 0 := by
  intro z₀ hz₀ hne
  have key := isolate s c hz₀ 1
  have hzero : ∑ k ∈ Finset.range ((isoPoly s z₀).natDegree + 1),
      (isoPoly s z₀).coeff k * ∑ z ∈ s, c z * z ^ (1 + k) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [h (1 + k) (by omega), mul_zero]
  rw [hzero] at key
  rcases mul_eq_zero.1 key with h1 | h1
  · exact (mul_eq_zero.1 h1).resolve_right (isoPoly_eval_self_ne_zero s z₀)
  · exact absurd (by simpa using h1) hne

/-- **(a)** Exponential-sum uniqueness, exactly as named in S4_DESIGN.md §6 (III). -/
theorem expSum_coeff_eq_zero (s : Finset ℂ) (c : ℂ → ℂ) (h0 : (0 : ℂ) ∉ s)
    (h : ∀ m : ℕ, 1 ≤ m → ∑ z ∈ s, c z * z ^ m = 0) : ∀ z ∈ s, c z = 0 :=
  fun z hz => expSum_coeff_eq_zero_of_ne_zero s c h z hz fun hz0 => h0 (hz0 ▸ hz)

/-- Two exponential polynomials with equal values for all `m ≥ 1` have equal coefficients at
all nonzero bases. -/
theorem expSum_coeff_eq_of_eq (s : Finset ℂ) (a b : ℂ → ℂ)
    (h : ∀ m : ℕ, 1 ≤ m → ∑ z ∈ s, a z * z ^ m = ∑ z ∈ s, b z * z ^ m) :
    ∀ z ∈ s, z ≠ 0 → a z = b z := by
  intro z hz hz0
  have : a z - b z = 0 := expSum_coeff_eq_zero_of_ne_zero s (fun z => a z - b z)
    (fun m hm => by simp only [sub_mul, Finset.sum_sub_distrib, h m hm, sub_self]) z hz hz0
  exact sub_eq_zero.1 this

/-- Regrouping an exponential polynomial along the progression `d * N + r` by the fibres of
`z ↦ z ^ d`. -/
theorem expSum_ap_eq (s : Finset ℂ) (c : ℂ → ℂ) (d r N : ℕ) :
    ∑ z ∈ s, c z * z ^ (d * N + r) =
      ∑ v ∈ s.image (· ^ d), (∑ w ∈ s with w ^ d = v, c w * w ^ r) * v ^ N := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (· ^ d)) (g := fun z : ℂ => z ^ d)
    (fun z hz => Finset.mem_image_of_mem _ hz) (fun z => c z * z ^ (d * N + r))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [← (Finset.mem_filter.1 hw).2, pow_add, pow_mul]
  ring

/-- **(a)** along an arithmetic progression: vanishing for all `m = d * N + r`, `N ≥ 1`, kills
the grouped coefficients `∑_{w ∈ s, w ^ d = z ^ d} c w * w ^ r` at nonzero `z`. -/
theorem expSum_ap_coeff_eq_zero (s : Finset ℂ) (c : ℂ → ℂ) (d r : ℕ)
    (h : ∀ N : ℕ, 1 ≤ N → ∑ z ∈ s, c z * z ^ (d * N + r) = 0) :
    ∀ z ∈ s, z ≠ 0 → ∑ w ∈ s with w ^ d = z ^ d, c w * w ^ r = 0 := by
  intro z hz hz0
  exact expSum_coeff_eq_zero_of_ne_zero (s.image (· ^ d))
    (fun v => ∑ w ∈ s with w ^ d = v, c w * w ^ r)
    (fun N hN => (expSum_ap_eq s c d r N).symm.trans (h N hN)) (z ^ d)
    (Finset.mem_image_of_mem _ hz) (pow_ne_zero d hz0)

/-! ### (b) Growth -/

theorem pow_comp_isBigO {α : Type*} (l : Filter α) (φ : α → ℕ) {z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hz : ‖z‖ ≤ R) : (fun a => z ^ φ a) =O[l] (fun a => R ^ φ a) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun a => ?_)
  rw [norm_pow, Real.norm_eq_abs, abs_pow, abs_of_nonneg hR, one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hz _

/-- Converse of (b), along any reindexing `φ` and any filter. -/
theorem expSum_comp_isBigO {α : Type*} (l : Filter α) (φ : α → ℕ) (s : Finset ℂ) (c : ℂ → ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ z ∈ s, c z ≠ 0 → ‖z‖ ≤ R) :
    (fun a => ∑ z ∈ s, c z * z ^ φ a) =O[l] (fun a => R ^ φ a) := by
  refine IsBigO.fun_sum fun z hz => ?_
  by_cases hc : c z = 0
  · simp only [hc, zero_mul]
    exact isBigO_zero _ _
  · exact (pow_comp_isBigO l φ hR (hs z hz hc)).const_mul_left (c z)

theorem norm_le_of_pow_isBigO {z : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : (fun m : ℕ => z ^ m) =O[atTop] (fun m : ℕ => R ^ m)) : ‖z‖ ≤ R := by
  by_contra hlt
  rw [not_le] at hlt
  have hz : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hlt
    exact absurd hR (not_le.2 hlt)
  have h1 : (fun m : ℕ => R ^ m) =o[atTop] (fun m : ℕ => ‖z‖ ^ m) :=
    isLittleO_pow_pow_of_lt_left hR hlt
  have h2 : (fun m : ℕ => ‖z‖ ^ m) =O[atTop] (fun m : ℕ => z ^ m) := by
    simpa only [norm_pow] using (isBigO_refl (fun m : ℕ => z ^ m) atTop).norm_left
  have h3 : (fun m : ℕ => z ^ m) =o[atTop] (fun m : ℕ => z ^ m) :=
    h.trans_isLittleO (h1.trans_isBigO h2)
  exact isLittleO_irrefl (Eventually.of_forall fun m => pow_ne_zero m hz).frequently h3

/-- **(b)** Growth: if the exponential polynomial is `O(R ^ m)`, every base with a nonzero
coefficient has modulus at most `R`. -/
theorem norm_le_of_expSum_isBigO (s : Finset ℂ) (c : ℂ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : (fun m : ℕ => ∑ z ∈ s, c z * z ^ m) =O[atTop] (fun m : ℕ => R ^ m)) :
    ∀ z ∈ s, c z ≠ 0 → ‖z‖ ≤ R := by
  intro z₀ hz₀ hc
  have hshift : ∀ k : ℕ,
      (fun m : ℕ => ∑ z ∈ s, c z * z ^ (m + k)) =O[atTop] (fun m : ℕ => R ^ m) := by
    intro k
    have h1 : (fun m : ℕ => ∑ z ∈ s, c z * z ^ (m + k)) =O[atTop] (fun m : ℕ => R ^ (m + k)) :=
      h.comp_tendsto (tendsto_add_atTop_nat k)
    have h2 : (fun m : ℕ => R ^ (m + k)) =O[atTop] (fun m : ℕ => R ^ m) :=
      ((isBigO_refl (fun m : ℕ => R ^ m) atTop).const_mul_left (R ^ k)).congr_left
        fun m => by ring
    exact h1.trans h2
  have hsum : (fun m : ℕ => ∑ k ∈ Finset.range ((isoPoly s z₀).natDegree + 1),
      (isoPoly s z₀).coeff k * ∑ z ∈ s, c z * z ^ (m + k)) =O[atTop] (fun m : ℕ => R ^ m) :=
    IsBigO.fun_sum fun k _ => (hshift k).const_mul_left _
  have hK : c z₀ * (isoPoly s z₀).eval z₀ ≠ 0 := mul_ne_zero hc (isoPoly_eval_self_ne_zero s z₀)
  have hpow : (fun m : ℕ => z₀ ^ m) =O[atTop] (fun m : ℕ => R ^ m) :=
    ((hsum.congr_left fun m => (isolate s c hz₀ m).symm).const_mul_left
      (c z₀ * (isoPoly s z₀).eval z₀)⁻¹).congr_left fun m => by
        rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  exact norm_le_of_pow_isBigO hR hpow

/-- **(b)** as an equivalence. -/
theorem expSum_isBigO_iff (s : Finset ℂ) (c : ℂ → ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (fun m : ℕ => ∑ z ∈ s, c z * z ^ m) =O[atTop] (fun m : ℕ => R ^ m) ↔
      ∀ z ∈ s, c z ≠ 0 → ‖z‖ ≤ R :=
  ⟨norm_le_of_expSum_isBigO s c hR, expSum_comp_isBigO atTop id s c hR⟩

/-- **(b)** along an arithmetic progression `m = d * N + r`: the conclusion concerns the
grouped coefficients `∑_{w ∈ s, w ^ d = z ^ d} c w * w ^ r` (the ungrouped statement is false). -/
theorem norm_le_of_expSum_isBigO_ap (s : Finset ℂ) (c : ℂ → ℂ) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : 0 < d) (r : ℕ)
    (h : (fun N : ℕ => ∑ z ∈ s, c z * z ^ (d * N + r)) =O[atTop] (fun N : ℕ => R ^ (d * N))) :
    ∀ z ∈ s, (∑ w ∈ s with w ^ d = z ^ d, c w * w ^ r) ≠ 0 → ‖z‖ ≤ R := by
  intro z₀ hz₀ hC
  have h' : (fun N : ℕ => ∑ v ∈ s.image (· ^ d), (∑ w ∈ s with w ^ d = v, c w * w ^ r) * v ^ N)
      =O[atTop] (fun N : ℕ => (R ^ d) ^ N) :=
    (h.congr_left fun N => expSum_ap_eq s c d r N).congr_right fun N => pow_mul R d N
  have := norm_le_of_expSum_isBigO (s.image (· ^ d))
    (fun v => ∑ w ∈ s with w ^ d = v, c w * w ^ r) (pow_nonneg hR d) h' (z₀ ^ d)
    (Finset.mem_image_of_mem _ hz₀) hC
  rw [norm_pow] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR hd.ne').1 this

/-! ### (d) Sign forms -/

/-- **(d)** core, along `m = d * N`: real coefficients that are `≥ 0` beyond modulus `R` and an
`O(R ^ m)` exponential polynomial force those coefficients to vanish. (A fibre `w ^ d = v` has
constant modulus, so the grouped coefficient is a sum of nonnegative terms.) -/
theorem coeff_eq_zero_of_nonneg_ap (s : Finset ℂ) (c : ℂ → ℝ) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : 0 < d) (hc : ∀ z ∈ s, R < ‖z‖ → 0 ≤ c z)
    (h : (fun N : ℕ => ∑ z ∈ s, (c z : ℂ) * z ^ (d * N)) =O[atTop]
      (fun N : ℕ => R ^ (d * N))) :
    ∀ z ∈ s, R < ‖z‖ → c z = 0 := by
  intro z₀ hz₀ hlt
  by_contra hne
  have hfib : ∀ w ∈ s.filter (fun w => w ^ d = z₀ ^ d), R < ‖w‖ := by
    intro w hw
    have hn : ‖w‖ ^ d = ‖z₀‖ ^ d := by rw [← norm_pow, (Finset.mem_filter.1 hw).2, norm_pow]
    rwa [(pow_left_inj₀ (norm_nonneg w) (norm_nonneg z₀) hd.ne').1 hn]
  have hpos : 0 < ∑ w ∈ s with w ^ d = z₀ ^ d, c w :=
    Finset.sum_pos' (fun w hw => hc w (Finset.mem_filter.1 hw).1 (hfib w hw))
      ⟨z₀, Finset.mem_filter.2 ⟨hz₀, rfl⟩, lt_of_le_of_ne (hc z₀ hz₀ hlt) (Ne.symm hne)⟩
  have hC : (∑ w ∈ s with w ^ d = z₀ ^ d, (c w : ℂ) * w ^ 0) ≠ 0 := by
    simp only [pow_zero, mul_one]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_ne_zero.2 hpos.ne'
  have h' : (fun N : ℕ => ∑ z ∈ s, (c z : ℂ) * z ^ (d * N + 0)) =O[atTop]
      (fun N : ℕ => R ^ (d * N)) := by simpa only [add_zero] using h
  exact absurd (norm_le_of_expSum_isBigO_ap s (fun z => (c z : ℂ)) hR hd 0 h' z₀ hz₀ hC)
    (not_le.2 hlt)

/-- **(d)** core, all `m`. -/
theorem coeff_eq_zero_of_nonneg (s : Finset ℂ) (c : ℂ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hc : ∀ z ∈ s, R < ‖z‖ → 0 ≤ c z)
    (h : (fun m : ℕ => ∑ z ∈ s, (c z : ℂ) * z ^ m) =O[atTop] (fun m : ℕ => R ^ m)) :
    ∀ z ∈ s, R < ‖z‖ → c z = 0 :=
  coeff_eq_zero_of_nonneg_ap s c hR one_pos hc (by simpa only [one_mul] using h)

/-- **(d)** Sign form: `∑ (n λ + g λ) λ ^ m = O(R ^ m)` with natural-number multiplicities
forces `n λ = g λ = 0` for `|λ| > R`. -/
theorem sign_form (s : Finset ℂ) (n g : ℂ → ℕ) {R : ℝ} (hR : 0 ≤ R)
    (h : (fun m : ℕ => ∑ z ∈ s, ((n z : ℂ) + g z) * z ^ m) =O[atTop] (fun m : ℕ => R ^ m)) :
    ∀ z ∈ s, R < ‖z‖ → n z = 0 ∧ g z = 0 := by
  intro z hz hlt
  have h0 : (n z : ℝ) + g z = 0 := coeff_eq_zero_of_nonneg s (fun z => (n z : ℝ) + g z) hR
    (fun _ _ _ => by positivity) (by simpa using h) z hz hlt
  have : n z + g z = 0 := by exact_mod_cast h0
  omega

/-- **(d)** Sign form along `m = d * N`. -/
theorem sign_form_ap (s : Finset ℂ) (n g : ℂ → ℕ) {R : ℝ} (hR : 0 ≤ R) {d : ℕ} (hd : 0 < d)
    (h : (fun N : ℕ => ∑ z ∈ s, ((n z : ℂ) + g z) * z ^ (d * N)) =O[atTop]
      (fun N : ℕ => R ^ (d * N))) :
    ∀ z ∈ s, R < ‖z‖ → n z = 0 ∧ g z = 0 := by
  intro z hz hlt
  have h0 : (n z : ℝ) + g z = 0 := coeff_eq_zero_of_nonneg_ap s (fun z => (n z : ℝ) + g z) hR hd
    (fun _ _ _ => by positivity) (by simpa using h) z hz hlt
  have : n z + g z = 0 := by exact_mod_cast h0
  omega

/-- **(d)** Sign form with nonnegative integer multiplicities. -/
theorem sign_form_int (s : Finset ℂ) (n g : ℂ → ℤ) (hn : ∀ z ∈ s, 0 ≤ n z)
    (hg : ∀ z ∈ s, 0 ≤ g z) {R : ℝ} (hR : 0 ≤ R)
    (h : (fun m : ℕ => ∑ z ∈ s, ((n z : ℂ) + g z) * z ^ m) =O[atTop] (fun m : ℕ => R ^ m)) :
    ∀ z ∈ s, R < ‖z‖ → n z = 0 ∧ g z = 0 := by
  intro z hz hlt
  have h0 : (n z : ℝ) + g z = 0 := coeff_eq_zero_of_nonneg s (fun z => (n z : ℝ) + g z) hR
    (fun w hw _ => by
      have h1 : (0 : ℝ) ≤ n w := by exact_mod_cast hn w hw
      have h2 : (0 : ℝ) ≤ g w := by exact_mod_cast hg w hw
      linarith) (by simpa using h) z hz hlt
  have : n z + g z = 0 := by exact_mod_cast h0
  have := hn z hz
  have := hg z hz
  omega

/-! ### (c) Multisets and integer multiplicities -/

theorem powerSum_eq_sum_count (A : Multiset ℂ) (m : ℕ) :
    (A.map (· ^ m)).sum = ∑ z ∈ A.toFinset, (A.count z : ℂ) * z ^ m := by
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]

theorem powerSum_eq_sum_count_of_subset (A : Multiset ℂ) {T : Finset ℂ} (hT : A.toFinset ⊆ T)
    (m : ℕ) : (A.map (· ^ m)).sum = ∑ z ∈ T, (A.count z : ℂ) * z ^ m := by
  rw [powerSum_eq_sum_count]
  refine Finset.sum_subset hT fun z _ hz => ?_
  rw [Multiset.count_eq_zero.2 fun h => hz (Multiset.mem_toFinset.2 h), Nat.cast_zero, zero_mul]

/-- Extending `∑ z ∈ s, e z * z ^ m` to a superset `T` by zero coefficients. -/
theorem sum_eq_sum_ite_of_subset (s T : Finset ℂ) (hsT : s ⊆ T) (e : ℂ → ℤ) (m : ℕ) :
    ∑ z ∈ s, (e z : ℂ) * z ^ m = ∑ z ∈ T, ((if z ∈ s then e z else 0 : ℤ) : ℂ) * z ^ m := by
  rw [← Finset.sum_subset hsT fun z _ hz => by simp [hz]]
  exact Finset.sum_congr rfl fun z hz => by simp [hz]

/-- **(c)** Signed integer-multiplicity form (S4_DESIGN.md §6 (III)): if the power sums satisfy
`N(m) = H1(m) - H2(m) + ∑_{z ∈ s} e z * z ^ m` for all `m ≥ 1`, then
`n(λ) - e(λ) = h1(λ) - h2(λ)` for every `λ ≠ 0` (with `e(λ) = 0` off `s`). -/
theorem count_sub_eq_of_trace_identity (Nm H1 H2 : Multiset ℂ) (s : Finset ℂ) (e : ℂ → ℤ)
    (h : ∀ m : ℕ, 1 ≤ m → (Nm.map (· ^ m)).sum =
      (H1.map (· ^ m)).sum - (H2.map (· ^ m)).sum + ∑ z ∈ s, (e z : ℂ) * z ^ m) :
    ∀ z : ℂ, z ≠ 0 →
      (Nm.count z : ℤ) - (if z ∈ s then e z else 0) = H1.count z - H2.count z := by
  intro z hz0
  set T : Finset ℂ := (Nm + H1 + H2).toFinset ∪ s with hT
  have hNT : Nm.toFinset ⊆ T := fun x hx => by
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] at hx ⊢
    tauto
  have hH1T : H1.toFinset ⊆ T := fun x hx => by
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] at hx ⊢
    tauto
  have hH2T : H2.toFinset ⊆ T := fun x hx => by
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] at hx ⊢
    tauto
  have hsT : s ⊆ T := Finset.subset_union_right
  have key : ∀ m : ℕ, 1 ≤ m →
      ∑ z ∈ T, (((Nm.count z : ℤ) + H2.count z : ℤ) : ℂ) * z ^ m =
        ∑ z ∈ T, (((H1.count z : ℤ) + (if z ∈ s then e z else 0) : ℤ) : ℂ) * z ^ m := by
    intro m hm
    simp only [Int.cast_add, Int.cast_natCast, add_mul, Finset.sum_add_distrib]
    rw [← powerSum_eq_sum_count_of_subset Nm hNT, ← powerSum_eq_sum_count_of_subset H2 hH2T,
      ← powerSum_eq_sum_count_of_subset H1 hH1T, ← sum_eq_sum_ite_of_subset s T hsT e m, h m hm]
    ring
  by_cases hzT : z ∈ T
  · have := expSum_coeff_eq_of_eq T _ _ key z hzT hz0
    have h' : (Nm.count z : ℤ) + H2.count z = H1.count z + (if z ∈ s then e z else 0) := by
      exact_mod_cast this
    linarith
  · have hzN : z ∉ Nm := fun hz => hzT (hNT (Multiset.mem_toFinset.2 hz))
    have hz1 : z ∉ H1 := fun hz => hzT (hH1T (Multiset.mem_toFinset.2 hz))
    have hz2 : z ∉ H2 := fun hz => hzT (hH2T (Multiset.mem_toFinset.2 hz))
    have hzs : z ∉ s := fun hz => hzT (hsT hz)
    simp [Multiset.count_eq_zero.2 hzN, Multiset.count_eq_zero.2 hz1,
      Multiset.count_eq_zero.2 hz2, hzs]

/-- **(c)** Equal power sums for all `m ≥ 1` give equal multiplicities at every `λ ≠ 0`. -/
theorem count_eq_of_powerSum_eq (A B : Multiset ℂ)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map (· ^ m)).sum = (B.map (· ^ m)).sum) :
    ∀ z : ℂ, z ≠ 0 → A.count z = B.count z := by
  intro z hz
  have := count_sub_eq_of_trace_identity A B 0 ∅ (fun _ => 0) (fun m hm => by simp [h m hm]) z hz
  simpa using this

/-- **(c)** Two multisets of nonzero complex numbers with equal power sums for all `m ≥ 1` are
equal. -/
theorem multiset_eq_of_powerSum_eq (A B : Multiset ℂ) (hA : (0 : ℂ) ∉ A) (hB : (0 : ℂ) ∉ B)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map (· ^ m)).sum = (B.map (· ^ m)).sum) : A = B := by
  refine Multiset.ext.2 fun z => ?_
  by_cases hz : z = 0
  · subst hz
    rw [Multiset.count_eq_zero.2 hA, Multiset.count_eq_zero.2 hB]
  · exact count_eq_of_powerSum_eq A B h z hz

/-- **(d)** for a multiset along `m = d * N`: `O(R ^ m)` power sums force every element to have
modulus at most `R`. -/
theorem multiset_norm_le_of_powerSum_isBigO_ap (A : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) {d : ℕ}
    (hd : 0 < d)
    (h : (fun N : ℕ => (A.map (· ^ (d * N))).sum) =O[atTop] (fun N : ℕ => R ^ (d * N))) :
    ∀ x ∈ A, ‖x‖ ≤ R := by
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  have h' : (fun N : ℕ => ∑ z ∈ A.toFinset, ((A.count z : ℝ) : ℂ) * z ^ (d * N)) =O[atTop]
      (fun N : ℕ => R ^ (d * N)) :=
    h.congr_left fun N => by rw [powerSum_eq_sum_count]; simp only [Complex.ofReal_natCast]
  have h0 : (A.count x : ℝ) = 0 := coeff_eq_zero_of_nonneg_ap A.toFinset (fun z => (A.count z : ℝ))
    hR hd (fun _ _ _ => Nat.cast_nonneg _) h' x (Multiset.mem_toFinset.2 hx) hlt
  have : A.count x = 0 := by exact_mod_cast h0
  exact (Multiset.count_eq_zero.1 this) hx

/-- **(d)** for a multiset: `O(R ^ m)` power sums force every element to have modulus `≤ R`. -/
theorem multiset_norm_le_of_powerSum_isBigO (A : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : (fun m : ℕ => (A.map (· ^ m)).sum) =O[atTop] (fun m : ℕ => R ^ m)) :
    ∀ x ∈ A, ‖x‖ ≤ R :=
  multiset_norm_le_of_powerSum_isBigO_ap A hR one_pos (by simpa only [one_mul] using h)

/-- Power sums of a multiset bounded by `R` are `O(R ^ φ)`. -/
theorem powerSum_comp_isBigO {α : Type*} (l : Filter α) (φ : α → ℕ) (A : Multiset ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    (fun a => (A.map (· ^ φ a)).sum) =O[l] (fun a => R ^ φ a) :=
  (expSum_comp_isBigO l φ A.toFinset (fun z => (A.count z : ℂ)) hR
    fun z hz _ => hA z (Multiset.mem_toFinset.1 hz)).congr_left
    fun a => (powerSum_eq_sum_count A (φ a)).symm

/-- **(d)**, the N4 matching conclusion (S4_DESIGN.md §6 (IV)) along `m = d * N`: if
`N(m) = H1(m) - H2(m) + ∑_{z ∈ s} e z * z ^ m` for `m = d * N`, `N ≥ 1`, every element of `H1`
has modulus `≤ R`, and `e z ≤ h2(z)` whenever `|z| > R`, then every element of `N` has modulus
`≤ R`. (k ≥ 3: `e z ≤ 0` beyond `R`; k = 2: `e p = 1 ≤ h2(p)`.) -/
theorem multiset_norm_le_of_trace_identity_ap (Nm H1 H2 : Multiset ℂ) (s : Finset ℂ)
    (e : ℂ → ℤ) {R : ℝ} (hR : 0 ≤ R) {d : ℕ} (hd : 0 < d) (hH1 : ∀ x ∈ H1, ‖x‖ ≤ R)
    (he : ∀ z ∈ s, R < ‖z‖ → e z ≤ H2.count z)
    (h : ∀ N : ℕ, 1 ≤ N → (Nm.map (· ^ (d * N))).sum =
      (H1.map (· ^ (d * N))).sum - (H2.map (· ^ (d * N))).sum +
        ∑ z ∈ s, (e z : ℂ) * z ^ (d * N)) :
    ∀ x ∈ Nm, ‖x‖ ≤ R := by
  set T : Finset ℂ := (Nm + H2).toFinset ∪ s with hT
  have hNT : Nm.toFinset ⊆ T := fun x hx => by
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] at hx ⊢
    tauto
  have hH2T : H2.toFinset ⊆ T := fun x hx => by
    simp only [hT, Finset.mem_union, Multiset.mem_toFinset, Multiset.mem_add] at hx ⊢
    tauto
  have hsT : s ⊆ T := Finset.subset_union_right
  -- the real coefficient `n + h2 - e`
  have hc : ∀ z ∈ T, R < ‖z‖ →
      0 ≤ ((Nm.count z : ℝ) + H2.count z - ((if z ∈ s then e z else 0 : ℤ) : ℝ)) := by
    intro z _ hlt
    have h1 : (0 : ℝ) ≤ Nm.count z := Nat.cast_nonneg _
    by_cases hzs : z ∈ s
    · have h2 : ((e z : ℤ) : ℝ) ≤ H2.count z := by exact_mod_cast he z hzs hlt
      rw [if_pos hzs]
      linarith
    · have h2 : (0 : ℝ) ≤ H2.count z := Nat.cast_nonneg _
      rw [if_neg hzs, Int.cast_zero]
      linarith
  have hid : ∀ N : ℕ, 1 ≤ N →
      ∑ z ∈ T, (((Nm.count z : ℝ) + H2.count z - ((if z ∈ s then e z else 0 : ℤ) : ℝ) : ℝ) : ℂ) *
        z ^ (d * N) = (H1.map (· ^ (d * N))).sum := by
    intro N hN
    simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_intCast, sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← powerSum_eq_sum_count_of_subset Nm hNT, ← powerSum_eq_sum_count_of_subset H2 hH2T,
      ← sum_eq_sum_ite_of_subset s T hsT e (d * N), h N hN]
    ring
  have hbig : (fun N : ℕ => ∑ z ∈ T,
      (((Nm.count z : ℝ) + H2.count z - ((if z ∈ s then e z else 0 : ℤ) : ℝ) : ℝ) : ℂ) *
        z ^ (d * N)) =O[atTop] (fun N : ℕ => R ^ (d * N)) := by
    refine (powerSum_comp_isBigO atTop (fun N => d * N) H1 hR hH1).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hid N hN).symm
  have hzero := coeff_eq_zero_of_nonneg_ap T
    (fun z => (Nm.count z : ℝ) + H2.count z - ((if z ∈ s then e z else 0 : ℤ) : ℝ)) hR hd hc hbig
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  have h0 : (Nm.count x : ℝ) + H2.count x - ((if x ∈ s then e x else 0 : ℤ) : ℝ) = 0 :=
    hzero x (hNT (Multiset.mem_toFinset.2 hx)) hlt
  have hcount : (1 : ℝ) ≤ Nm.count x := by
    exact_mod_cast Multiset.one_le_count_iff_mem.2 hx
  by_cases hxs : x ∈ s
  · have h2 : ((e x : ℤ) : ℝ) ≤ H2.count x := by exact_mod_cast he x hxs hlt
    rw [if_pos hxs] at h0
    linarith
  · have h2 : (0 : ℝ) ≤ H2.count x := Nat.cast_nonneg _
    rw [if_neg hxs, Int.cast_zero] at h0
    linarith

/-- **(d)**, the N4 matching conclusion (S4_DESIGN.md §6 (IV)) for all `m ≥ 1`. -/
theorem multiset_norm_le_of_trace_identity (Nm H1 H2 : Multiset ℂ) (s : Finset ℂ)
    (e : ℂ → ℤ) {R : ℝ} (hR : 0 ≤ R) (hH1 : ∀ x ∈ H1, ‖x‖ ≤ R)
    (he : ∀ z ∈ s, R < ‖z‖ → e z ≤ H2.count z)
    (h : ∀ m : ℕ, 1 ≤ m → (Nm.map (· ^ m)).sum =
      (H1.map (· ^ m)).sum - (H2.map (· ^ m)).sum + ∑ z ∈ s, (e z : ℂ) * z ^ m) :
    ∀ x ∈ Nm, ‖x‖ ≤ R :=
  multiset_norm_le_of_trace_identity_ap Nm H1 H2 s e hR one_pos hH1 he
    fun N hN => by simpa only [one_mul] using h N hN

/-! ### Sanity checks -/

/-- `2 ^ m` is not `O(1 ^ m)`. -/
theorem sanity_two_pow_not_isBigO_one :
    ¬ (fun m : ℕ => (2 : ℂ) ^ m) =O[atTop] (fun m : ℕ => (1 : ℝ) ^ m) := by
  intro h
  have := norm_le_of_pow_isBigO zero_le_one h
  norm_num at this

/-- Vanishing on the explicit set `{1, 2}`. -/
theorem sanity_vanish_one_two (a b : ℂ) (h : ∀ m : ℕ, 1 ≤ m → a + b * 2 ^ m = 0) :
    a = 0 ∧ b = 0 := by
  have h21 : (2 : ℂ) ≠ 1 := by norm_num
  have key := expSum_coeff_eq_zero ({1, 2} : Finset ℂ) (fun z => if z = 1 then a else b)
    (by norm_num) fun m hm => by
      rw [Finset.sum_pair (Ne.symm h21)]
      simpa [h21] using h m hm
  exact ⟨by simpa using key 1 (by simp), by simpa [h21] using key 2 (by simp)⟩

/-- Why the progression lemmas use grouped coefficients: along odd `m` the bases `2` and `-2`
cancel, so `∑_{z ∈ {2, -2}} z ^ (2N+1) = 0 = O(1)` although `|±2| > 1`. -/
theorem sanity_ap_cancel (N : ℕ) : (2 : ℂ) ^ (2 * N + 1) + (-2) ^ (2 * N + 1) = 0 := by
  rw [Odd.neg_pow ⟨N, rfl⟩]
  ring

/-- Sign form on `{3}`: `n * 3 ^ m = O(2 ^ m)` forces `n = 0`. -/
theorem sanity_sign (n : ℕ)
    (h : (fun m : ℕ => (n : ℂ) * 3 ^ m) =O[atTop] (fun m : ℕ => (2 : ℝ) ^ m)) : n = 0 :=
  (sign_form {3} (fun _ => n) (fun _ => 0) (R := 2) (by norm_num) (by simpa using h) 3 (by simp)
    (by norm_num)).1

/-- Multiset form on singletons. -/
theorem sanity_multiset (x : ℂ) (hx : x ≠ 0) (h : ∀ m : ℕ, 1 ≤ m → x ^ m = 2 ^ m) : x = 2 := by
  have := multiset_eq_of_powerSum_eq {x} {2}
    (fun h0 => hx (Multiset.mem_singleton.1 h0).symm) (by norm_num)
    fun m hm => by simpa using h m hm
  simpa using this

/-- The k = 2 shape of the N4 conclusion: `2 ^ m = 2 ^ m - 3 ^ m + 1 * 3 ^ m` with
`e 3 = 1 ≤ h2 3`. -/
theorem sanity_trace_identity_wt2 : ∀ x ∈ ({2} : Multiset ℂ), ‖x‖ ≤ 2 :=
  multiset_norm_le_of_trace_identity {2} {2} {3} {3} (fun _ => 1) (by norm_num)
    (fun x hx => by rw [Multiset.mem_singleton] at hx; subst hx; norm_num)
    (fun z hz _ => by rw [Finset.mem_singleton] at hz; subst hz; simp) fun m _ => by simp

end RamanujanPetersson.ExpSum


