-- Prove2me | Definitions.Def_RPLib_F2_001
-- name    : RPLib_F2_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T02:50:08.583195+00:00
-- url     : https://prove2.me/theorems/ca99588d-d586-4b1c-bccd-35ae42570435
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 001 of 70
-- statement:
--   File 001 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S3.ExpSum`: Exponential polynomials: uniqueness, growth and sign lemmas
--   * `S3.Places_A`: 1. Cardinality of quotients of Dedekind domains and of free modules over PIDs
--   * `S3.Places_B`: 4. Function fields over `Fq`: the two rings of places
--   * `S3.Places_C`: 8. Functions without poles are constants
--   * `S3.RR_A`: Riemann-Roch, part A: the abstract repartition (adele) calculus
--   * `S3.RR_B`: Riemann-Roch, part B: the index formula, Weil differentials and the Riemann-Roch theorem
--   * `S3.RR_C`: Riemann-Roch, part C: the concrete instance for function fields
--   * `S3.RR_D`: Riemann-Roch, part D: the pole-divisor family and constant field extensions
--   * `S3.SB_Core`: Stepanov-Bombieri, abstract core (twisted form)
--   * `S3.SB_Count`: Twisted orbit counting (obligation E2, abstract part)
--   * `S3.SB_Transport`: Transport of places along automorphisms of a function field (obligation O1)
--   * `S3.SB_GalA`: S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound
--   * `S3.SB_GalB`: S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`
--   * `S3.SB_GalC`: S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field
--   * `S3.SB_Upper`: S3-ZetaSB, D1: the Galois-twist upper bound
--   * `S3.Zeta_A`: S3-ZetaSB, O5 part A: effective divisors and the Newton identity
--   * `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib

/-!
# Ramanujan-Petersson curve library (flat edition), file 001 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S3.ExpSum`: Exponential polynomials: uniqueness, growth and sign lemmas
* `S3.Places_A`: 1. Cardinality of quotients of Dedekind domains and of free modules over PIDs
* `S3.Places_B`: 4. Function fields over `Fq`: the two rings of places
* `S3.Places_C`: 8. Functions without poles are constants
* `S3.RR_A`: Riemann-Roch, part A: the abstract repartition (adele) calculus
* `S3.RR_B`: Riemann-Roch, part B: the index formula, Weil differentials and the Riemann-Roch theorem
* `S3.RR_C`: Riemann-Roch, part C: the concrete instance for function fields
* `S3.RR_D`: Riemann-Roch, part D: the pole-divisor family and constant field extensions
* `S3.SB_Core`: Stepanov-Bombieri, abstract core (twisted form)
* `S3.SB_Count`: Twisted orbit counting (obligation E2, abstract part)
* `S3.SB_Transport`: Transport of places along automorphisms of a function field (obligation O1)
* `S3.SB_GalA`: S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound
* `S3.SB_GalB`: S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`
* `S3.SB_GalC`: S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field
* `S3.SB_Upper`: S3-ZetaSB, D1: the Galois-twist upper bound
* `S3.Zeta_A`: S3-ZetaSB, O5 part A: effective divisors and the Newton identity
* `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
-/

set_option autoImplicit false

-- ===== S3.ExpSum =====
section

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

/-! ### (b) Growth -/

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

/-! ### Sanity checks -/

end RamanujanPetersson.ExpSum


end

-- ===== S3.Places_A =====
section

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 1. Cardinality of quotients of Dedekind domains and of free modules over PIDs -/

section CardQuot

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Infinite S]

/-- `I ↦ Nat.card (S ⧸ I)` is multiplicative on an infinite Dedekind domain. -/
theorem cardQuot_mul' (I J : Ideal S) :
    Submodule.cardQuot (I * J) = Submodule.cardQuot I * Submodule.cardQuot J :=
  UniqueFactorizationMonoid.multiplicative_of_coprime Submodule.cardQuot I J
    (Submodule.cardQuot_bot _ _)
    (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
    (fun {I} i hI =>
      have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
      cardQuot_pow_of_prime hI.ne_zero)
    fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.isUnit_iff.mp
        (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

variable (S) in
/-- The cardinality of the quotient, as a monoid-with-zero hom on ideals. -/
def cardHom : Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := cardQuot_mul' I J
  map_one' := by rw [Ideal.one_eq_top, Submodule.cardQuot_top]
  map_zero' := by rw [Ideal.zero_eq_bot, Submodule.cardQuot_bot]

theorem cardHom_apply (I : Ideal S) : cardHom S I = Nat.card (S ⧸ I) :=
  Submodule.cardQuot_apply I

end CardQuot

section NormCard

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Infinite A]
variable {S : Type*} [CommRing S] [IsDomain S] [Algebra A S] [Module.Free A S] [Module.Finite A S]

/-- For `S` free of finite rank over a PID `A`: `#(S ⧸ a) = #(A ⧸ N(a))`. -/
theorem card_quot_eq_card_quot_norm (a : S) (ha : a ≠ 0) :
    Nat.card (S ⧸ Ideal.span {a}) = Nat.card (A ⧸ Ideal.span {Algebra.norm A a}) := by
  classical
  set N : Submodule A S := (Ideal.span {a}).restrictScalars A with hN
  have hmem : ∀ x : S, a * x ∈ N := fun x =>
    Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self a)
  let e0 : S →ₗ[A] N :=
    { toFun := fun x => ⟨a * x, hmem x⟩
      map_add' := fun x y => by ext; simp [mul_add]
      map_smul' := fun c x => by ext; simp }
  have e0bij : Function.Bijective e0 := by
    constructor
    · intro x y hxy
      have : a * x = a * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ ha this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      exact ⟨x, by ext; simp [e0, mul_comm]⟩
  let e : S ≃ₗ[A] N := LinearEquiv.ofBijective e0 e0bij
  have hdet : LinearMap.det (N.subtype ∘ₗ (e : S →ₗ[A] N)) = Algebra.norm A a := by
    rw [Algebra.norm_apply]
    congr 1
  let b := Module.Free.chooseBasis A S
  have h : Module.finrank A N = Module.finrank A S := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : S ≃ₗ[A] N := b'.equiv ab (Equiv.refl _)
  let f : S →ₗ[A] S := N.subtype.comp (e' : S →ₗ[A] N)
  have hf : ∀ i, f (b' i) = c i • b' i := by
    intro i
    show ((b'.equiv ab (Equiv.refl _)) (b' i) : S) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, hf, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (Algebra.norm A a) (∏ i, c i) := by
    rw [← hdet, ← hdetf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  calc Nat.card (S ⧸ Ideal.span {a}) = Nat.card (S ⧸ N) :=
        Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {a})).toEquiv.symm
    _ = Nat.card (Π i, A ⧸ Ideal.span ({c i} : Set A)) :=
        Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
    _ = ∏ i, Nat.card (A ⧸ Ideal.span ({c i} : Set A)) := Nat.card_pi
    _ = ∏ i, cardHom A (Ideal.span ({c i} : Set A)) := by simp only [cardHom_apply]
    _ = cardHom A (Ideal.span ({∏ i, c i} : Set A)) := by
        rw [← Ideal.prod_span_singleton, map_prod]
    _ = Nat.card (A ⧸ Ideal.span {Algebra.norm A a}) := by
        rw [cardHom_apply, Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm]

end NormCard

section PolyCard

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem card_polyQuot {g : Fq[X]} (hg : g ≠ 0) :
    Nat.card (Fq[X] ⧸ Ideal.span {g}) = Fintype.card Fq ^ g.natDegree := by
  let pb := AdjoinRoot.powerBasis hg
  have : Module.Finite Fq (AdjoinRoot g) := pb.finite
  have h1 := Module.natCard_eq_pow_finrank (K := Fq) (V := AdjoinRoot g)
  rw [pb.finrank, AdjoinRoot.powerBasis_dim, Nat.card_eq_fintype_card (α := Fq)] at h1
  exact h1

end PolyCard

/-! ## 2. The valuation ring at infinity of `Fq(x)` -/

section Oinf

variable (Fq : Type*) [Field Fq] [DecidableEq (RatFunc Fq)]

/-- The valuation ring of `Fq(x)` at `x = ∞`: `{f : deg num f ≤ deg den f}`. -/
abbrev Oinf : ValuationSubring (RatFunc Fq) := (RatFunc.inftyValuation Fq).valuationSubring

theorem mem_Oinf_iff (f : RatFunc Fq) : f ∈ Oinf Fq ↔ RatFunc.inftyValuation Fq f ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

theorem inftyValuation_eq_exp {f : RatFunc Fq} (hf : f ≠ 0) :
    RatFunc.inftyValuation Fq f = WithZero.exp f.intDegree := by
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero Fq hf]

theorem mem_Oinf_iff' {f : RatFunc Fq} (hf : f ≠ 0) : f ∈ Oinf Fq ↔ f.intDegree ≤ 0 := by
  rw [mem_Oinf_iff, inftyValuation_eq_exp Fq hf, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem algebraMap_mem_Oinf (c : Fq) : algebraMap Fq (RatFunc Fq) c ∈ Oinf Fq := by
  rw [mem_Oinf_iff]
  by_cases hc : c = 0
  · simp [hc]
  · rw [RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C Fq hc]

instance : Algebra Fq (Oinf Fq) :=
  RingHom.toAlgebra ((algebraMap Fq (RatFunc Fq)).codRestrict (Oinf Fq) (algebraMap_mem_Oinf Fq))

@[simp] theorem coe_algebraMap_Oinf (c : Fq) :
    ((algebraMap Fq (Oinf Fq) c : Oinf Fq) : RatFunc Fq) = algebraMap Fq (RatFunc Fq) c := rfl

instance : IsScalarTower Fq (Oinf Fq) (RatFunc Fq) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The uniformizer `1/x` of `Oinf`. -/
def piInf : Oinf Fq := ⟨1 / RatFunc.X, by
  rw [mem_Oinf_iff, RatFunc.inftyValuation.X_inv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num⟩

@[simp] theorem coe_piInf : ((piInf Fq : Oinf Fq) : RatFunc Fq) = 1 / RatFunc.X := rfl

theorem X_ne_zero' : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero

theorem intDegree_div_polys {p d : Fq[X]} (hp : p ≠ 0) (hd : d ≠ 0) :
    RatFunc.intDegree (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      (p.natDegree : ℤ) - d.natDegree := by
  have hp' : algebraMap Fq[X] (RatFunc Fq) p ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hp
  have hd' : (algebraMap Fq[X] (RatFunc Fq) d)⁻¹ ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hd
  rw [div_eq_mul_inv, RatFunc.intDegree_mul hp' hd', RatFunc.intDegree_inv,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_eq_add_neg]

theorem mem_span_piInf_iff (z : Oinf Fq) :
    z ∈ Ideal.span {piInf Fq} ↔ (z : RatFunc Fq) = 0 ∨ RatFunc.intDegree (z : RatFunc Fq) < 0 := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨w, rfl⟩
    by_cases hw : (w : RatFunc Fq) = 0
    · left; simp [hw]
    · right
      have hw' := (mem_Oinf_iff' Fq hw).mp w.2
      simp only [MulMemClass.coe_mul, coe_piInf]
      rw [RatFunc.intDegree_mul hw (by simpa using X_ne_zero' Fq), one_div, RatFunc.intDegree_inv,
        RatFunc.intDegree_X]
      omega
  · rintro (h | h)
    · exact ⟨0, by ext; simp [h]⟩
    · have hz : (z : RatFunc Fq) ≠ 0 := fun h0 => by simp [h0] at h
      have hzX : (z : RatFunc Fq) * RatFunc.X ∈ Oinf Fq := by
        rw [mem_Oinf_iff' Fq (mul_ne_zero hz (X_ne_zero' Fq)),
          RatFunc.intDegree_mul hz (X_ne_zero' Fq), RatFunc.intDegree_X]
        omega
      refine ⟨⟨_, hzX⟩, ?_⟩
      ext
      simp only [MulMemClass.coe_mul, coe_piInf]
      field_simp [X_ne_zero' Fq]

theorem algebraMap_mem_span_piInf_iff (c : Fq) :
    algebraMap Fq (Oinf Fq) c ∈ Ideal.span {piInf Fq} ↔ c = 0 := by
  rw [mem_span_piInf_iff]
  constructor
  · rintro (h | h)
    · simpa using h
    · rw [coe_algebraMap_Oinf, RatFunc.algebraMap_eq_C, RatFunc.intDegree_C] at h
      exact absurd h (lt_irrefl 0)
  · rintro rfl; left; simp

theorem exists_sub_mem_span_piInf (z : Oinf Fq) :
    ∃ c : Fq, z - algebraMap Fq (Oinf Fq) c ∈ Ideal.span {piInf Fq} := by
  set f : RatFunc Fq := (z : RatFunc Fq) with hfz
  by_cases hf : f = 0
  · exact ⟨0, by rw [map_zero, sub_zero, mem_span_piInf_iff]; left; exact hf⟩
  have hdeg := (mem_Oinf_iff' Fq hf).mp z.2
  have hle : f.num.natDegree ≤ f.denom.natDegree := by
    have : f.intDegree = (f.num.natDegree : ℤ) - f.denom.natDegree := rfl
    omega
  set d := f.denom.natDegree
  set c := f.num.coeff d
  refine ⟨c, ?_⟩
  rw [mem_span_piInf_iff]
  set p : Fq[X] := f.num - C c * f.denom with hp
  have hden0 : f.denom ≠ 0 := f.denom_ne_zero
  have hrepr : ((z - algebraMap Fq (Oinf Fq) c : Oinf Fq) : RatFunc Fq) =
      algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) f.denom := by
    have hden' : algebraMap Fq[X] (RatFunc Fq) f.denom ≠ 0 := by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hden0
    rw [hp, map_sub, map_mul, sub_div, mul_div_assoc, div_self hden', mul_one, RatFunc.num_div_denom]
    simp [f, RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C]
  rw [hrepr]
  by_cases hp0 : p = 0
  · left; simp [hp0]
  right
  rw [intDegree_div_polys Fq hp0 hden0]
  have hmon : f.denom.Monic := f.monic_denom
  have hlt : p.natDegree < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · exfalso; apply hp0
      have h1 : f.denom = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hd0
      have h2 : f.num = C c := by
        rw [Polynomial.eq_C_of_natDegree_le_zero (by omega : f.num.natDegree ≤ 0)]
        simp [c, hd0]
      rw [hp, h1, h2, mul_one, sub_self]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hp0, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [hp, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le hm with h | h
      · subst h; rw [hmon.coeff_natDegree]; simp [c, d]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
  omega

/-- The residue map `Fq → Oinf ⧸ (1/x)` is a bijection. -/
theorem residue_bijective :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {piInf Fq})).comp (algebraMap Fq (Oinf Fq))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hc
    exact (algebraMap_mem_span_piInf_iff Fq c).mp hc
  · intro w
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c, hc⟩ := exists_sub_mem_span_piInf Fq z
    exact ⟨c, by rw [RingHom.comp_apply, Ideal.Quotient.eq]; rw [← neg_mem_iff, neg_sub]; exact hc⟩

theorem piInf_ne_zero : piInf Fq ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp [X_ne_zero' Fq] at this

theorem span_piInf_isMaximal : (Ideal.span {piInf Fq}).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (RingEquiv.ofBijective _ (residue_bijective Fq)).symm.toMulEquiv.isField (Field.toIsField Fq)

instance : Infinite (Oinf Fq) := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact IsDiscreteValuationRing.not_isField (Oinf Fq) (Finite.isField_of_domain (Oinf Fq))

variable [Fintype Fq]

theorem card_residue : Nat.card (Oinf Fq ⧸ Ideal.span {piInf Fq}) = Fintype.card Fq := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective _ (residue_bijective Fq))).symm

/-- The order at infinity of a nonzero element of `Oinf` is `-intDegree`. -/
theorem span_eq_pow {y : Oinf Fq} (hy : y ≠ 0) :
    Ideal.span {y} = Ideal.span {piInf Fq} ^ (-(y : RatFunc Fq).intDegree).toNat := by
  set n := (-(y : RatFunc Fq).intDegree).toNat
  have hy' : (y : RatFunc Fq) ≠ 0 := fun h => hy (Subtype.ext h)
  have hdeg := (mem_Oinf_iff' Fq hy').mp y.2
  have hn : (n : ℤ) = -(y : RatFunc Fq).intDegree := Int.toNat_of_nonneg (by omega)
  have hXn : (RatFunc.X ^ n : RatFunc Fq).intDegree = n := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_pow]
  have hu0 : (y : RatFunc Fq) * RatFunc.X ^ n ≠ 0 := mul_ne_zero hy' (pow_ne_zero _ (X_ne_zero' Fq))
  have hudeg : ((y : RatFunc Fq) * RatFunc.X ^ n).intDegree = 0 := by
    rw [RatFunc.intDegree_mul hy' (pow_ne_zero _ (X_ne_zero' Fq)), hXn]
    omega
  have hu : (y : RatFunc Fq) * RatFunc.X ^ n ∈ Oinf Fq := (mem_Oinf_iff' Fq hu0).mpr hudeg.le
  have hui : ((y : RatFunc Fq) * RatFunc.X ^ n)⁻¹ ∈ Oinf Fq :=
    (mem_Oinf_iff' Fq (inv_ne_zero hu0)).mpr (by rw [RatFunc.intDegree_inv, hudeg]; simp)
  let u : Oinf Fq := ⟨_, hu⟩
  have h1 : u * ⟨_, hui⟩ = 1 := by
    ext
    show ((y : RatFunc Fq) * RatFunc.X ^ n) * ((y : RatFunc Fq) * RatFunc.X ^ n)⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  have hunit : IsUnit u := isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hyu : y = u * piInf Fq ^ n := by
    ext
    simp only [u, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_piInf]
    rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (X_ne_zero' Fq)), mul_one]
  rw [hyu, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit hunit]

theorem span_piInf_ne_bot : Ideal.span {piInf Fq} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact piInf_ne_zero Fq

/-- `#(Oinf ⧸ y) = q ^ (-intDegree y)`. -/
theorem card_quot_Oinf {y : Oinf Fq} (hy : y ≠ 0) :
    Nat.card (Oinf Fq ⧸ Ideal.span {y}) = Fintype.card Fq ^ (-(y : RatFunc Fq).intDegree).toNat := by
  have : (Ideal.span {piInf Fq}).IsPrime := (span_piInf_isMaximal Fq).isPrime
  rw [span_eq_pow Fq hy, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime (span_piInf_ne_bot Fq),
    Submodule.cardQuot_apply, card_residue]

end Oinf

/-! ## 3. Places of a Dedekind domain with finite residue rings: degree, order, divisors -/

section Generic

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra Fq S]

/-- Every nonzero principal ideal has finite index. -/
class FiniteQuot : Prop where
  finite : ∀ a : S, a ≠ 0 → Finite (S ⧸ Ideal.span {a})

variable {S}

/-- The degree of a place: the `Fq`-dimension of its residue field. -/
def deg (P : HeightOneSpectrum S) : ℕ := Module.finrank Fq (S ⧸ P.asIdeal)

variable [FiniteQuot S]

instance finite_residue (P : HeightOneSpectrum S) : Finite (S ⧸ P.asIdeal) := by
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := FiniteQuot.finite (S := S) a ha0
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))

instance moduleFinite_residue (P : HeightOneSpectrum S) : Module.Finite Fq (S ⧸ P.asIdeal) :=
  Module.Finite.of_finite

theorem card_residue_eq (P : HeightOneSpectrum S) :
    Nat.card (S ⧸ P.asIdeal) = Fintype.card Fq ^ deg Fq P := by
  rw [Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card (α := Fq)]; rfl

theorem deg_pos (P : HeightOneSpectrum S) : 0 < deg Fq P := by
  have : Nontrivial (S ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
  exact Module.finrank_pos

variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K]

/-- The order of `f` at `P` (`0` for `f = 0`). -/
def ord (P : HeightOneSpectrum S) (f : K) : ℤ := -WithZero.log (P.valuation K f)

/-- The multiplicity of `P` in the ideal `(a)`. -/
def cnt (P : HeightOneSpectrum S) (a : S) : ℕ :=
  (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a})).factors

theorem ord_algebraMap (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    ord P (algebraMap S K a) = cnt P a := by
  rw [ord, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg ha,
    WithZero.log_exp, neg_neg, cnt]

@[simp] theorem ord_zero (P : HeightOneSpectrum S) : ord P (0 : K) = 0 := by simp [ord]

theorem ord_mul (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem ord_div (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f / g) = ord P f - ord P g := by
  rw [ord, ord, ord, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem finite_cnt {a : S} (ha : a ≠ 0) : {P : HeightOneSpectrum S | cnt P a ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.mp (Associates.finite_factors (I := Ideal.span {a})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]))
  refine h.subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, cnt] at hP ⊢
  exact_mod_cast hP

theorem finite_ord (f : K) : {P : HeightOneSpectrum S | ord P f ≠ 0}.Finite := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have ha' : algebraMap S K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr ha0
  have hb' : algebraMap S K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S K)).mpr hb0
  refine ((finite_cnt ha0).union (finite_cnt hb0)).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hP ⊢
  rw [ord_div P ha' hb', ord_algebraMap P ha0, ord_algebraMap P hb0] at hP
  by_contra hcon
  push Not at hcon
  rw [hcon.1, hcon.2] at hP
  simp at hP

variable (S) in
/-- The divisor of `f` restricted to the places of `S`. -/
def divS (f : K) : HeightOneSpectrum S →₀ ℤ :=
  Finsupp.ofSupportFinite (fun P => ord P f) (finite_ord f)

@[simp] theorem divS_apply (f : K) (P : HeightOneSpectrum S) : divS S f P = ord P f := rfl

/-- Degree of a divisor supported on the places of `S`. -/
def degS (D : HeightOneSpectrum S →₀ ℤ) : ℤ := D.sum fun P n => n * (deg Fq P : ℤ)

theorem degS_sub (D E : HeightOneSpectrum S →₀ ℤ) : degS Fq (D - E) = degS Fq D - degS Fq E := by
  unfold degS
  rw [Finsupp.sum_sub_index]
  intro P a b; ring

theorem divS_div {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : divS S (f / g) = divS S f - divS S g := by
  ext P; simp [ord_div P hf hg]

variable [Infinite S]

/-- `#(S ⧸ a) = q ^ (Σ_P cnt_P(a) deg P)`. -/
theorem card_quot_eq_pow {a : S} (ha : a ≠ 0) :
    Nat.card (S ⧸ Ideal.span {a}) = Fintype.card Fq ^
      (∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg Fq P) := by
  have hI : Ideal.span {a} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rw [← cardHom_apply, ← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [show cardHom S (∏ᶠ v : HeightOneSpectrum S, v.maxPowDividing (Ideal.span {a})) =
      (cardHom S : Ideal S →* ℕ) (∏ᶠ v : HeightOneSpectrum S, v.maxPowDividing (Ideal.span {a}))
      from rfl, MonoidHom.map_finprod _ (Ideal.hasFiniteMulSupport hI)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_cnt ha).toFinset)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun P _ => ?_
    simp only [MonoidHom.coe_coe, HeightOneSpectrum.maxPowDividing, map_pow, cardHom_apply,
      card_residue_eq Fq P, ← pow_mul, cnt, mul_comm]
  · intro P hP
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hP
    simp [HeightOneSpectrum.maxPowDividing, cnt] at h0 ⊢
    simp [h0]

theorem degS_divS_algebraMap {a : S} (ha : a ≠ 0) :
    degS Fq (divS S (algebraMap S K a)) =
      ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg Fq P : ℕ) : ℤ) := by
  unfold degS
  rw [Finsupp.sum_of_support_subset (s := (finite_cnt ha).toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [divS_apply, ord_algebraMap P ha]
  · intro P hP
    simp only [Finsupp.mem_support_iff, divS_apply, ord_algebraMap P ha] at hP
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    exact_mod_cast hP
  · intro P _; simp

end Generic

end RamanujanPetersson.Places

end

end

-- ===== S3.Places_B =====
section

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 4. Function fields over `Fq`: the two rings of places -/

section FunctionFieldSetup

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

instance isScalarTower_ratFunc : IsScalarTower Fq (RatFunc Fq) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply Fq Fq[X] F, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F,
      ← IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq)]

instance isScalarTower_Oinf : IsScalarTower Fq (Oinf Fq) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F]
    exact IsScalarTower.algebraMap_apply Fq (RatFunc Fq) F c

/-- The ring of functions regular away from `x = ∞` (finite places). -/
abbrev Rfin : Type _ := FunctionField.ringOfIntegers Fq F

/-- The ring of functions regular at all places over `x = ∞` (infinite places). -/
abbrev Rinf : Type _ := integralClosure (Oinf Fq) F

instance : IsDedekindDomain (Rinf Fq F) := integralClosure.isDedekindDomain (Oinf Fq) (RatFunc Fq) F

instance : IsFractionRing (Rinf Fq F) F := integralClosure.isFractionRing_of_finite_extension (RatFunc Fq) F

instance : Module.Finite (Oinf Fq) (Rinf Fq F) := IsIntegralClosure.finite (Oinf Fq) (RatFunc Fq) F _

instance : Module.Free (Oinf Fq) (Rinf Fq F) := IsIntegralClosure.module_free (Oinf Fq) (RatFunc Fq) F _

instance faithfulSMul_poly : FaithfulSMul Fq[X] F :=
  (faithfulSMul_iff_algebraMap_injective Fq[X] F).mpr (by
    rw [IsScalarTower.algebraMap_eq Fq[X] (RatFunc Fq) F]
    exact (algebraMap (RatFunc Fq) F).injective.comp (IsFractionRing.injective Fq[X] (RatFunc Fq)))

instance : Module.Free Fq[X] (Rfin Fq F) := IsIntegralClosure.module_free Fq[X] (RatFunc Fq) F _

instance : Module.Finite Fq[X] (Rfin Fq F) := IsIntegralClosure.finite Fq[X] (RatFunc Fq) F _

instance : Infinite (Rfin Fq F) :=
  Infinite.of_injective _ (FunctionField.ringOfIntegers.algebraMap_injective Fq F)

theorem algebraMap_Oinf_Rinf_injective : Function.Injective (algebraMap (Oinf Fq) (Rinf Fq F)) := by
  intro a b h
  have h2 : algebraMap (Oinf Fq) F a = algebraMap (Oinf Fq) F b := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F,
    IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) F b] at h2
  exact Subtype.ext ((algebraMap (RatFunc Fq) F).injective h2)

instance : Infinite (Rinf Fq F) := Infinite.of_injective _ (algebraMap_Oinf_Rinf_injective Fq F)

instance : FiniteQuot (Rfin Fq F) where
  finite a ha := by
    have hN : Algebra.norm Fq[X] a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    apply Nat.finite_of_card_ne_zero
    rw [card_quot_eq_card_quot_norm (A := Fq[X]) a ha, card_polyQuot hN]
    exact pow_ne_zero _ Fintype.card_ne_zero

instance : FiniteQuot (Rinf Fq F) where
  finite a ha := by
    have hN : Algebra.norm (Oinf Fq) a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    apply Nat.finite_of_card_ne_zero
    rw [card_quot_eq_card_quot_norm (A := Oinf Fq) a ha, card_quot_Oinf Fq hN]
    exact pow_ne_zero _ Fintype.card_ne_zero

/-! ### Norm bridge -/

theorem norm_bridge_fin (a : Rfin Fq F) :
    algebraMap Fq[X] (RatFunc Fq) (Algebra.norm Fq[X] a) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a) := by
  have := IsIntegralClosure.isLocalization Fq[X] (RatFunc Fq) F (Rfin Fq F)
  exact (Algebra.norm_localization Fq[X] (nonZeroDivisors Fq[X]) (Rₘ := RatFunc Fq) (Sₘ := F) a).symm

theorem norm_bridge_inf (c : Rinf Fq F) :
    ((Algebra.norm (Oinf Fq) c : Oinf Fq) : RatFunc Fq) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c) := by
  have := IsIntegralClosure.isLocalization (Oinf Fq) (RatFunc Fq) F (Rinf Fq F)
  exact (Algebra.norm_localization (Oinf Fq) (nonZeroDivisors (Oinf Fq)) (Rₘ := RatFunc Fq) (Sₘ := F) c).symm

theorem two_le_card : 2 ≤ Fintype.card Fq := Fintype.one_lt_card

/-- Finite part: `deg (div a)|_fin = deg_x N(a)`. -/
theorem degS_fin {a : Rfin Fq F} (ha : a ≠ 0) :
    degS Fq (divS (Rfin Fq F) (algebraMap (Rfin Fq F) F a)) =
      (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a)).intDegree := by
  have hN : Algebra.norm Fq[X] a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have h1 := card_quot_eq_pow Fq (S := Rfin Fq F) ha
  rw [card_quot_eq_card_quot_norm (A := Fq[X]) a ha, card_polyQuot hN] at h1
  have h2 := Nat.pow_right_injective (two_le_card Fq) h1
  rw [degS_divS_algebraMap Fq ha, ← h2, ← norm_bridge_fin, RatFunc.intDegree_polynomial]

/-- Infinite part: `deg (div c)|_inf = -deg_x N(c)`. -/
theorem degS_inf {c : Rinf Fq F} (hc : c ≠ 0) :
    degS Fq (divS (Rinf Fq F) (algebraMap (Rinf Fq F) F c)) =
      -(Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c)).intDegree := by
  have hN : Algebra.norm (Oinf Fq) c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
  have hN' : ((Algebra.norm (Oinf Fq) c : Oinf Fq) : RatFunc Fq) ≠ 0 := fun h => hN (Subtype.ext h)
  have h1 := card_quot_eq_pow Fq (S := Rinf Fq F) hc
  rw [card_quot_eq_card_quot_norm (A := Oinf Fq) c hc, card_quot_Oinf Fq hN] at h1
  have h2 := Nat.pow_right_injective (two_le_card Fq) h1
  have hle := (mem_Oinf_iff' Fq hN').mp (Algebra.norm (Oinf Fq) c).2
  rw [degS_divS_algebraMap Fq hc, ← h2, ← norm_bridge_inf]
  omega

/-- The product formula, split into the finite and the infinite places. -/
theorem degS_fin_add_degS_inf {f : F} (hf : f ≠ 0) :
    degS Fq (divS (Rfin Fq F) f) + degS Fq (divS (Rinf Fq F) f) = 0 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Rfin Fq F) f
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (Rinf Fq F) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hf hab.symm
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd; exact hf hcd.symm
  have inj1 := IsFractionRing.injective (Rfin Fq F) F
  have inj2 := IsFractionRing.injective (Rinf Fq F) F
  have ha' : algebraMap (Rfin Fq F) F a ≠ 0 := (map_ne_zero_iff _ inj1).mpr ha0
  have hb' : algebraMap (Rfin Fq F) F b ≠ 0 := (map_ne_zero_iff _ inj1).mpr hb0
  have hc' : algebraMap (Rinf Fq F) F c ≠ 0 := (map_ne_zero_iff _ inj2).mpr hc0
  have hd' : algebraMap (Rinf Fq F) F d ≠ 0 := (map_ne_zero_iff _ inj2).mpr hd0
  have e1 : Algebra.norm (RatFunc Fq) f * Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a) := by
    rw [← map_mul, ← hab, div_mul_cancel₀ _ hb']
  have e2 : Algebra.norm (RatFunc Fq) f * Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d) =
      Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c) := by
    rw [← map_mul, ← hcd, div_mul_cancel₀ _ hd']
  have nf : Algebra.norm (RatFunc Fq) f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  have nb : Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb'
  have nd : Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd'
  have i1 := congrArg RatFunc.intDegree e1
  have i2 := congrArg RatFunc.intDegree e2
  rw [RatFunc.intDegree_mul nf nb] at i1
  rw [RatFunc.intDegree_mul nf nd] at i2
  have p1 : degS Fq (divS (Rfin Fq F) f) =
      (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F a)).intDegree -
        (Algebra.norm (RatFunc Fq) (algebraMap (Rfin Fq F) F b)).intDegree := by
    rw [← hab, divS_div ha' hb', degS_sub, degS_fin Fq F ha0, degS_fin Fq F hb0]
  have p2 : degS Fq (divS (Rinf Fq F) f) =
      -(Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F c)).intDegree +
        (Algebra.norm (RatFunc Fq) (algebraMap (Rinf Fq F) F d)).intDegree := by
    rw [← hcd, divS_div hc' hd', degS_sub, degS_inf Fq F hc0, degS_inf Fq F hd0]; ring
  rw [p1, p2]
  omega

end FunctionFieldSetup

/-! ## 5. Places, divisors, principal divisors -/

section Divisors

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The places of `F` (relative to the chosen separating element `x`): the finite places
(`HeightOneSpectrum` of `Rfin`) and the places over `x = ∞` (`HeightOneSpectrum` of `Rinf`). -/
abbrev Place : Type _ := HeightOneSpectrum (Rfin Fq F) ⊕ HeightOneSpectrum (Rinf Fq F)

/-- Divisors: finitely supported `ℤ`-valued functions on places. -/
abbrev Divisor : Type _ := Place Fq F →₀ ℤ

variable {Fq F}

/-- The degree of a place over `Fq` (the `Fq`-dimension of its residue field). -/
def Place.deg : Place Fq F → ℕ :=
  Sum.elim (_root_.RamanujanPetersson.Places.deg Fq) (_root_.RamanujanPetersson.Places.deg Fq)

/-- The order of `f` at a place. -/
def Place.ord : Place Fq F → F → ℤ :=
  Sum.elim (fun P f => _root_.RamanujanPetersson.Places.ord P f)
    (fun P f => _root_.RamanujanPetersson.Places.ord P f)

@[simp] theorem Place.deg_inl (P : HeightOneSpectrum (Rfin Fq F)) :
    Place.deg (Sum.inl P : Place Fq F) = _root_.RamanujanPetersson.Places.deg Fq P := rfl
@[simp] theorem Place.deg_inr (P : HeightOneSpectrum (Rinf Fq F)) :
    Place.deg (Sum.inr P : Place Fq F) = _root_.RamanujanPetersson.Places.deg Fq P := rfl
@[simp] theorem Place.ord_inl (P : HeightOneSpectrum (Rfin Fq F)) (f : F) :
    Place.ord (Sum.inl P : Place Fq F) f = _root_.RamanujanPetersson.Places.ord P f := rfl
@[simp] theorem Place.ord_inr (P : HeightOneSpectrum (Rinf Fq F)) (f : F) :
    Place.ord (Sum.inr P : Place Fq F) f = _root_.RamanujanPetersson.Places.ord P f := rfl

theorem Place.deg_pos (P : Place Fq F) : 0 < P.deg := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.deg_pos Fq P, _root_.RamanujanPetersson.Places.deg_pos Fq P]

theorem Place.ord_mul (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f * g) = P.ord f + P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.ord_mul P hf hg, _root_.RamanujanPetersson.Places.ord_mul P hf hg]

theorem Place.ord_div (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f / g) = P.ord f - P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.Places.ord_div P hf hg, _root_.RamanujanPetersson.Places.ord_div P hf hg]

/-- The degree of a divisor. -/
def Divisor.deg (D : Divisor Fq F) : ℤ := D.sum fun P n => n * (P.deg : ℤ)

theorem Divisor.deg_add (D E : Divisor Fq F) : Divisor.deg (D + E) = D.deg + E.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem Divisor.deg_neg (D : Divisor Fq F) : Divisor.deg (-D) = -D.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Divisor.deg_sub (D E : Divisor Fq F) : Divisor.deg (D - E) = D.deg - E.deg := by
  rw [sub_eq_add_neg, Divisor.deg_add, Divisor.deg_neg, sub_eq_add_neg]

theorem Divisor.deg_single (P : Place Fq F) (n : ℤ) : Divisor.deg (Finsupp.single P n : Divisor Fq F) = n * P.deg := by
  unfold Divisor.deg
  rw [Finsupp.sum_single_index (by ring)]

theorem Divisor.deg_sumElim (D : HeightOneSpectrum (Rfin Fq F) →₀ ℤ)
    (E : HeightOneSpectrum (Rinf Fq F) →₀ ℤ) :
    Divisor.deg (D.sumElim E : Divisor Fq F) = degS Fq D + degS Fq E := by
  unfold Divisor.deg
  rw [Finsupp.sum_sumElim]
  rfl

/-- The principal divisor of `f` (the zero divisor for `f = 0`). -/
def div (f : F) : Divisor Fq F := (divS (Rfin Fq F) f).sumElim (divS (Rinf Fq F) f)

@[simp] theorem div_apply (f : F) (P : Place Fq F) : div f P = P.ord f := by
  rcases P with P | P <;> rfl

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f * g) : Divisor Fq F) = div f + div g := by
  ext P
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, P.ord_mul hf hg]

theorem div_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f / g) : Divisor Fq F) = div f - div g := by
  ext P
  simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, P.ord_div hf hg]

/-- **Product formula**: a nonzero function has as many zeros as poles, counted with degrees. -/
theorem deg_div {f : F} (hf : f ≠ 0) : Divisor.deg (div f : Divisor Fq F) = 0 := by
  rw [div, Divisor.deg_sumElim]
  exact degS_fin_add_degS_inf Fq F hf

end Divisors

/-! ## 6. The full constant field -/

section ConstantField

theorem moduleFinite_of_algHom (Fq : Type*) [Field Fq] {k S : Type*} [Field k] [Algebra Fq k]
    [CommRing S] [Algebra Fq S] (φ : k →ₐ[Fq] S) (P : Ideal S) [P.IsMaximal] [Finite (S ⧸ P)] :
    Module.Finite Fq k ∧ finrank Fq k ∣ finrank Fq (S ⧸ P) := by
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  let ψ : k →ₐ[Fq] S ⧸ P := (Ideal.Quotient.mkₐ Fq P).comp φ
  letI : Algebra k (S ⧸ P) := ψ.toRingHom.toAlgebra
  have : IsScalarTower Fq k (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : Module.Finite Fq (S ⧸ P) := Module.Finite.of_finite
  have : Module.Finite k (S ⧸ P) := Module.Finite.of_restrictScalars_finite Fq k (S ⧸ P)
  have : Module.Finite Fq k :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom Fq k (S ⧸ P)).toLinearMap
      (algebraMap k (S ⧸ P)).injective
  exact ⟨inferInstance, Dvd.intro _ (Module.finrank_mul_finrank Fq k (S ⧸ P))⟩

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The full constant field of `F`: the algebraic closure of `Fq` in `F`. -/
abbrev constField : IntermediateField Fq F := algebraicClosure Fq F

theorem isIntegral_of_mem_constField (c : constField Fq F) : IsIntegral Fq (c : F) :=
  (mem_algebraicClosure_iff.mp c.2).isIntegral

/-- Constants are regular at the finite places. -/
def constToRfin : constField Fq F →ₐ[Fq] Rfin Fq F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField Fq F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Constants are regular at the infinite places. -/
def constToRinf : constField Fq F →ₐ[Fq] Rinf Fq F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField Fq F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem not_isField_Rinf : ¬ IsField (Rinf Fq F) := by
  rw [← Algebra.IsIntegral.isField_iff_isField (algebraMap_Oinf_Rinf_injective Fq F)]
  exact IsDiscreteValuationRing.not_isField _

/-- There is at least one place over `x = ∞`. -/
theorem nonempty_infPlace : Nonempty (HeightOneSpectrum (Rinf Fq F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Rinf Fq F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_Rinf Fq F)⟩⟩

theorem finrank_constField_dvd (P : Place Fq F) : finrank Fq (constField Fq F) ∣ P.deg := by
  rcases P with P | P
  · haveI := P.isMaximal
    exact (moduleFinite_of_algHom Fq (constToRfin Fq F) P.asIdeal).2
  · haveI := P.isMaximal
    exact (moduleFinite_of_algHom Fq (constToRinf Fq F) P.asIdeal).2

instance finiteDimensional_constField : FiniteDimensional Fq (constField Fq F) := by
  obtain ⟨P⟩ := nonempty_infPlace Fq F
  have := P.isMaximal
  exact (moduleFinite_of_algHom Fq (constToRinf Fq F) P.asIdeal).1

/-- A place of degree one forces the full constant field to be `Fq`. -/
theorem constField_eq_bot_of_deg_one {P : Place Fq F} (h : P.deg = 1) : constField Fq F = ⊥ :=
  IntermediateField.finrank_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ finrank_constField_dvd Fq F P))

end ConstantField

/-! ## 7. Places of bounded degree; points with values in finite extensions of `Fq` -/

section FiniteFields

variable (Fq : Type*) [Field Fq] [Fintype Fq]

theorem pow_card_pow_eq {K : Type*} [Field K] [Fintype K] (x : K) (k : ℕ) :
    x ^ (Fintype.card K ^ k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, FiniteField.pow_card]

/-- An `Fq`-embedding of fields divides the degrees. -/
theorem finrank_dvd_of_algHom_field {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Module.Finite Fq L] (φ : K →ₐ[Fq] L) : finrank Fq K ∣ finrank Fq L := by
  letI : Algebra K L := φ.toRingHom.toAlgebra
  have : IsScalarTower Fq K L := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite Fq K L
  have : Module.Finite Fq K :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom Fq K L).toLinearMap (algebraMap K L).injective
  exact Dvd.intro _ (Module.finrank_mul_finrank Fq K L)

/-- A finite field of degree `d` over `Fq` has `d` embeddings into one of degree divisible by `d`. -/
theorem card_algHom_of_dvd {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Finite K] [Finite L] (h : finrank Fq K ∣ finrank Fq L) : Nat.card (K →ₐ[Fq] L) = finrank Fq K := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype L := Fintype.ofFinite L
  have : Module.Finite Fq K := Module.Finite.of_finite
  obtain ⟨k, hk⟩ := h
  have hcard : Fintype.card L = Fintype.card K ^ k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := Fq) (V := L), Module.natCard_eq_pow_finrank (K := Fq) (V := K), hk,
      pow_mul]
  have hL1 : 1 < Fintype.card L := Fintype.one_lt_card
  have hsplit : (X ^ Fintype.card L - X : L[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq L hL1]
    exact Finset.card_univ
  have hspl : ∀ x : K, (map (algebraMap Fq L) (minpoly Fq x)).Splits := by
    intro x
    apply Splits.of_dvd hsplit (FiniteField.X_pow_card_sub_X_ne_zero L hL1)
    have hd : minpoly Fq x ∣ (X ^ Fintype.card L - X : Fq[X]) := by
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hcard, pow_card_pow_eq, sub_self]
    simpa using Polynomial.map_dvd (algebraMap Fq L) hd
  rw [← AlgHom.card_of_splits Fq K L hspl]
  exact Nat.card_eq_fintype_card

theorem card_algHom_eq_zero {K L : Type*} [Field K] [Field L] [Algebra Fq K] [Algebra Fq L]
    [Module.Finite Fq L] (h : ¬ finrank Fq K ∣ finrank Fq L) : Nat.card (K →ₐ[Fq] L) = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun φ => h (finrank_dvd_of_algHom_field Fq φ)⟩

theorem finite_algHom {A B : Type*} [Ring A] [Ring B] [Algebra Fq A] [Algebra Fq B] [Finite A] [Finite B] :
    Finite (A →ₐ[Fq] B) :=
  Finite.of_injective _ DFunLike.coe_injective

end FiniteFields

section PointCount

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S] [FiniteQuot S]

/-- Places of a fixed degree are finite in number, as soon as some `t ∈ S` is not a root of any
`T ^ N - T` (`N ≥ 2`): a place of degree `d` contains `t ^ (q ^ d) - t`. -/
theorem finite_deg_eq_of {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t) (d : ℕ) :
    {P : HeightOneSpectrum S | deg Fq P = d}.Finite := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · convert Set.finite_empty
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => (deg_pos Fq P).ne' (h.trans hd)
  set N := Fintype.card Fq ^ d with hNdef
  have hq : 2 ≤ Fintype.card Fq := Fintype.one_lt_card
  have hN : 2 ≤ N := hq.trans (Nat.le_self_pow hd.ne' _)
  have h0 : t ^ N - t ≠ 0 := sub_ne_zero.mpr (ht N hN)
  have hI : Ideal.span {t ^ N - t} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow,
    sub_eq_zero]
  have := P.isMaximal
  letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (S ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (S ⧸ P.asIdeal) = N := by
    rw [← Nat.card_eq_fintype_card, card_residue_eq Fq P, hP]
  rw [← hc]
  exact FiniteField.pow_card _

theorem finite_deg_dvd_of {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t) {m : ℕ} (hm : m ≠ 0) :
    {P : HeightOneSpectrum S | deg Fq P ∣ m}.Finite :=
  (m.divisors.finite_toSet.biUnion fun d _ => finite_deg_eq_of Fq ht d).subset fun P hP =>
    Set.mem_biUnion (Nat.mem_divisors.mpr ⟨hP, hm⟩) rfl

variable [Infinite S] (L : Type*) [Field L] [Algebra Fq L] [Finite L]

theorem ker_ne_bot (φ : S →ₐ[Fq] L) : RingHom.ker φ ≠ ⊥ := by
  intro h
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr h
  have := Finite.of_injective φ hinj
  exact _root_.not_finite S

/-- The place cut out by an `L`-valued point. -/
def kerPlace (φ : S →ₐ[Fq] L) : HeightOneSpectrum S :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ker_ne_bot Fq L φ⟩

/-- The `L`-valued points with kernel `P` are the `Fq`-embeddings of the residue field at `P`. -/
def fiberEquiv (P : HeightOneSpectrum S) :
    {φ : S →ₐ[Fq] L // kerPlace Fq L φ = P} ≃ (S ⧸ P.asIdeal →ₐ[Fq] L) where
  toFun φ := Ideal.Quotient.liftₐ P.asIdeal φ.1 (fun a ha => by
    rw [← φ.2] at ha
    exact RingHom.mem_ker.mp ha)
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mkₐ Fq P.asIdeal), by
    have := P.isMaximal
    letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
    have hinj : Function.Injective ψ := ψ.toRingHom.injective
    apply HeightOneSpectrum.ext
    ext a
    change a ∈ RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ Fq P.asIdeal)) ↔ a ∈ P.asIdeal
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff ψ hinj,
      Ideal.Quotient.eq_zero_iff_mem]⟩
  left_inv φ := Subtype.ext (AlgHom.ext fun _ => rfl)
  right_inv ψ := Ideal.Quotient.algHom_ext Fq (AlgHom.ext fun _ => rfl)

theorem card_fiber (P : HeightOneSpectrum S) :
    Nat.card {φ : S →ₐ[Fq] L // kerPlace Fq L φ = P} =
      if deg Fq P ∣ finrank Fq L then deg Fq P else 0 := by
  rw [Nat.card_congr (fiberEquiv Fq L P)]
  have := P.isMaximal
  letI : Field (S ⧸ P.asIdeal) := Ideal.Quotient.field _
  have : Module.Finite Fq L := Module.Finite.of_finite
  split_ifs with h
  · exact card_algHom_of_dvd Fq h
  · exact card_algHom_eq_zero Fq h

/-- **Point count**: `#Hom_Fq(S, L) = Σ_{deg P ∣ [L : Fq]} deg P`, for any finite set `T` of places
containing all places of degree dividing `[L : Fq]`. -/
theorem card_algHom_eq_sum {T : Finset (HeightOneSpectrum S)}
    (hT : ∀ P, deg Fq P ∣ finrank Fq L → P ∈ T) :
    Nat.card (S →ₐ[Fq] L) = ∑ P ∈ T with deg Fq P ∣ finrank Fq L, deg Fq P := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hmem : ∀ φ : S →ₐ[Fq] L, kerPlace Fq L φ ∈ T := fun φ => hT _ (by
    have := (kerPlace Fq L φ).isMaximal
    letI : Field (S ⧸ (kerPlace Fq L φ).asIdeal) := Ideal.Quotient.field _
    exact finrank_dvd_of_algHom_field Fq (fiberEquiv Fq L _ ⟨φ, rfl⟩))
  have hfib : ∀ P : HeightOneSpectrum S, {φ : S →ₐ[Fq] L | kerPlace Fq L φ = P}.Finite := fun P => by
    have : Finite (S ⧸ P.asIdeal →ₐ[Fq] L) := finite_algHom Fq
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (fiberEquiv Fq L P).symm)
  have hfin : Finite (S →ₐ[Fq] L) :=
    Set.finite_univ_iff.mp ((T.finite_toSet.biUnion fun P _ => hfib P).subset fun φ _ =>
      Set.mem_biUnion (hmem φ) rfl)
  have := Fintype.ofFinite (S →ₐ[Fq] L)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := kerPlace Fq L) (t := T) (fun φ _ => hmem φ), Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← card_fiber Fq L P, Nat.card_eq_fintype_card, Fintype.card_subtype]

end PointCount

section FunctionFieldCount

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem X_pow_ne_self {N : ℕ} (hN : 2 ≤ N) :
    (algebraMap Fq[X] (Rfin Fq F) X) ^ N ≠ algebraMap Fq[X] (Rfin Fq F) X := by
  rw [← map_pow, Ne, (FunctionField.ringOfIntegers.algebraMap_injective Fq F).eq_iff]
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow, natDegree_X] at this
  omega

theorem piInf_pow_ne_self {N : ℕ} (hN : 2 ≤ N) :
    (algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)) ^ N ≠ algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq) := by
  rw [← map_pow, Ne, (algebraMap_Oinf_Rinf_injective Fq F).eq_iff]
  intro h
  have h2 := congrArg (fun z : Oinf Fq => RatFunc.intDegree (z : RatFunc Fq)) h
  simp only [SubmonoidClass.coe_pow, coe_piInf, one_div, inv_pow] at h2
  rw [RatFunc.intDegree_inv, RatFunc.intDegree_inv, ← RatFunc.algebraMap_X, ← map_pow,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, natDegree_X_pow, natDegree_X] at h2
  omega

theorem finite_place_deg_eq (d : ℕ) : {P : Place Fq F | P.deg = d}.Finite := by
  have h1 := finite_deg_eq_of Fq (fun N hN => X_pow_ne_self Fq F hN) d
  have h2 := finite_deg_eq_of Fq (fun N hN => piInf_pow_ne_self Fq F hN) d
  refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
  rintro (P | P) hP
  · exact Or.inl ⟨P, hP, rfl⟩
  · exact Or.inr ⟨P, hP, rfl⟩

theorem finite_place_deg_dvd {m : ℕ} (hm : m ≠ 0) : {P : Place Fq F | P.deg ∣ m}.Finite :=
  (m.divisors.finite_toSet.biUnion fun d _ => finite_place_deg_eq Fq F d).subset fun P hP =>
    Set.mem_biUnion (Nat.mem_divisors.mpr ⟨hP, hm⟩) rfl

/-- `N_m = Σ_{deg P ∣ m} deg P` (`0` for `m = 0`). -/
def numPoints (m : ℕ) : ℕ :=
  if hm : m = 0 then 0 else ∑ P ∈ (finite_place_deg_dvd Fq F hm).toFinset, P.deg

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- Affine points: `#Hom_Fq(Rfin, L) = Σ_{finite P, deg P ∣ [L:Fq]} deg P`. -/
theorem card_algHom_Rfin :
    Nat.card (Rfin Fq F →ₐ[Fq] L) = ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN)
      (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset, deg Fq P := by
  have : Module.Finite Fq L := Module.Finite.of_finite
  rw [card_algHom_eq_sum Fq L (T := (finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN)
    (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset) (fun P hP => (Set.Finite.mem_toFinset _).mpr hP)]
  congr 1
  exact Finset.filter_true_of_mem fun P hP => by simpa using hP

theorem card_algHom_Rinf :
    Nat.card (Rinf Fq F →ₐ[Fq] L) = ∑ P ∈ (finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN)
      (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset, deg Fq P := by
  have : Module.Finite Fq L := Module.Finite.of_finite
  rw [card_algHom_eq_sum Fq L (T := (finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN)
    (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset) (fun P hP => (Set.Finite.mem_toFinset _).mpr hP)]
  congr 1
  exact Finset.filter_true_of_mem fun P hP => by simpa using hP

/-- `N_m = #Hom_Fq(Rfin, L) + #Hom_Fq(Rinf, L)` for `L` of degree `m` over `Fq`. -/
theorem numPoints_eq_card_algHom :
    numPoints Fq F (finrank Fq L) = Nat.card (Rfin Fq F →ₐ[Fq] L) + Nat.card (Rinf Fq F →ₐ[Fq] L) := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  have hm : finrank Fq L ≠ 0 := (Module.finrank_pos (R := Fq) (M := L)).ne'
  rw [card_algHom_Rfin, card_algHom_Rinf, numPoints, dif_neg hm]
  have hsplit : (finite_place_deg_dvd Fq F hm).toFinset =
      ((finite_deg_dvd_of Fq (fun N hN => X_pow_ne_self Fq F hN) hm).toFinset.map Function.Embedding.inl).disjUnion
      ((finite_deg_dvd_of Fq (fun N hN => piInf_pow_ne_self Fq F hN) hm).toFinset.map Function.Embedding.inr)
      (by
        rw [Finset.disjoint_left]
        rintro _ h1 h2
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp h1
        obtain ⟨b, -, hb⟩ := Finset.mem_map.mp h2
        exact Sum.inr_ne_inl hb) := by
    ext P
    rcases P with P | P <;> simp
  rw [hsplit, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  rfl

end FunctionFieldCount

end RamanujanPetersson.Places

end

end

-- ===== S3.Places_C =====
section

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial IsDedekindDomain Module

namespace RamanujanPetersson.Places

/-! ## 8. Functions without poles are constants -/

section Valuation

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

theorem valuation_le_one_of_neg_log_nonneg (P : HeightOneSpectrum S) {f : K}
    (h : 0 ≤ -WithZero.log (P.valuation K f)) : P.valuation K f ≤ 1 := by
  by_cases hf : f = 0
  · simp [hf]
  have hv : P.valuation K f ≠ 0 := by simpa using hf
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem neg_log_nonneg_of_valuation_le_one (P : HeightOneSpectrum S) {f : K}
    (h : P.valuation K f ≤ 1) : 0 ≤ -WithZero.log (P.valuation K f) := by
  by_cases hf : f = 0
  · simp [hf]
  have hv : P.valuation K f ≠ 0 := by simpa using hf
  rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem neg_log_nonneg_algebraMap (P : HeightOneSpectrum S) (a : S) :
    0 ≤ -WithZero.log (P.valuation K (algebraMap S K a)) :=
  neg_log_nonneg_of_valuation_le_one P (P.valuation_le_one a)

/-- The ultrametric inequality for `ord = -log v`. -/
theorem min_neg_log_le_neg_log_add (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    min (-WithZero.log (P.valuation K f)) (-WithZero.log (P.valuation K g)) ≤
      -WithZero.log (P.valuation K (f + g)) := by
  have h := Valuation.map_add (P.valuation K) f g
  have hv1 : P.valuation K f ≠ 0 := by simpa using hf
  have hv2 : P.valuation K g ≠ 0 := by simpa using hg
  have hv3 : P.valuation K (f + g) ≠ 0 := by simpa using hfg
  rw [← WithZero.exp_log hv1, ← WithZero.exp_log hv2, ← WithZero.exp_log hv3, le_max_iff,
    WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  rcases h with h | h
  · exact min_le_of_left_le (by omega)
  · exact min_le_of_right_le (by omega)

end Valuation

section NoPoles

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem isIntegral_poly_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rfin Fq F), 0 ≤ ord P f) : IsIntegral Fq[X] f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

theorem isIntegral_Oinf_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rinf Fq F), 0 ≤ ord P f) : IsIntegral (Oinf Fq) f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

/-- A polynomial in `x` that is regular at `x = ∞` is a constant. -/
theorem mem_range_of_mem_Oinf {p : Fq[X]} (h : algebraMap Fq[X] (RatFunc Fq) p ∈ Oinf Fq) :
    algebraMap Fq[X] (RatFunc Fq) p ∈ Set.range (algebraMap Fq (RatFunc Fq)) := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hne : algebraMap Fq[X] (RatFunc Fq) p ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))]
  have h2 := (mem_Oinf_iff' Fq hne).mp h
  rw [RatFunc.intDegree_polynomial] at h2
  have hdeg : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq), Polynomial.algebraMap_eq,
    ← eq_C_of_natDegree_eq_zero hdeg]

/-- Integral over `Fq[x]` and over the valuation ring at `∞` implies integral over `Fq`. -/
theorem isIntegral_of_isIntegral_poly_Oinf {f : F} (h1 : IsIntegral Fq[X] f)
    (h2 : IsIntegral (Oinf Fq) f) : IsIntegral Fq f := by
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc Fq) h1
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc Fq) h2
  have hl : minpoly (RatFunc Fq) f ∈ lifts (algebraMap Fq (RatFunc Fq)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hc2 : (minpoly (RatFunc Fq) f).coeff n ∈ Oinf Fq := by
      rw [e2, coeff_map]
      exact SetLike.coe_mem _
    rw [e1, coeff_map] at hc2 ⊢
    exact mem_range_of_mem_Oinf Fq hc2
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic h1.tower_top)
  refine ⟨q, hmon, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap (RatFunc Fq), hq, minpoly.aeval]

/-- **A function without poles is a constant** (Riemann-Roch's `L(0) = k`). -/
theorem mem_constField_of_ord_nonneg {f : F} (h : ∀ P : Place Fq F, 0 ≤ P.ord f) :
    f ∈ constField Fq F :=
  mem_algebraicClosure_iff.mpr (isIntegral_of_isIntegral_poly_Oinf Fq F
    (isIntegral_poly_of_ord_nonneg Fq F fun P => h (Sum.inl P))
    (isIntegral_Oinf_of_ord_nonneg Fq F fun P => h (Sum.inr P))).isAlgebraic

/-- Constants have no poles. -/
theorem ord_nonneg_of_mem_constField {f : F} (hf : f ∈ constField Fq F) (P : Place Fq F) :
    0 ≤ P.ord f := by
  rcases P with P | P
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRfin Fq F ⟨f, hf⟩)
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRinf Fq F ⟨f, hf⟩)

theorem Place.ord_one (P : Place Fq F) : P.ord (1 : F) = 0 := by
  have h := P.ord_mul (one_ne_zero (α := F)) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

theorem Place.ord_add (P : Place Fq F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases P with P | P
  exacts [min_neg_log_le_neg_log_add P hf hg hfg, min_neg_log_le_neg_log_add P hf hg hfg]

/-- Nonzero constants have neither zeros nor poles. -/
theorem ord_eq_zero_of_mem_constField {f : F} (hf : f ∈ constField Fq F) (hf0 : f ≠ 0)
    (P : Place Fq F) : P.ord f = 0 := by
  have h1 := ord_nonneg_of_mem_constField Fq F hf P
  have h2 := ord_nonneg_of_mem_constField Fq F (inv_mem hf) P
  have h3 : P.ord (f * f⁻¹) = P.ord f + P.ord f⁻¹ := P.ord_mul hf0 (inv_ne_zero hf0)
  rw [mul_inv_cancel₀ hf0, Place.ord_one] at h3
  omega

/-- Multiplying by a nonzero constant does not change orders. -/
theorem ord_const_mul {c f : F} (hc : c ∈ constField Fq F) (hc0 : c ≠ 0) (hf : f ≠ 0) (P : Place Fq F) :
    P.ord (c * f) = P.ord f := by
  rw [P.ord_mul hc0 hf, ord_eq_zero_of_mem_constField Fq F hc hc0, zero_add]

/-- `div f = 0` exactly for the nonzero constants. -/
theorem div_eq_zero_iff {f : F} (hf : f ≠ 0) :
    (div f : Divisor Fq F) = 0 ↔ f ∈ constField Fq F := by
  constructor
  · intro h
    apply mem_constField_of_ord_nonneg
    intro P
    have h' := congrArg (fun D : Divisor Fq F => D P) h
    simp only [div_apply, Finsupp.coe_zero, Pi.zero_apply] at h'
    omega
  · intro h
    ext P
    rw [div_apply, Finsupp.coe_zero, Pi.zero_apply, ord_eq_zero_of_mem_constField Fq F h hf P]

end NoPoles

/-! ## 9. Degree-one places of a constant field extension -/

section ConstantFieldExtension

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']

end ConstantFieldExtension

end RamanujanPetersson.Places

end

end

-- ===== S3.RR_A =====
section

/-!
# Riemann-Roch, part A: the abstract repartition (adele) calculus

Weil's proof of Riemann-Roch (Stichtenoth, *Algebraic Function Fields and Codes*, ch. 1) with
repartitions whose entries lie in `F` itself (no completions).  Everything here is ABSTRACT:
a field `F` over a finite field `Fq` with a family `v : ι → Valuation F ℤᵐ⁰` of valuations
(the places) and degrees `deg : ι → ℕ`.  The axioms used are collected in `Data.Axioms`;
part C discharges them for function fields (`RamanujanPetersson.Places`).

All index bookkeeping is done with `AddSubgroup.relIndex` (unconditionally multiplicative,
`0` encodes an infinite index) and converted to `Module.finrank` only for `L(D)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.RR

/-! ### Group-theoretic index lemmas -/

section Index

/-- Relative index of two submodules, as additive subgroups. -/
noncomputable def rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (H K : Submodule R V) : ℕ :=
  H.toAddSubgroup.relIndex K.toAddSubgroup

theorem inf_toAddSubgroup' {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (H K : Submodule R V) :
    (H ⊓ K).toAddSubgroup = H.toAddSubgroup ⊓ K.toAddSubgroup := rfl

/-- `[H' : H] = [H' ∩ K : H ∩ K] [H' + K : H + K]` for `H ≤ H'` in an abelian group. -/
theorem relIndex_split {G : Type*} [AddCommGroup G] {H H' : AddSubgroup G} (K : AddSubgroup G)
    (h : H ≤ H') :
    H.relIndex H' = (H ⊓ K).relIndex (H' ⊓ K) * (H ⊔ K).relIndex (H' ⊔ K) := by
  have h1 : H ≤ H ⊔ (H' ⊓ K) := le_sup_left
  have h2 : H ⊔ (H' ⊓ K) ≤ H' := sup_le h inf_le_left
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  congr 1
  · rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right H (H' ⊓ K),
      ← AddSubgroup.inf_relIndex_right (H ⊓ K) (H' ⊓ K)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, c⟩, b, c⟩
    · rintro ⟨⟨a, c⟩, b, _⟩; exact ⟨a, b, c⟩
  · have hmod : H ⊔ (H' ⊓ K) = H' ⊓ (H ⊔ K) := by
      apply le_antisymm
      · exact sup_le (le_inf h le_sup_left) (inf_le_inf_left _ le_sup_right)
      · intro x hx
        rw [AddSubgroup.mem_inf] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx2
        have hb' : b ∈ H' := by simpa using H'.sub_mem hx1 (h ha)
        exact AddSubgroup.mem_sup.2 ⟨a, ha, b, AddSubgroup.mem_inf.2 ⟨hb', hb⟩, rfl⟩
    rw [hmod, AddSubgroup.inf_relIndex_left, ← AddSubgroup.relIndex_sup_left H' (H ⊔ K)]
    congr 1
    apply le_antisymm
    · exact sup_le (sup_le (h.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

/-- `|K| = |H| [K : H]` for `H ≤ K`. -/
theorem card_mul_relIndex {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have := (H.addSubgroupOf K).card_mul_index
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h).toEquiv] at this
  exact this

theorem rI_split {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H H' : Submodule R V}
    (K : Submodule R V) (h : H ≤ H') :
    rI H H' = rI (H ⊓ K) (H' ⊓ K) * rI (H ⊔ K) (H' ⊔ K) := by
  unfold rI
  rw [Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup, inf_toAddSubgroup',
    inf_toAddSubgroup']
  exact relIndex_split _ h

theorem rI_mul_rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K L : Submodule R V}
    (hHK : H ≤ K) (hKL : K ≤ L) : rI H K * rI K L = rI H L :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL

theorem card_mul_rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K : Submodule R V}
    (h : H ≤ K) : Nat.card H * rI H K = Nat.card K :=
  card_mul_relIndex (H := H.toAddSubgroup) (K := K.toAddSubgroup) h

theorem rI_eq_one_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K : Submodule R V} :
    rI H K = 1 ↔ K ≤ H := by
  unfold rI
  rw [AddSubgroup.relIndex_eq_one]
  rfl

end Index

/-! ### Exponential helpers -/

theorem exp_mul_le_exp_iff {a b : ℤ} {x : ℤᵐ⁰} : exp a * x ≤ exp b ↔ x ≤ exp (b - a) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← exp_log hx, ← exp_add, exp_le_exp, exp_le_exp]; omega

theorem pow_eq_pow_mul {q a b : ℕ} (hq : 1 < q) {r : ℕ} (h : q ^ a * r = q ^ b) :
    a ≤ b ∧ r = q ^ (b - a) := by
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right hq).1 ⟨r, h.symm⟩
  refine ⟨hab, ?_⟩
  have hpos : 0 < q ^ a := pow_pos (by omega) a
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, ← pow_add, Nat.add_sub_cancel' hab]

/-! ### Abstract data -/

/-- Abstract data for Riemann-Roch: valuations `v i` on `F` (the places), trivial on `Fq`,
with degrees `deg i`, such that a nonzero `f` has `v i f ≠ 1` for finitely many `i`. -/
structure Data (Fq F ι : Type*) [Field Fq] [Field F] [Algebra Fq F] where
  v : ι → Valuation F ℤᵐ⁰
  deg : ι → ℕ
  v_algebraMap : ∀ i (c : Fq), c ≠ 0 → v i (algebraMap Fq F c) = 1
  finite_ne_one : ∀ f : F, f ≠ 0 → {i | v i f ≠ 1}.Finite

namespace Data

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)

/-! #### Divisors -/

/-- The degree of a divisor. -/
def degD (D : ι →₀ ℤ) : ℤ := D.sum fun i n => n * (d.deg i : ℤ)

theorem degD_add (D E : ι →₀ ℤ) : d.degD (D + E) = d.degD D + d.degD E := by
  unfold degD; rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem degD_neg (D : ι →₀ ℤ) : d.degD (-D) = -d.degD D := by
  unfold degD
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem degD_sub (D E : ι →₀ ℤ) : d.degD (D - E) = d.degD D - d.degD E := by
  rw [sub_eq_add_neg, degD_add, degD_neg, sub_eq_add_neg]

theorem degD_single (i : ι) (n : ℤ) : d.degD (Finsupp.single i n) = n * d.deg i := by
  unfold degD; rw [Finsupp.sum_single_index (by ring)]

@[simp] theorem degD_zero : d.degD 0 = 0 := by simp [degD]

theorem degD_nsmul (n : ℕ) (D : ι →₀ ℤ) : d.degD (n • D) = n * d.degD D := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, degD_add, ih]; push_cast; ring

theorem degD_nonneg {E : ι →₀ ℤ} (hE : 0 ≤ E) : 0 ≤ d.degD E := by
  unfold degD
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hE i) (Nat.cast_nonneg _)

theorem degD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.degD D ≤ d.degD E := by
  have := d.degD_nonneg (sub_nonneg.2 h)
  rw [degD_sub] at this; linarith

/-- With positive degrees, an effective divisor of degree `0` is zero. -/
theorem eq_zero_of_degD_eq_zero (hdeg : ∀ i, 0 < d.deg i) {E : ι →₀ ℤ} (hE : 0 ≤ E)
    (h0 : d.degD E = 0) : E = 0 := by
  unfold degD Finsupp.sum at h0
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hE i) (Nat.cast_nonneg _))] at h0
  ext i
  by_cases hi : i ∈ E.support
  · rcases mul_eq_zero.1 (h0 i hi) with h | h
    · exact h
    · have := hdeg i; omega
  · simpa using hi

/-! #### Balls, adeles and Riemann-Roch spaces -/

theorem v_smul (i : ι) {c : Fq} (hc : c ≠ 0) (f : F) : d.v i (c • f) = d.v i f := by
  rw [Algebra.smul_def, map_mul, d.v_algebraMap i c hc, one_mul]

/-- The ball `{f | v_i f ≤ exp n}` (functions with a pole of order at most `n` at `i`). -/
def ball (i : ι) (n : ℤ) : Submodule Fq F where
  carrier := {f | d.v i f ≤ exp n}
  add_mem' {a b} ha hb := ((d.v i).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  smul_mem' c f hf := by
    by_cases hc : c = 0
    · simp [hc]
    · show d.v i (c • f) ≤ exp n
      rw [d.v_smul i hc]; exact hf

@[simp] theorem mem_ball {i : ι} {n : ℤ} {f : F} : f ∈ d.ball i n ↔ d.v i f ≤ exp n := Iff.rfl

/-- The space `A(D)` of repartitions `α` with `v_i (α i) ≤ exp (D i)` for all `i`. -/
def AD (D : ι →₀ ℤ) : Submodule Fq (ι → F) := Submodule.pi Set.univ fun i => d.ball i (D i)

theorem mem_AD {D : ι →₀ ℤ} {α : ι → F} : α ∈ d.AD D ↔ ∀ i, d.v i (α i) ≤ exp (D i) := by
  simp [AD, Submodule.mem_pi]

theorem AD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.AD D ≤ d.AD E := fun _ hα =>
  d.mem_AD.2 fun i => (d.mem_AD.1 hα i).trans (exp_le_exp.2 (h i))

/-- The adeles (repartitions): `α : ι → F` with `v_i (α i) ≤ 1` for almost all `i`. -/
def adeles : Submodule Fq (ι → F) where
  carrier := {α | {i | 1 < d.v i (α i)}.Finite}
  add_mem' {a b} ha hb := (ha.union hb).subset fun i hi => by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hi
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at h
    exact absurd (((d.v i).map_add _ _).trans (max_le h.1 h.2)) (not_le.2 hi)
  zero_mem' := by simp
  smul_mem' c a ha := by
    by_cases hc : c = 0
    · simp [hc]
    · refine ha.subset fun i hi => ?_
      simp only [Set.mem_setOf_eq, Pi.smul_apply] at hi ⊢
      rwa [d.v_smul i hc] at hi

theorem mem_adeles {α : ι → F} : α ∈ d.adeles ↔ {i | 1 < d.v i (α i)}.Finite := Iff.rfl

theorem AD_le_adeles (D : ι →₀ ℤ) : d.AD D ≤ d.adeles := by
  intro α hα
  refine D.support.finite_toSet.subset fun i hi => ?_
  by_contra h
  have h0 : D i = 0 := by simpa using h
  have h1 := d.mem_AD.1 hα i
  rw [h0, exp_zero] at h1
  exact absurd h1 (not_le.2 hi)

/-- The diagonal embedding `F → ι → F`. -/
def const (_ : Data Fq F ι) : F →ₗ[Fq] (ι → F) := LinearMap.pi fun _ => LinearMap.id

@[simp] theorem const_apply (f : F) (i : ι) : d.const f i = f := rfl

theorem const_injective [Nonempty ι] : Function.Injective d.const := fun f g h => by
  have := congr_fun h (Classical.arbitrary ι)
  simpa using this

/-- The principal repartitions. -/
def Fs : Submodule Fq (ι → F) := LinearMap.range d.const

theorem Fs_le_adeles : d.Fs ≤ d.adeles := by
  rintro _ ⟨f, rfl⟩
  by_cases hf : f = 0
  · subst hf; simp
  · refine (d.finite_ne_one f hf).subset fun i hi => ?_
    exact ne_of_gt hi

/-- The Riemann-Roch space `L(D) = {f | v_i f ≤ exp (D i) for all i}`. -/
def LD (D : ι →₀ ℤ) : Submodule Fq F := (d.AD D).comap d.const

theorem mem_LD {D : ι →₀ ℤ} {f : F} : f ∈ d.LD D ↔ ∀ i, d.v i f ≤ exp (D i) := by
  simp [LD, mem_AD]

theorem LD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.LD D ≤ d.LD E :=
  Submodule.comap_mono (d.AD_mono h)

/-- `ℓ(D) = dim_Fq L(D)`. -/
noncomputable def ell (D : ι →₀ ℤ) : ℕ := Module.finrank Fq (d.LD D)

theorem map_LD (D : ι →₀ ℤ) : (d.LD D).map d.const = d.AD D ⊓ d.Fs := by
  rw [LD, Submodule.map_comap_eq, inf_comm]
  rfl

theorem rI_LD [Nonempty ι] (D E : ι →₀ ℤ) :
    rI (d.LD D) (d.LD E) = rI (d.AD D ⊓ d.Fs) (d.AD E ⊓ d.Fs) := by
  rw [← d.map_LD, ← d.map_LD]
  unfold rI
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ d.const_injective]

/-! #### Divisors of functions -/

/-- The divisor of `f` (`0` for `f = 0`): `(div f) i = -log (v_i f)`. -/
noncomputable def div (f : F) : ι →₀ ℤ :=
  Finsupp.ofSupportFinite (fun i => -log (d.v i f)) (by
    by_cases hf : f = 0
    · subst hf; simp
    · refine (d.finite_ne_one f hf).subset fun i hi h1 => hi ?_
      simp [h1])

theorem div_apply (f : F) (i : ι) : d.div f i = -log (d.v i f) := by
  simp [div, Finsupp.ofSupportFinite_coe]

theorem v_eq_exp {f : F} (hf : f ≠ 0) (i : ι) : d.v i f = exp (-(d.div f i)) := by
  rw [div_apply, neg_neg, exp_log ((map_ne_zero _).2 hf)]

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : d.div (f * g) = d.div f + d.div g := by
  ext i
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, map_mul]
  rw [log_mul ((map_ne_zero _).2 hf) ((map_ne_zero _).2 hg)]; ring

theorem div_inv {f : F} (hf : f ≠ 0) : d.div f⁻¹ = -d.div f := by
  have h := d.div_mul (inv_ne_zero hf) hf
  rw [inv_mul_cancel₀ hf] at h
  have h1 : d.div (1 : F) = 0 := by ext i; simp [div_apply]
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_LD_iff_div {D : ι →₀ ℤ} {f : F} (hf : f ≠ 0) : f ∈ d.LD D ↔ 0 ≤ d.div f + D := by
  rw [mem_LD, Finsupp.le_def]
  refine forall_congr' fun i => ?_
  rw [d.v_eq_exp hf, exp_le_exp, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- Multiplication by `z ≠ 0` maps `L(D + div z)` onto `L(D)`. -/
theorem map_mul_LD {z : F} (hz : z ≠ 0) (D : ι →₀ ℤ) :
    (d.LD (D + d.div z)).map (LinearMap.mulLeft Fq z) = d.LD D := by
  have key : ∀ (E : ι →₀ ℤ) (g : F), g ∈ d.LD (E + d.div z) ↔ z * g ∈ d.LD E := by
    intro E g
    simp only [mem_LD, map_mul, d.v_eq_exp hz, exp_mul_le_exp_iff, Finsupp.coe_add, Pi.add_apply]
    refine forall_congr' fun i => ?_
    rw [sub_neg_eq_add]
  ext f
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact (key D g).1 hg
  · intro hf
    refine ⟨z⁻¹ * f, (key D _).2 ?_, ?_⟩
    · rwa [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    · rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem ell_add_div {z : F} (hz : z ≠ 0) (D : ι →₀ ℤ) : d.ell (D + d.div z) = d.ell D := by
  have hinj : Function.Injective (LinearMap.mulLeft Fq z) := fun a b h => by
    simpa [LinearMap.mulLeft_apply, hz] using h
  unfold ell
  rw [← d.map_mul_LD hz D]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (LinearMap.mulLeft Fq z) hinj (d.LD (D + d.div z))))

/-! #### The local-to-global index computation -/

theorem rI_AD_single (D : ι →₀ ℤ) (i : ι) :
    rI (d.AD D) (d.AD (D + Finsupp.single i 1)) = rI (d.ball i (D i)) (d.ball i (D i + 1)) := by
  classical
  set D' := D + Finsupp.single i 1 with hD'
  have hsi : ∀ j, j ≠ i → D' j = D j := fun j hj => by
    simp [hD', Ne.symm hj]
  have hii : D' i = D i + 1 := by simp [hD']
  let ev : (ι → F) →+ F := Pi.evalAddMonoidHom (fun _ => F) i
  have hAD : (d.AD D).toAddSubgroup =
      (d.ball i (D i)).toAddSubgroup.comap ev ⊓ (d.AD D').toAddSubgroup := by
    ext α
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_inf, AddSubgroup.mem_comap, mem_AD,
      Submodule.mem_toAddSubgroup, mem_ball, ev, Pi.evalAddMonoidHom_apply]
    constructor
    · intro h
      refine ⟨h i, fun j => (h j).trans (exp_le_exp.2 ?_)⟩
      by_cases hj : j = i
      · subst hj; rw [hii]; omega
      · rw [hsi j hj]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h1
      · simpa [hsi j hj] using h2 j
  have hmap : (d.AD D').toAddSubgroup.map ev = (d.ball i (D i + 1)).toAddSubgroup := by
    ext f
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, mem_AD, mem_ball, ev,
      Pi.evalAddMonoidHom_apply]
    constructor
    · rintro ⟨α, hα, rfl⟩; simpa [hii] using hα i
    · intro hf
      refine ⟨Pi.single i f, fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simpa [hii] using hf
      · simp [hj]
  unfold rI
  rw [hAD, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

/-! #### The axioms and the global index of `A(D) ⊆ A(D')` -/

variable [Fintype Fq]

/-- The local axioms of the abstract theory (discharged for function fields in part C):
places exist and have positive degree, the local index `[ball i (n+1) : ball i n] = q ^ deg i`,
the product formula and `L(0)` finite. -/
structure Axioms0 : Prop where
  nonempty : Nonempty ι
  deg_pos : ∀ i, 0 < d.deg i
  localIndex : ∀ i (n : ℤ), rI (d.ball i n) (d.ball i (n + 1)) = Fintype.card Fq ^ d.deg i
  deg_div : ∀ f : F, f ≠ 0 → d.degD (d.div f) = 0
  finite_L0 : Finite (d.LD 0)

/-- The axioms: the local axioms plus the input for Riemann's inequality (for function fields:
`B` the pole divisor of a separating element `x`, `C` a pole bound for an integral basis). -/
structure Axioms extends Axioms0 d : Prop where
  riemannInput : ∃ B : ι →₀ ℤ, 0 ≤ B ∧ 0 < d.degD B ∧ ∃ C : ι →₀ ℤ, 0 ≤ C ∧
    ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B + C)

variable {d}

theorem one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card

theorem rI_AD_add_single_nat (hd : d.Axioms0) (D : ι →₀ ℤ) (i : ι) (n : ℕ) :
    rI (d.AD D) (d.AD (D + Finsupp.single i (n : ℤ))) = Fintype.card Fq ^ (n * d.deg i) := by
  induction n with
  | zero => simp [rI, AddSubgroup.relIndex_self]
  | succ n ih =>
    have e : D + Finsupp.single i ((n + 1 : ℕ) : ℤ) =
        (D + Finsupp.single i (n : ℤ)) + Finsupp.single i 1 := by
      rw [Nat.cast_succ, Finsupp.single_add, add_assoc]
    rw [e, ← rI_mul_rI (d.AD_mono (le_add_of_nonneg_right
        (Finsupp.single_nonneg.2 (Nat.cast_nonneg _))))
      (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))), ih,
      d.rI_AD_single, hd.localIndex, ← pow_add]
    congr 1; ring

theorem rI_AD_add (hd : d.Axioms0) {E : ι →₀ ℤ} (hE : 0 ≤ E) (D : ι →₀ ℤ) :
    rI (d.AD D) (d.AD (D + E)) = Fintype.card Fq ^ (d.degD E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero => simp [rI, AddSubgroup.relIndex_self]
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have hb0 : 0 ≤ b := by have := hE a; simpa [hfa] using this
    have hf0 : 0 ≤ f := fun j => by
      by_cases hj : j = a
      · subst hj; simp [hfa]
      · have := hE j; simpa [Finsupp.single_apply, Ne.symm hj] using this
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    rw [← add_assoc, ← rI_mul_rI (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 hb0)))
      (d.AD_mono (le_add_of_nonneg_right hf0)), rI_AD_add_single_nat hd, ih hf0, ← pow_add,
      degD_add, degD_single]
    congr 1
    have hdf := d.degD_nonneg hf0
    have hm : ((k : ℤ) * (d.deg a : ℤ)) = ((k * d.deg a : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    generalize k * d.deg a = m
    omega

/-- `[A(D') : A(D)] = q ^ (deg D' - deg D)`. -/
theorem rI_AD_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    rI (d.AD D) (d.AD D') = Fintype.card Fq ^ (d.degD D' - d.degD D).toNat := by
  have := rI_AD_add hd (sub_nonneg.2 h) D
  rwa [add_sub_cancel, degD_sub] at this

theorem card_LD_mul {D D' : ι →₀ ℤ} (h : D ≤ D') :
    Nat.card (d.LD D) * rI (d.LD D) (d.LD D') = Nat.card (d.LD D') :=
  card_mul_rI (d.LD_mono h)

theorem rI_LD_mul (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    rI (d.LD D) (d.LD D') * rI (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      Fintype.card Fq ^ (d.degD D' - d.degD D).toNat := by
  have := hd.nonempty
  rw [d.rI_LD, ← rI_split _ (d.AD_mono h), rI_AD_le hd h]

theorem finite_LD (hd : d.Axioms0) (D : ι →₀ ℤ) : Finite (d.LD D) := by
  have := hd.finite_L0
  have h1 : (0 : ι →₀ ℤ) ≤ D ⊔ 0 := le_sup_right
  have h2 : D ≤ D ⊔ 0 := le_sup_left
  have hne : rI (d.LD 0) (d.LD (D ⊔ 0)) ≠ 0 := by
    intro h0
    have := rI_LD_mul hd h1
    rw [h0, zero_mul] at this
    exact absurd this.symm (pow_ne_zero _ Fintype.card_ne_zero)
  have hc : Nat.card (d.LD (D ⊔ 0)) ≠ 0 := by
    rw [← card_LD_mul h1]
    exact mul_ne_zero Nat.card_pos.ne' hne
  have : Finite (d.LD (D ⊔ 0)) := Nat.finite_of_card_ne_zero hc
  exact Finite.of_injective (Submodule.inclusion (d.LD_mono h2)) (Submodule.inclusion_injective _)

/-- `|L(D)| = q ^ ℓ(D)`. -/
theorem card_LD (hd : d.Axioms0) (D : ι →₀ ℤ) : Nat.card (d.LD D) = Fintype.card Fq ^ d.ell D := by
  have := finite_LD hd D
  have : Module.Finite Fq (d.LD D) := Module.Finite.of_finite
  rw [ell, Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card]

theorem ell_le_of_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    d.ell D ≤ d.ell D' ∧ rI (d.LD D) (d.LD D') = Fintype.card Fq ^ (d.ell D' - d.ell D) := by
  have := card_LD_mul (d := d) h
  rw [card_LD hd, card_LD hd] at this
  exact pow_eq_pow_mul (one_lt_q (Fq := Fq)) this

/-- `ℓ(D') - ℓ(D) ≤ deg D' - deg D` for `D ≤ D'`, and the index of `A(D) + F` in `A(D') + F`. -/
theorem ell_sub_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    (d.ell D' : ℤ) - d.ell D ≤ d.degD D' - d.degD D ∧
    rI (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      Fintype.card Fq ^ ((d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D)) := by
  obtain ⟨hle, hr⟩ := ell_le_of_le hd h
  have := rI_LD_mul hd h
  rw [hr] at this
  obtain ⟨h1, h2⟩ := pow_eq_pow_mul (one_lt_q (Fq := Fq)) this
  refine ⟨?_, h2⟩
  have := d.degD_mono h
  omega

end Data

end RamanujanPetersson.RR


end

-- ===== S3.RR_B =====
section

/-!
# Riemann-Roch, part B: the index formula, Weil differentials and the Riemann-Roch theorem

Abstract setting of part A (`RamanujanPetersson.RR.Data` with `Data.Axioms`).  Following
Stichtenoth ch. 1.4-1.5 (with `Fq`-dimensions and `Fq`-degrees; `ℓ 0 = [k : Fq]` for the full
constant field `k`, so the classical statements are the case `ℓ 0 = 1`):

* `ell_eq_zero_of_degD_neg`, `defect_le` (Riemann's bound), `gamma = max_D (deg D - ℓ D)`;
* `rI_adeles`: `[A : A(D) + F] = q ^ iota D` with `iota D = ℓ D - deg D + γ`; `genus = iota 0`;
* Weil differentials `Omega D` (linear forms on the adeles vanishing on `A(D) + F`), the `F`-action
  `wsmul`, `finrank_Omega : dim Ω(D) = iota D`, one-dimensionality over `F`
  (`exists_eq_wsmul`, `exists_weilDiff_ne_zero`), the divisor of a differential (`exists_divisor`);
* `riemannRoch`: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` for a canonical divisor `W`, and the
  corollaries `ell_canonical`, `degD_canonical`, `ell_eq_of_large_degD`, `ell_le_degD_add`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.RR

namespace Data

section General

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)

/-! ### Definitions -/

/-- The maximal defect `γ = sup_D (deg D - ℓ D)` (finite under the axioms, `defect_le`). -/
noncomputable def gamma : ℤ := sSup (Set.range fun D : ι →₀ ℤ => d.degD D - d.ell D)

/-- The index exponent `iota D = ℓ D - deg D + γ`, so that `[A : A(D) + F] = q ^ iota D`. -/
noncomputable def iota (D : ι →₀ ℤ) : ℕ := ((d.ell D : ℤ) - d.degD D + d.gamma).toNat

/-- The genus (over `Fq`): `g = iota 0 = dim_Fq A / (A(0) + F)`. -/
noncomputable def genus : ℕ := d.iota 0

theorem AD_sup (D1 D2 : ι →₀ ℤ) : d.AD (D1 ⊔ D2) = d.AD D1 ⊔ d.AD D2 := by
  classical
  apply le_antisymm
  · intro α hα
    rw [mem_AD] at hα
    refine Submodule.mem_sup.2 ⟨fun i => if D2 i ≤ D1 i then α i else 0, ?_,
      fun i => if D2 i ≤ D1 i then 0 else α i, ?_, ?_⟩
    · rw [mem_AD]; intro i
      split_ifs with h
      · have := hα i; rwa [Finsupp.sup_apply, sup_eq_left.2 h] at this
      · simp
    · rw [mem_AD]; intro i
      split_ifs with h
      · simp
      · have := hα i; rwa [Finsupp.sup_apply, sup_eq_right.2 (not_le.1 h).le] at this
    · funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  · exact sup_le (d.AD_mono le_sup_left) (d.AD_mono le_sup_right)

/-- Every adele lies in some `A(E)`. -/
theorem exists_AD_of_mem_adeles {α : ι → F} (hα : α ∈ d.adeles) : ∃ E : ι →₀ ℤ, α ∈ d.AD E := by
  classical
  refine ⟨Finsupp.ofSupportFinite (fun i => if 1 < d.v i (α i) then log (d.v i (α i)) else 0) ?_, ?_⟩
  · refine (d.mem_adeles.1 hα).subset fun i hi => ?_
    by_contra h
    exact hi (if_neg h)
  · rw [mem_AD]
    intro i
    rw [Finsupp.ofSupportFinite_coe]
    split_ifs with h
    · rw [exp_log (zero_lt_one.trans h).ne']
    · rw [exp_zero]; exact not_lt.1 h

theorem mul_mem_adeles (x : F) {α : ι → F} (hα : α ∈ d.adeles) : (fun i => x * α i) ∈ d.adeles := by
  by_cases hx : x = 0
  · subst hx
    have : (fun i => (0 : F) * α i) = 0 := funext fun i => zero_mul _
    rw [this]; exact d.adeles.zero_mem
  · refine ((d.finite_ne_one x hx).union (d.mem_adeles.1 hα)).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, map_mul] at hi
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_not] at h
    rw [h.1, one_mul] at hi
    exact absurd hi (not_lt.2 h.2)

/-- Multiplication of repartitions by `x ∈ F`. -/
def mulA (x : F) : d.adeles →ₗ[Fq] d.adeles where
  toFun α := ⟨fun i => x * (α : ι → F) i, d.mul_mem_adeles x α.2⟩
  map_add' α β := by
    apply Subtype.ext; funext i; simp [mul_add]
  map_smul' c α := by
    apply Subtype.ext; funext i; simp

@[simp] theorem mulA_apply (x : F) (α : d.adeles) (i : ι) :
    ((d.mulA x α : d.adeles) : ι → F) i = x * (α : ι → F) i := rfl

/-- The `F`-action on linear forms on the adeles: `(x • ω) α = ω (x α)`. -/
def wsmul (x : F) (ω : Module.Dual Fq d.adeles) : Module.Dual Fq d.adeles := ω ∘ₗ d.mulA x

theorem wsmul_apply (x : F) (ω : Module.Dual Fq d.adeles) (α : d.adeles) :
    d.wsmul x ω α = ω (d.mulA x α) := rfl

theorem wsmul_wsmul (x y : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul x (d.wsmul y ω) = d.wsmul (y * x) ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply]
  congr 1
  apply Subtype.ext; funext i; simp only [mulA_apply]; ring

theorem one_wsmul (ω : Module.Dual Fq d.adeles) : d.wsmul 1 ω = ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply]
  congr 1
  apply Subtype.ext; funext i; simp only [mulA_apply, one_mul]

theorem zero_wsmul (ω : Module.Dual Fq d.adeles) : d.wsmul 0 ω = 0 := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.zero_apply]
  have : d.mulA 0 α = 0 := by apply Subtype.ext; funext i; simp
  rw [this, map_zero]

theorem wsmul_zero (x : F) : d.wsmul x 0 = 0 := rfl

theorem add_wsmul (x y : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul (x + y) ω = d.wsmul x ω + d.wsmul y ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.add_apply]
  rw [← map_add]
  congr 1
  apply Subtype.ext; funext i; simp [add_mul]

theorem smul_wsmul (c : Fq) (x : F) (ω : Module.Dual Fq d.adeles) :
    d.wsmul (c • x) ω = c • d.wsmul x ω := by
  refine LinearMap.ext fun α => ?_
  simp only [wsmul_apply, LinearMap.smul_apply]
  rw [← map_smul]
  congr 1
  apply Subtype.ext; funext i; simp

theorem inv_wsmul_wsmul {x : F} (hx : x ≠ 0) (ω : Module.Dual Fq d.adeles) :
    d.wsmul x⁻¹ (d.wsmul x ω) = ω := by
  rw [wsmul_wsmul, mul_inv_cancel₀ hx, one_wsmul]

/-- `x ↦ x • ω` as an `Fq`-linear map. -/
def wsmulL (ω : Module.Dual Fq d.adeles) : F →ₗ[Fq] Module.Dual Fq d.adeles where
  toFun x := d.wsmul x ω
  map_add' x y := d.add_wsmul x y ω
  map_smul' c x := d.smul_wsmul c x ω

@[simp] theorem wsmulL_apply (ω : Module.Dual Fq d.adeles) (x : F) : d.wsmulL ω x = d.wsmul x ω := rfl

theorem wsmulL_injective {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) : Function.Injective (d.wsmulL ω) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra hx0
  apply hω
  rw [← d.inv_wsmul_wsmul hx0 ω]
  rw [wsmulL_apply] at hx
  rw [hx, wsmul_zero]

/-! ### Weil differentials -/

/-- `Ω(D)`: the linear forms on the adeles vanishing on `A(D) + F` (Weil differentials of
divisor `≥ D`). -/
def Omega (D : ι →₀ ℤ) : Submodule Fq (Module.Dual Fq d.adeles) :=
  ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).dualAnnihilator

theorem mem_Omega {D : ι →₀ ℤ} {ω : Module.Dual Fq d.adeles} :
    ω ∈ d.Omega D ↔ ∀ α : d.adeles, (α : ι → F) ∈ d.AD D ⊔ d.Fs → ω α = 0 := by
  simp [Omega, Submodule.mem_dualAnnihilator]

/-- `W` is a canonical divisor: the divisor of a nonzero Weil differential. -/
def IsCanonical (W : ι →₀ ℤ) : Prop :=
  ∃ ω : Module.Dual Fq d.adeles, ω ≠ 0 ∧ ∀ D, ω ∈ d.Omega D ↔ D ≤ W

theorem Omega_anti {D D' : ι →₀ ℤ} (h : D ≤ D') : d.Omega D' ≤ d.Omega D := fun ω hω =>
  d.mem_Omega.2 fun α hα => d.mem_Omega.1 hω α (sup_le_sup_right (d.AD_mono h) _ hα)

theorem Omega_sup (D1 D2 : ι →₀ ℤ) : d.Omega (D1 ⊔ D2) = d.Omega D1 ⊓ d.Omega D2 := by
  apply le_antisymm
  · exact le_inf (d.Omega_anti le_sup_left) (d.Omega_anti le_sup_right)
  · rintro ω ⟨h1, h2⟩
    rw [SetLike.mem_coe, mem_Omega] at h1 h2
    rw [mem_Omega]
    intro α hα
    rw [AD_sup, sup_sup_distrib_right] at hα
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hα
    have ha' : a ∈ d.adeles := sup_le (d.AD_le_adeles _) d.Fs_le_adeles ha
    have hb' : b ∈ d.adeles := sup_le (d.AD_le_adeles _) d.Fs_le_adeles hb
    have : α = ⟨a, ha'⟩ + ⟨b, hb'⟩ := Subtype.ext hab.symm
    rw [this, map_add, h1 _ ha, h2 _ hb, add_zero]

theorem mul_mem_AD {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {α : ι → F} (hα : α ∈ d.AD D) :
    (fun i => x * α i) ∈ d.AD (D - d.div x) := by
  rw [mem_AD] at hα ⊢
  intro i
  rw [map_mul, d.v_eq_exp hx, exp_mul_le_exp_iff]
  simpa using hα i

theorem mul_mem_AD_sup_Fs {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {β : ι → F} (hβ : β ∈ d.AD D ⊔ d.Fs) :
    (fun i => x * β i) ∈ d.AD (D - d.div x) ⊔ d.Fs := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hβ
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hb
  refine Submodule.mem_sup.2 ⟨_, d.mul_mem_AD hx ha, d.const (x * f), LinearMap.mem_range_self _ _, ?_⟩
  funext i; simp [mul_add]

/-- `x • ω ∈ Ω(D) ↔ ω ∈ Ω(D - (x))` for `x ≠ 0`. -/
theorem wsmul_mem_Omega_iff {x : F} (hx : x ≠ 0) {D : ι →₀ ℤ} {ω : Module.Dual Fq d.adeles} :
    d.wsmul x ω ∈ d.Omega D ↔ ω ∈ d.Omega (D - d.div x) := by
  simp only [mem_Omega, wsmul_apply]
  constructor
  · intro h β hβ
    have hβ' := d.mul_mem_AD_sup_Fs (inv_ne_zero hx) hβ
    rw [d.div_inv hx, sub_neg_eq_add, sub_add_cancel] at hβ'
    have := h (d.mulA x⁻¹ β) hβ'
    rwa [show d.mulA x (d.mulA x⁻¹ β) = β from
      Subtype.ext (funext fun i => by simp [hx])] at this
  · intro h α hα
    exact h (d.mulA x α) (d.mul_mem_AD_sup_Fs hx hα)

/-- `x ∈ L(D' - D)` and `ω ∈ Ω(D')` give `x • ω ∈ Ω(D)`. -/
theorem wsmul_mem_Omega {x : F} {D D' : ι →₀ ℤ} (hx : x ∈ d.LD (D' - D))
    {ω : Module.Dual Fq d.adeles} (hω : ω ∈ d.Omega D') : d.wsmul x ω ∈ d.Omega D := by
  by_cases hx0 : x = 0
  · subst hx0; rw [zero_wsmul]; exact zero_mem _
  rw [d.wsmul_mem_Omega_iff hx0]
  refine d.Omega_anti ?_ hω
  have := (d.mem_LD_iff_div hx0).1 hx
  rw [Finsupp.le_def] at this ⊢
  intro i
  have := this i
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
    Pi.zero_apply] at this ⊢
  omega

end General

/-! ### Results under the axioms -/

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] [Fintype Fq] {d : Data Fq F ι}

theorem LD_eq_bot_of_degD_neg (hd : d.Axioms) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.LD D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  have h := d.degD_nonneg ((d.mem_LD_iff_div hf0).1 hf)
  rw [degD_add, hd.deg_div f hf0] at h
  linarith

theorem ell_eq_zero_of_degD_neg (hd : d.Axioms) {D : ι →₀ ℤ} (hD : d.degD D < 0) : d.ell D = 0 := by
  rw [ell, LD_eq_bot_of_degD_neg hd hD, finrank_bot]

theorem exists_ne_zero_of_ell_pos {D : ι →₀ ℤ} (h : 0 < d.ell D) : ∃ f ∈ d.LD D, f ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : d.LD D = ⊥ := (Submodule.eq_bot_iff _).2 hcon
  rw [ell, this, finrank_bot] at h
  exact lt_irrefl 0 h

/-- The defect of effective divisors is bounded by the Riemann-input constant. -/
theorem defect_le_of_nonneg (hd : d.Axioms) {B : ι →₀ ℤ} (hBdeg : 0 < d.degD B) {c : ℤ}
    (hc : ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B)) {A : ι →₀ ℤ} (hA : 0 ≤ A) :
    d.degD A - d.ell A ≤ c := by
  set n : ℕ := (c + d.degD A).toNat + 1 with hn
  have h1 : (n : ℤ) ≥ c + d.degD A + 1 := by omega
  have h2 : (n : ℤ) * d.degD B ≥ n := by
    have : (1 : ℤ) ≤ d.degD B := hBdeg
    nlinarith
  have hle : n • B - A ≤ n • B := sub_le_self _ hA
  have h3 := (ell_sub_le hd.1 hle).1
  rw [degD_sub] at h3
  have hcn := hc n
  have hpos : 0 < d.ell (n • B - A) := by
    rw [degD_nsmul] at h3
    omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_pos hpos
  have hdiv := (d.mem_LD_iff_div hz0).1 hz
  have hA2 : A + d.div z⁻¹ ≤ n • B := by
    rw [d.div_inv hz0, Finsupp.le_def]
    intro i
    have := Finsupp.le_def.1 hdiv i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_neg, Pi.add_apply, Pi.sub_apply,
      Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
    omega
  have h4 := (ell_sub_le hd.1 hA2).1
  rw [d.ell_add_div (inv_ne_zero hz0), degD_add, hd.deg_div _ (inv_ne_zero hz0), degD_nsmul] at h4
  linarith

/-- Riemann's bound: `deg D - ℓ D` is bounded above. -/
theorem defect_le (hd : d.Axioms) : ∃ c : ℤ, ∀ D : ι →₀ ℤ, d.degD D - d.ell D ≤ c := by
  obtain ⟨B, _, hBdeg, C, hC, c0, hc0⟩ := hd.riemannInput
  have hc : ∀ n : ℕ, (n : ℤ) * d.degD B - (c0 + d.degD C) ≤ d.ell (n • B) := fun n => by
    have h1 := (ell_sub_le hd.1 (le_add_of_nonneg_right hC : n • B ≤ n • B + C)).1
    rw [degD_add] at h1
    have := hc0 n
    linarith
  refine ⟨c0 + d.degD C, fun D => ?_⟩
  have h1 := (ell_sub_le hd.1 (le_sup_left : D ≤ D ⊔ 0)).1
  have h2 := defect_le_of_nonneg hd hBdeg hc (le_sup_right : (0 : ι →₀ ℤ) ≤ D ⊔ 0)
  linarith

theorem bddAbove_defect (hd : d.Axioms) :
    BddAbove (Set.range fun D : ι →₀ ℤ => d.degD D - d.ell D) := by
  obtain ⟨c, hc⟩ := defect_le hd
  exact ⟨c, by rintro _ ⟨D, rfl⟩; exact hc D⟩

theorem defect_le_gamma (hd : d.Axioms) (D : ι →₀ ℤ) : d.degD D - d.ell D ≤ d.gamma :=
  le_csSup (bddAbove_defect hd) ⟨D, rfl⟩

theorem exists_gamma (hd : d.Axioms) : ∃ D0 : ι →₀ ℤ, d.degD D0 - d.ell D0 = d.gamma :=
  Int.csSup_mem (Set.range_nonempty _) (bddAbove_defect hd)

theorem defect_eq_gamma (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.degD D - d.ell D = d.gamma := by
  have h1 := (ell_sub_le hd.1 h).1
  have h2 := defect_le_gamma hd D
  linarith

theorem AD_le_AD_sup_Fs (hd : d.Axioms) {D0 D D' : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) (h' : D ≤ D') : d.AD D' ≤ d.AD D ⊔ d.Fs := by
  have e1 := defect_eq_gamma hd h0 h
  have e2 := defect_eq_gamma hd h0 (h.trans h')
  have hle := (ell_le_of_le hd.1 h').1
  have hr := (ell_sub_le hd.1 h').2
  have hexp : (d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D) = 0 := by omega
  rw [hexp, pow_zero, rI_eq_one_iff] at hr
  exact le_sup_left.trans hr

/-- `A = A(D) + F` once `D ≥ D0` (`D0` of maximal defect). -/
theorem adeles_eq (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (h : D0 ≤ D) : d.adeles = d.AD D ⊔ d.Fs := by
  apply le_antisymm
  · intro α hα
    obtain ⟨E, hE⟩ := d.exists_AD_of_mem_adeles hα
    exact AD_le_AD_sup_Fs hd h0 h (le_sup_left : D ≤ D ⊔ E) (d.AD_mono le_sup_right hE)
  · exact sup_le (d.AD_le_adeles D) d.Fs_le_adeles

theorem iota_eq (hd : d.Axioms) (D : ι →₀ ℤ) : (d.iota D : ℤ) = d.ell D - d.degD D + d.gamma := by
  have := defect_le_gamma hd D
  unfold iota; omega

theorem genus_eq (hd : d.Axioms) : (d.genus : ℤ) = d.ell 0 + d.gamma := by
  rw [genus, iota_eq hd, degD_zero, sub_zero]

/-- The index formula `[A : A(D) + F] = q ^ (ℓ D - deg D + γ)`. -/
theorem rI_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    rI (d.AD D ⊔ d.Fs) d.adeles = Fintype.card Fq ^ d.iota D := by
  obtain ⟨D0, h0⟩ := exists_gamma hd
  have hD : D ≤ D ⊔ D0 := le_sup_left
  rw [adeles_eq hd h0 (le_sup_right : D0 ≤ D ⊔ D0), (ell_sub_le hd.1 hD).2]
  congr 1
  have e2 := defect_eq_gamma hd h0 (le_sup_right : D0 ≤ D ⊔ D0)
  have hle := (ell_le_of_le hd.1 hD).1
  have h1 := (ell_sub_le hd.1 hD).1
  have := iota_eq hd D
  omega

/-- `A = A(D) + F` once `deg D > deg D0 + γ`. -/
theorem adeles_le_of_degD (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.adeles ≤ d.AD D ⊔ d.Fs := by
  have hpos : 0 < d.ell (D - D0) := by
    have := defect_le_gamma hd (D - D0); rw [degD_sub] at this; omega
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_ell_pos hpos
  have hzD : D0 ≤ D + d.div z := by
    have := (d.mem_LD_iff_div hz0).1 hz
    rw [Finsupp.le_def] at this ⊢
    intro i
    have := this i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega
  intro α hα
  have hβ : (fun i => z⁻¹ * α i) ∈ d.AD (D + d.div z) ⊔ d.Fs :=
    (adeles_eq hd h0 hzD).le (d.mul_mem_adeles z⁻¹ hα)
  have := d.mul_mem_AD_sup_Fs hz0 hβ
  rw [add_sub_cancel_right] at this
  convert this using 1
  funext i; simp [hz0]

theorem Omega_eq_bot_of_degD (hd : d.Axioms) {D0 D : ι →₀ ℤ} (h0 : d.degD D0 - d.ell D0 = d.gamma)
    (hD : d.degD D0 + d.gamma < d.degD D) : d.Omega D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro ω hω
  refine LinearMap.ext fun α => ?_
  exact d.mem_Omega.1 hω α (adeles_le_of_degD hd h0 hD α.2)

/-! ### Dimension of `Ω(D)` -/

theorem card_quot_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    Nat.card (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) = Fintype.card Fq ^ d.iota D := by
  rw [← rI_adeles hd D]
  have e : ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).toAddSubgroup =
      (d.AD D ⊔ d.Fs).toAddSubgroup.comap d.adeles.subtype.toAddMonoidHom := rfl
  have e2 : d.adeles.subtype.toAddMonoidHom.range = d.adeles.toAddSubgroup := by
    ext x; simp
  show ((d.AD D ⊔ d.Fs).comap d.adeles.subtype).toAddSubgroup.index = _
  rw [e, AddSubgroup.index_comap, e2]
  rfl

theorem finite_quot_adeles (hd : d.Axioms) (D : ι →₀ ℤ) :
    Module.Finite Fq (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) := by
  have hc := card_quot_adeles hd D
  have : Finite (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  exact Module.Finite.of_finite

theorem finite_Omega (hd : d.Axioms) (D : ι →₀ ℤ) : Module.Finite Fq (d.Omega D) := by
  have := finite_quot_adeles hd D
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))

/-- `dim_Fq Ω(D) = iota D = ℓ D - deg D + γ`. -/
theorem finrank_Omega (hd : d.Axioms) (D : ι →₀ ℤ) : Module.finrank Fq (d.Omega D) = d.iota D := by
  have := finite_quot_adeles hd D
  have hc := card_quot_adeles hd D
  have h2 : Module.finrank Fq (d.adeles ⧸ (d.AD D ⊔ d.Fs).comap d.adeles.subtype) = d.iota D := by
    rw [Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card] at hc
    exact Nat.pow_right_injective (by have := one_lt_q (Fq := Fq); omega) hc
  rw [← h2, ← Subspace.dual_finrank_eq]
  exact (LinearEquiv.finrank_eq
    (Submodule.dualQuotEquivDualAnnihilator ((d.AD D ⊔ d.Fs).comap d.adeles.subtype))).symm

/-! ### One-dimensionality over `F` -/

/-- Any two Weil differentials, the first nonzero, satisfy `ω₂ = x • ω₁` (Stichtenoth 1.5.9). -/
theorem exists_eq_wsmul (hd : d.Axioms) {ω1 ω2 : Module.Dual Fq d.adeles} {A1 A2 : ι →₀ ℤ}
    (h1 : ω1 ∈ d.Omega A1) (h2 : ω2 ∈ d.Omega A2) (hω1 : ω1 ≠ 0) : ∃ x : F, ω2 = d.wsmul x ω1 := by
  by_cases hω2 : ω2 = 0
  · exact ⟨0, by rw [hω2, zero_wsmul]⟩
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (3 * d.gamma - d.degD A1 - d.degD A2).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hn1 : (n : ℤ) ≥ 3 * d.gamma - d.degD A1 - d.degD A2 + 1 := by omega
  -- dimension of Ω(-B)
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank Fq (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_Omega hd, iota_eq hd, ell_eq_zero_of_degD_neg hd hneg, degD_neg, hdegB]; ring
  have := finite_Omega hd (-B)
  -- the two subspaces
  have hU : ∀ {ω : Module.Dual Fq d.adeles} {A : ι →₀ ℤ}, ω ∈ d.Omega A →
      (d.LD (A + B)).map (d.wsmulL ω) ≤ d.Omega (-B) := by
    rintro ω A hω _ ⟨x, hx, rfl⟩
    refine d.wsmul_mem_Omega (D' := A) ?_ hω
    rwa [sub_neg_eq_add]
  have hdim : ∀ {ω : Module.Dual Fq d.adeles} {A : ι →₀ ℤ}, ω ≠ 0 →
      Module.finrank Fq ((d.LD (A + B)).map (d.wsmulL ω)) = d.ell (A + B) := fun hω =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm
  have hl : ∀ A : ι →₀ ℤ, d.degD A + n * d.deg P - d.gamma ≤ d.ell (A + B) := fun A => by
    have := defect_le_gamma hd (A + B); rw [degD_add, hdegB] at this; linarith
  set U1 := (d.LD (A1 + B)).map (d.wsmulL ω1)
  set U2 := (d.LD (A2 + B)).map (d.wsmulL ω2)
  have hU1 : U1 ≤ d.Omega (-B) := hU h1
  have hU2 : U2 ≤ d.Omega (-B) := hU h2
  have : FiniteDimensional Fq U1 := Submodule.finiteDimensional_of_le hU1
  have : FiniteDimensional Fq U2 := Submodule.finiteDimensional_of_le hU2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U1 U2
  have hsup : Module.finrank Fq ↥(U1 ⊔ U2) ≤ Module.finrank Fq (d.Omega (-B)) :=
    Submodule.finrank_mono (sup_le hU1 hU2)
  rw [hdim hω1, hdim hω2] at hsum
  have hinf : U1 ⊓ U2 ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot, add_zero] at hsum
    have := hl A1
    have := hl A2
    have : (Module.finrank Fq ↥(U1 ⊔ U2) : ℤ) ≤ Module.finrank Fq (d.Omega (-B)) := by exact_mod_cast hsup
    have hs : (Module.finrank Fq ↥(U1 ⊔ U2) : ℤ) = d.ell (A1 + B) + d.ell (A2 + B) := by exact_mod_cast hsum
    nlinarith
  obtain ⟨η, hη, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨⟨x1, -, hx1⟩, ⟨x2, -, hx2⟩⟩ := hη
  simp only [wsmulL_apply] at hx1 hx2
  have hx20 : x2 ≠ 0 := by
    rintro rfl; rw [zero_wsmul] at hx2; exact hη0 hx2.symm
  refine ⟨x1 * x2⁻¹, ?_⟩
  rw [← wsmul_wsmul, hx1, ← hx2, inv_wsmul_wsmul _ hx20]

/-- There is a nonzero Weil differential. -/
theorem exists_weilDiff_ne_zero (hd : d.Axioms) :
    ∃ (ω : Module.Dual Fq d.adeles) (A : ι →₀ ℤ), ω ∈ d.Omega A ∧ ω ≠ 0 := by
  obtain ⟨P⟩ := hd.nonempty
  have hP := hd.deg_pos P
  set n : ℕ := (-d.gamma).toNat + 1 with hn
  set B : ι →₀ ℤ := n • Finsupp.single P 1 with hB
  have hdegB : d.degD B = n * d.deg P := by rw [hB, degD_nsmul, degD_single, one_mul]
  have hnP : (n : ℤ) ≤ n * d.deg P := by
    have : (1 : ℤ) ≤ d.deg P := by exact_mod_cast hP
    nlinarith
  have hneg : d.degD (-B) < 0 := by rw [degD_neg, hdegB]; omega
  have hiota : (Module.finrank Fq (d.Omega (-B)) : ℤ) = n * d.deg P + d.gamma := by
    rw [finrank_Omega hd, iota_eq hd, ell_eq_zero_of_degD_neg hd hneg, degD_neg, hdegB]; ring
  have hne : d.Omega (-B) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hiota
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨ω, -B, hω, hω0⟩

/-! ### The divisor of a Weil differential -/

/-- A nonzero Weil differential `ω` has a divisor `W`: `ω ∈ Ω(D) ↔ D ≤ W`. -/
theorem exists_divisor (hd : d.Axioms) {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) {A : ι →₀ ℤ}
    (hA : ω ∈ d.Omega A) : ∃ W : ι →₀ ℤ, ∀ D, ω ∈ d.Omega D ↔ D ≤ W := by
  obtain ⟨D0, h0⟩ := exists_gamma hd
  have hb : ∀ D, ω ∈ d.Omega D → d.degD D ≤ d.degD D0 + d.gamma := fun D hD => by
    by_contra hlt
    push Not at hlt
    rw [Omega_eq_bot_of_degD hd h0 hlt] at hD
    exact hω ((Submodule.mem_bot _).1 hD)
  obtain ⟨m, ⟨W, hW, rfl⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ D, ω ∈ d.Omega D ∧ d.degD D = m)
    ⟨d.degD D0 + d.gamma, by rintro z ⟨D, hD, rfl⟩; exact hb D hD⟩ ⟨_, A, hA, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun hle => d.Omega_anti hle hW⟩⟩
  have hsup : ω ∈ d.Omega (D ⊔ W) := by rw [Omega_sup]; exact ⟨hD, hW⟩
  have h1 := hm _ ⟨_, hsup, rfl⟩
  have h2 : (D ⊔ W) - W = 0 := by
    apply d.eq_zero_of_degD_eq_zero hd.deg_pos (sub_nonneg.2 le_sup_right)
    have := d.degD_mono (le_sup_right : W ≤ D ⊔ W)
    rw [degD_sub]; linarith
  have : D ⊔ W = W := sub_eq_zero.1 h2
  exact le_sup_left.trans this.le

theorem exists_isCanonical (hd : d.Axioms) : ∃ W : ι →₀ ℤ, d.IsCanonical W := by
  obtain ⟨ω, A, hA, hω⟩ := exists_weilDiff_ne_zero hd
  obtain ⟨W, hW⟩ := exists_divisor hd hω hA
  exact ⟨W, ω, hω, hW⟩

/-- `(x ω) = (x) + (ω)`. -/
theorem isCanonical_add_div {W : ι →₀ ℤ} (hW : d.IsCanonical W) {x : F} (hx : x ≠ 0) :
    d.IsCanonical (W + d.div x) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  refine ⟨d.wsmul x ω, fun h => hω ?_, fun D => ?_⟩
  · rw [← d.inv_wsmul_wsmul hx ω, h, wsmul_zero]
  · rw [d.wsmul_mem_Omega_iff hx, hWω, Finsupp.le_def, Finsupp.le_def]
    refine forall_congr' fun i => ?_
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply]
    omega

/-! ### The Riemann-Roch theorem -/

/-- `Ω(D) = L(W - D) • ω` for `ω` with divisor `W`. -/
theorem map_LD_eq_Omega (hd : d.Axioms) {ω : Module.Dual Fq d.adeles} (hω : ω ≠ 0) {W : ι →₀ ℤ}
    (hW : ∀ D, ω ∈ d.Omega D ↔ D ≤ W) (D : ι →₀ ℤ) :
    (d.LD (W - D)).map (d.wsmulL ω) = d.Omega D := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact d.wsmul_mem_Omega hx ((hW W).2 le_rfl)
  · intro η hη
    obtain ⟨x, rfl⟩ := exists_eq_wsmul hd ((hW W).2 le_rfl) hη hω
    refine ⟨x, ?_, rfl⟩
    by_cases hx : x = 0
    · subst hx; exact zero_mem _
    rw [d.wsmul_mem_Omega_iff hx, hW] at hη
    rw [SetLike.mem_coe, d.mem_LD_iff_div hx, Finsupp.le_def]
    rw [Finsupp.le_def] at hη
    intro i; have := hη i
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega

/-- `dim Ω(D) = ℓ(W - D)`. -/
theorem iota_eq_ell (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    d.iota D = d.ell (W - D) := by
  obtain ⟨ω, hω, hWω⟩ := hW
  rw [← finrank_Omega hd, ← map_LD_eq_Omega hd hω hWω D, ell]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (d.wsmulL_injective hω) _)).symm

/-- **Riemann-Roch**: `ℓ D - ℓ (W - D) = deg D + ℓ 0 - g` (`ℓ 0 = 1` for constant field `Fq`). -/
theorem riemannRoch (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) (D : ι →₀ ℤ) :
    (d.ell D : ℤ) - d.ell (W - D) = d.degD D + d.ell 0 - d.genus := by
  have h1 := iota_eq_ell hd hW D
  have h2 := iota_eq hd D
  have h3 := genus_eq hd
  rw [h1] at h2
  linarith

/-- Riemann's inequality `ℓ D ≥ deg D + ℓ 0 - g`. -/
theorem riemann_inequality (hd : d.Axioms) (D : ι →₀ ℤ) :
    d.degD D + d.ell 0 - d.genus ≤ d.ell D := by
  have := defect_le_gamma hd D
  have := genus_eq hd
  linarith

/-- `ℓ W = g`. -/
theorem ell_canonical (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) : d.ell W = d.genus := by
  have := riemannRoch hd hW 0
  rw [sub_zero, degD_zero] at this
  omega

/-- `deg W = 2g - 2ℓ 0` (`= 2g - 2` for constant field `Fq`). -/
theorem degD_canonical (hd : d.Axioms) {W : ι →₀ ℤ} (hW : d.IsCanonical W) :
    d.degD W = 2 * d.genus - 2 * d.ell 0 := by
  have h1 := riemannRoch hd hW W
  have h2 := ell_canonical hd hW
  rw [sub_self] at h1
  rw [h2] at h1
  linarith

/-- `ℓ D = deg D + ℓ 0 - g` once `deg D > 2g - 2ℓ 0`. -/
theorem ell_eq_of_large_degD (hd : d.Axioms) {D : ι →₀ ℤ}
    (hD : 2 * (d.genus : ℤ) - 2 * d.ell 0 < d.degD D) :
    (d.ell D : ℤ) = d.degD D + d.ell 0 - d.genus := by
  obtain ⟨W, hW⟩ := exists_isCanonical hd
  have h1 := riemannRoch hd hW D
  have h0 : d.ell (W - D) = 0 := by
    apply ell_eq_zero_of_degD_neg hd
    rw [degD_sub, degD_canonical hd hW]; linarith
  rw [h0, Nat.cast_zero, sub_zero] at h1
  exact h1

end Data

end RamanujanPetersson.RR


end

-- ===== S3.RR_C =====
section

/-!
# Riemann-Roch, part C: the concrete instance for function fields

The abstract axioms of `RR_A` (`Data.Axioms`) hold for the places of a function field
`F / Fq` (unit S3-Places): the local index `[ball (n+1) : ball n] = q ^ deg P` (generic
Dedekind lemma `relIndex_ballG`), the product formula, `L(0)` = constants, and the Riemann
input with `B` the pole divisor of `x` and `C` the pole divisor of an integral basis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.RR

/-! ### The local index at a place of a Dedekind domain -/

section LocalIndex

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

/-- The additive subgroup `{f | v_P f ≤ exp n}`. -/
def ballG (P : HeightOneSpectrum S) (n : ℤ) : AddSubgroup K where
  carrier := {f | P.valuation K f ≤ exp n}
  add_mem' {a b} ha hb := ((P.valuation K).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    show P.valuation K (-a) ≤ exp n
    rw [Valuation.map_neg]; exact ha

theorem mem_ballG {P : HeightOneSpectrum S} {n : ℤ} {f : K} :
    f ∈ ballG P n ↔ P.valuation K f ≤ exp n := Iff.rfl

theorem le_exp_neg_one_iff {x : ℤᵐ⁰} : x ≤ exp (-1) ↔ x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = exp k := ⟨log x, (exp_log hx).symm⟩
    rw [exp_le_exp, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]; omega

theorem exists_valuation_eq_exp (P : HeightOneSpectrum S) (k : ℤ) :
    ∃ c : K, P.valuation K c = exp k := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
  have h1 : ∀ m : ℕ, P.valuation K (π ^ m) = exp (-(m : ℤ)) := fun m => by
    rw [map_pow, hπ, ← exp_nsmul]; congr 1; simp
  have h2 : ∀ m : ℕ, P.valuation K (π⁻¹ ^ m) = exp (m : ℤ) := fun m => by
    rw [map_pow, map_inv₀, hπ, ← exp_neg, ← exp_nsmul]; congr 1; simp
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  exacts [⟨_, h2 m⟩, ⟨_, h1 m⟩]

theorem relIndex_ballG_neg_one (P : HeightOneSpectrum S) :
    (ballG (K := K) P (-1)).relIndex (ballG P 0) = Nat.card (S ⧸ P.asIdeal) := by
  let f : S →+ K := (algebraMap S K).toAddMonoidHom
  have hinj : Function.Injective f := IsFractionRing.injective S K
  have hle : ballG (K := K) P (-1) ≤ ballG P 0 := fun x hx =>
    (mem_ballG.1 hx).trans (exp_le_exp.2 (by norm_num))
  have hR : f.range ≤ ballG (K := K) P 0 := by
    rintro _ ⟨a, rfl⟩; exact P.valuation_le_one a
  rw [relIndex_split f.range hle]
  have h1 : ballG (K := K) P 0 ⊓ f.range = (⊤ : AddSubgroup S).map f := by
    rw [inf_eq_right.2 hR, ← AddMonoidHom.range_eq_map]
  have h2 : ballG (K := K) P (-1) ⊓ f.range = P.asIdeal.toAddSubgroup.map f := by
    ext y; constructor
    · rintro ⟨hy, ⟨a, rfl⟩⟩
      exact ⟨a, (P.valuation_lt_one_iff_mem a).1 (le_exp_neg_one_iff.1 hy), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨le_exp_neg_one_iff.2 ((P.valuation_lt_one_iff_mem a).2 ha), a, rfl⟩
  have h3 : ballG (K := K) P 0 ≤ ballG P (-1) ⊔ f.range := by
    intro x hx
    obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_of_integer (mem_ballG.1 hx) 1
    have hmem : x - algebraMap S K a ∈ ballG (K := K) P (-1) := by
      rw [mem_ballG, le_exp_neg_one_iff, Valuation.map_sub_swap]; simpa using ha
    exact AddSubgroup.mem_sup.2 ⟨_, hmem, algebraMap S K a, ⟨a, rfl⟩, sub_add_cancel _ _⟩
  rw [h1, h2, sup_eq_left.2 hR, AddSubgroup.relIndex_eq_one.2 h3, mul_one,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_top_right]
  rfl

/-- The local index `[ball P (n+1) : ball P n] = #(S / P)`. -/
theorem relIndex_ballG (P : HeightOneSpectrum S) (n : ℤ) :
    (ballG (K := K) P n).relIndex (ballG P (n + 1)) = Nat.card (S ⧸ P.asIdeal) := by
  obtain ⟨c, hc⟩ := exists_valuation_eq_exp (K := K) P (-(n + 1))
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (exp_ne_zero hc.symm).elim
  let g : K →+ K := AddMonoidHom.mulLeft c
  have e1 : ballG (K := K) P n = (ballG (K := K) P (-1)).comap g := by
    ext x
    simp only [AddSubgroup.mem_comap, mem_ballG, g, AddMonoidHom.coe_mulLeft, map_mul, hc,
      exp_mul_le_exp_iff]
    rw [show (-1 : ℤ) - -(n + 1) = n by ring]
  have e2 : (ballG (K := K) P (n + 1)).map g = ballG P 0 := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      show P.valuation K (c * x) ≤ exp 0
      rw [map_mul, hc, exp_mul_le_exp_iff, show (0 : ℤ) - -(n + 1) = n + 1 by ring]; exact hx
    · intro hy
      refine ⟨c⁻¹ * y, ?_, ?_⟩
      · show P.valuation K (c⁻¹ * y) ≤ exp (n + 1)
        rw [map_mul, map_inv₀, hc, ← exp_neg, exp_mul_le_exp_iff,
          show n + 1 - -(-(n + 1)) = (0 : ℤ) by ring]; exact hy
      · show c * (c⁻¹ * y) = y
        rw [mul_inv_cancel_left₀ hc0]
  rw [e1, AddSubgroup.relIndex_comap, e2, relIndex_ballG_neg_one]

end LocalIndex

/-! ### The data of a function field -/

section FunctionField

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The valuation at a place. -/
noncomputable def ffv : Places.Place Fq F → Valuation F ℤᵐ⁰ :=
  Sum.elim (fun P => P.valuation F) (fun P => P.valuation F)

variable {Fq F}

theorem ord_eq_neg_log (P : Places.Place Fq F) (f : F) : P.ord f = -log (ffv Fq F P f) := by
  rcases P with P | P <;> rfl

theorem ffv_eq_one {P : Places.Place Fq F} {f : F} (hf : f ≠ 0) (h : P.ord f = 0) :
    ffv Fq F P f = 1 := by
  have hv : ffv Fq F P f ≠ 0 := (Valuation.ne_zero_iff _).2 hf
  rw [ord_eq_neg_log] at h
  rw [← exp_log hv, show log (ffv Fq F P f) = 0 by omega, exp_zero]

variable (Fq F)

/-- The abstract Riemann-Roch data of a function field. -/
noncomputable def ffData : Data Fq F (Places.Place Fq F) where
  v := ffv Fq F
  deg := Places.Place.deg
  v_algebraMap P c hc := by
    have h0 : algebraMap Fq F c ≠ 0 := (_root_.map_ne_zero _).2 hc
    exact ffv_eq_one h0 (Places.ord_eq_zero_of_mem_constField Fq F
      (IntermediateField.algebraMap_mem _ c) h0 P)
  finite_ne_one f hf := by
    refine (Places.div f : Places.Divisor Fq F).support.finite_toSet.subset fun P hP => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Places.div_apply]
    exact fun h => hP (ffv_eq_one hf h)

variable {Fq F}

@[simp] theorem ffData_v (P : Places.Place Fq F) : (ffData Fq F).v P = ffv Fq F P := rfl

@[simp] theorem ffData_deg (P : Places.Place Fq F) : (ffData Fq F).deg P = P.deg := rfl

theorem ffData_div (f : F) : (ffData Fq F).div f = Places.div f := by
  ext P
  rw [Data.div_apply, Places.div_apply, ord_eq_neg_log]; rfl

theorem ffData_degD (D : Places.Divisor Fq F) : (ffData Fq F).degD D = D.deg := rfl

theorem ffData_localIndex (P : Places.Place Fq F) (n : ℤ) :
    rI ((ffData Fq F).ball P n) ((ffData Fq F).ball P (n + 1)) =
      Fintype.card Fq ^ (ffData Fq F).deg P := by
  unfold rI
  rcases P with P | P
  · have e : ∀ m : ℤ, ((ffData Fq F).ball (Sum.inl P) m).toAddSubgroup = ballG P m :=
      fun m => AddSubgroup.ext fun _ => Iff.rfl
    rw [e, e, relIndex_ballG, Places.card_residue_eq Fq]; rfl
  · have e : ∀ m : ℤ, ((ffData Fq F).ball (Sum.inr P) m).toAddSubgroup = ballG P m :=
      fun m => AddSubgroup.ext fun _ => Iff.rfl
    rw [e, e, relIndex_ballG, Places.card_residue_eq Fq]; rfl

theorem ffData_finite_L0 : Finite ((ffData Fq F).LD 0) := by
  have hmem : ∀ f : (ffData Fq F).LD 0, (f : F) ∈ Places.constField Fq F := fun f =>
    Places.mem_constField_of_ord_nonneg Fq F fun P => by
      have h := (ffData Fq F).mem_LD.1 f.2 P
      rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h
      rcases P with P | P
      · exact Places.neg_log_nonneg_of_valuation_le_one P h
      · exact Places.neg_log_nonneg_of_valuation_le_one P h
  have : Finite (Places.constField Fq F) := Module.finite_of_finite Fq
  exact Finite.of_injective (fun f => (⟨f, hmem f⟩ : Places.constField Fq F))
    fun f g h => Subtype.ext (congrArg Subtype.val h :)

/-- The local axioms hold for function fields. -/
theorem ffData_axioms0 : (ffData Fq F).Axioms0 where
  nonempty := ⟨Sum.inr (Places.nonempty_infPlace Fq F).some⟩
  deg_pos := Places.Place.deg_pos
  localIndex := ffData_localIndex
  deg_div f hf := by rw [ffData_div, ffData_degD]; exact Places.deg_div hf
  finite_L0 := ffData_finite_L0

end FunctionField

/-! ### The Riemann input -/

section RiemannInput

/-- If `v x ≤ e` with `1 ≤ e` then `v (p(x)) ≤ e ^ m` for `deg p ≤ m`. -/
theorem Data.v_aeval_le {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)
    (i : ι) {x : F} {e : ℤᵐ⁰} (he : 1 ≤ e) (hx : d.v i x ≤ e) {m : ℕ} {p : Fq[X]}
    (hp : p ∈ degreeLT Fq (m + 1)) : d.v i (aeval x p) ≤ e ^ m := by
  have hdeg : p.natDegree < m + 1 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · exact (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  rw [aeval_eq_sum_range' hdeg]
  refine Valuation.map_sum_le _ fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  by_cases hc : p.coeff j = 0
  · rw [hc, zero_smul, map_zero]; exact zero_le
  · rw [d.v_smul i hc, map_pow]
    exact (pow_le_pow_left₀ zero_le hx j).trans (pow_le_pow_right₀ he hjm)

theorem log_nonpos_iff' {v : ℤᵐ⁰} (hv : v ≠ 0) : log v ≤ 0 ↔ v ≤ 1 := by
  conv_rhs => rw [← exp_log hv]
  rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]

theorem log_nonneg_iff' {v : ℤᵐ⁰} (hv : v ≠ 0) : 0 ≤ log v ↔ 1 ≤ v := by
  conv_rhs => rw [← exp_log hv]
  rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x`. -/
noncomputable def xF : F := algebraMap Fq[X] F X

/-- An `Fq[X]`-basis of the ring of integers `Rfin` (an integral basis). -/
noncomputable def bas : Module.Basis (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) Fq[X]
    (Places.Rfin Fq F) :=
  Module.Free.chooseBasis Fq[X] (Places.Rfin Fq F)

/-- The pole divisor of `x`. -/
noncomputable def poleB : Places.Divisor Fq F := (-(ffData Fq F).div (xF Fq F)) ⊔ 0

/-- The sum of the pole divisors of the integral basis. -/
noncomputable def poleC : Places.Divisor Fq F :=
  ∑ k, ((-(ffData Fq F).div (algebraMap (Places.Rfin Fq F) F (bas Fq F k))) ⊔ 0)

variable {Fq F}

theorem xF_ne_zero : xF Fq F ≠ 0 := by
  rw [xF, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Fq[X] F)]; exact X_ne_zero

theorem aeval_xF (q : Fq[X]) : aeval (xF Fq F) q = algebraMap Fq[X] F q := by
  have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom Fq Fq[X] F) X q
  rw [aeval_X_left_apply, IsScalarTower.coe_toAlgHom'] at this
  exact this

theorem xF_inv_eq : (xF Fq F)⁻¹ = algebraMap (Places.Rinf Fq F) F
    (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F) (Places.piInf Fq)) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Places.Oinf Fq) (RatFunc Fq) F]
  show _ = algebraMap (RatFunc Fq) F (1 / RatFunc.X)
  rw [xF, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F, RatFunc.algebraMap_X, one_div,
    map_inv₀]

theorem ffv_xF_inl (P : HeightOneSpectrum (Places.Rfin Fq F)) :
    ffv Fq F (Sum.inl P) (xF Fq F) ≤ 1 := by
  show P.valuation F (algebraMap Fq[X] F X) ≤ 1
  rw [IsScalarTower.algebraMap_apply Fq[X] (Places.Rfin Fq F) F]
  exact P.valuation_le_one _

theorem one_le_ffv_xF_inr (P : HeightOneSpectrum (Places.Rinf Fq F)) :
    1 ≤ ffv Fq F (Sum.inr P) (xF Fq F) := by
  have h : P.valuation F (xF Fq F)⁻¹ ≤ 1 := by rw [xF_inv_eq]; exact P.valuation_le_one _
  have hv : P.valuation F (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [map_inv₀] at h
  show 1 ≤ P.valuation F (xF Fq F)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF Fq F) = exp k := ⟨_, (exp_log hv).symm⟩
  rw [hk, ← exp_neg, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at h
  rw [hk, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; omega

theorem poleB_nonneg : 0 ≤ poleB Fq F := le_sup_right

theorem poleC_nonneg : 0 ≤ poleC Fq F := Finset.sum_nonneg fun _ _ => le_sup_right

theorem poleB_eq : poleB Fq F = Finsupp.sumElim 0 (-(Places.divS (Places.Rinf Fq F) (xF Fq F))) := by
  ext P
  have hv : ffv Fq F P (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  rcases P with P | P
  · rw [Finsupp.sumElim_inl, Finsupp.coe_zero, Pi.zero_apply]
    exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inl P))
  · rw [Finsupp.sumElim_inr, Finsupp.neg_apply, Places.divS_apply,
      sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inr P)), Places.ord, neg_neg]
    rfl

theorem degS_zero' {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S] :
    Places.degS Fq (0 : HeightOneSpectrum S →₀ ℤ) = 0 := by
  simp [Places.degS]

theorem degD_poleB :
    (ffData Fq F).degD (poleB Fq F) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) := by
  rw [ffData_degD, poleB_eq, Places.Divisor.deg_sumElim, degS_zero', zero_add, ← zero_sub,
    Places.degS_sub, degS_zero', zero_sub]
  have hsum := Places.degS_fin_add_degS_inf Fq F (xF_ne_zero (Fq := Fq) (F := F))
  have hxR : algebraMap Fq[X] (Places.Rfin Fq F) X ≠ 0 := fun h => xF_ne_zero (Fq := Fq) (F := F) (by
    rw [xF, IsScalarTower.algebraMap_apply Fq[X] (Places.Rfin Fq F) F, h, map_zero])
  have e : xF Fq F = algebraMap (Places.Rfin Fq F) F (algebraMap Fq[X] (Places.Rfin Fq F) X) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hfin : Places.degS Fq (Places.divS (Places.Rfin Fq F) (xF Fq F)) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) := by
    rw [e, Places.degS_fin Fq F hxR, ← Places.norm_bridge_fin Fq F,
      Algebra.norm_algebraMap_of_basis (bas Fq F), RatFunc.intDegree_polynomial, natDegree_X_pow]
  omega

theorem ffv_bas_le (k : Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) (P : Places.Place Fq F) :
    (ffData Fq F).v P (algebraMap (Places.Rfin Fq F) F (bas Fq F k)) ≤ exp (poleC Fq F P) := by
  have hbk : algebraMap (Places.Rfin Fq F) F (bas Fq F k) ≠ 0 := fun h =>
    (bas Fq F).ne_zero k (Subtype.ext h)
  rw [(ffData Fq F).v_eq_exp hbk P, exp_le_exp, poleC, Finsupp.finsetSum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ((-(ffData Fq F).div
    (algebraMap (Places.Rfin Fq F) F (bas Fq F k))) ⊔ 0) P)
    (fun k _ => by rw [Finsupp.sup_apply]; exact le_sup_right) (Finset.mem_univ k))
  rw [Finsupp.sup_apply, Finsupp.neg_apply]
  exact le_sup_left

variable (Fq F) in
/-- `p ↦ Σ_k p_k(x) b_k`, polynomials of degree `≤ m` against the integral basis. -/
noncomputable def Phi (m : ℕ) :
    (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F) → degreeLT Fq (m + 1)) →ₗ[Fq] F where
  toFun p := ∑ k, aeval (xF Fq F) (p k : Fq[X]) * algebraMap (Places.Rfin Fq F) F (bas Fq F k)
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c p := by simp [Finset.smul_sum]

theorem Phi_apply (m : ℕ) (p) : Phi Fq F m p =
    ∑ k, aeval (xF Fq F) (p k : Fq[X]) * algebraMap (Places.Rfin Fq F) F (bas Fq F k) := rfl

theorem Phi_mem (m : ℕ) (p) :
    Phi Fq F m p ∈ (ffData Fq F).LD (m • poleB Fq F + poleC Fq F) := by
  rw [Data.mem_LD]
  intro P
  rw [Finsupp.add_apply, Finsupp.smul_apply, exp_add, exp_nsmul, Phi_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  have hB : 0 ≤ poleB Fq F P := poleB_nonneg (Fq := Fq) (F := F) P
  have he : 1 ≤ exp (poleB Fq F P) := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp]; exact hB
  have hx : (ffData Fq F).v P (xF Fq F) ≤ exp (poleB Fq F P) := by
    rw [(ffData Fq F).v_eq_exp xF_ne_zero P, exp_le_exp, poleB, Finsupp.sup_apply,
      Finsupp.neg_apply]
    exact le_sup_left
  exact mul_le_mul' ((ffData Fq F).v_aeval_le P he hx (p k).2) (ffv_bas_le k P)

theorem Phi_injective (m : ℕ) : Function.Injective (Phi Fq F m) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hker : LinearMap.ker (IsScalarTower.toAlgHom Fq[X] (Places.Rfin Fq F) F).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 fun a b h => Subtype.ext h
  have hli := Fintype.linearIndependent_iff.1 ((bas Fq F).linearIndependent.map' _ hker)
    (fun k => (p k : Fq[X])) (by
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
        Algebra.smul_def, ← aeval_xF]
      exact hp)
  funext k
  exact Subtype.ext (hli k)

theorem finrank_dom (m : ℕ) :
    Module.finrank Fq (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F) → degreeLT Fq (m + 1)) =
      Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (m + 1) := by
  let e := (LinearEquiv.piCongrRight fun _ => degreeLTEquiv Fq (m + 1)).trans
    (LinearEquiv.curry Fq Fq (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) (Fin (m + 1))).symm
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]

theorem ell_ge (m : ℕ) :
    Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (m + 1) ≤
      (ffData Fq F).ell (m • poleB Fq F + poleC Fq F) := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) (m • poleB Fq F + poleC Fq F)
  have : Module.Finite Fq ((ffData Fq F).LD (m • poleB Fq F + poleC Fq F)) := Module.Finite.of_finite
  rw [← finrank_dom, Data.ell]
  exact LinearMap.finrank_le_finrank_of_injective (f := (Phi Fq F m).codRestrict _ (Phi_mem m))
    fun p q h => Phi_injective m (congrArg Subtype.val h)

theorem ffData_riemannInput : ∃ B : Places.Divisor Fq F, 0 ≤ B ∧ 0 < (ffData Fq F).degD B ∧
    ∃ C : Places.Divisor Fq F, 0 ≤ C ∧
      ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * (ffData Fq F).degD B - c ≤ (ffData Fq F).ell (n • B + C) := by
  have := (bas Fq F).index_nonempty
  have hpos : 0 < Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) :=
    Fintype.card_pos
  refine ⟨poleB Fq F, poleB_nonneg, ?_, poleC Fq F, poleC_nonneg, 0, fun n => ?_⟩
  · rw [degD_poleB]; exact_mod_cast hpos
  · rw [degD_poleB]
    have h := ell_ge (Fq := Fq) (F := F) n
    have h' : ((Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) * (n + 1) : ℕ) : ℤ)
        ≤ (ffData Fq F).ell (n • poleB Fq F + poleC Fq F) := by exact_mod_cast h
    push_cast at h'
    nlinarith

/-- **The axioms of the abstract theory hold for function fields.** -/
theorem ffData_axioms : (ffData Fq F).Axioms := ⟨ffData_axioms0, ffData_riemannInput⟩

end RiemannInput

/-! ### Riemann-Roch for function fields -/

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- The Riemann-Roch space `L(D)` of a function field (over `Fq`). -/
noncomputable abbrev LF (D : Places.Divisor Fq F) : Submodule Fq F := (ffData Fq F).LD D

variable (Fq F) in
/-- `ℓ(D) = dim_Fq L(D)`. -/
noncomputable abbrev ellF (D : Places.Divisor Fq F) : ℕ := (ffData Fq F).ell D

variable (Fq F) in
/-- The genus of `F` (over `Fq`): `g = dim_Fq A / (A(0) + F)`. -/
noncomputable abbrev genusF : ℕ := (ffData Fq F).genus

variable (Fq F) in
/-- `W` is a canonical divisor of `F` (the divisor of a nonzero Weil differential). -/
abbrev IsCanonicalF (W : Places.Divisor Fq F) : Prop := (ffData Fq F).IsCanonical W

theorem mem_LF {D : Places.Divisor Fq F} {f : F} (hf : f ≠ 0) :
    f ∈ LF Fq F D ↔ 0 ≤ Places.div f + D := by
  rw [(ffData Fq F).mem_LD_iff_div hf, ffData_div]

theorem finiteDimensional_LF (D : Places.Divisor Fq F) : FiniteDimensional Fq (LF Fq F D) := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) D
  exact Module.Finite.of_finite

theorem card_LF (D : Places.Divisor Fq F) :
    Nat.card (LF Fq F D) = Fintype.card Fq ^ ellF Fq F D :=
  Data.card_LD ffData_axioms0 D

/-- `L(0)` is the full constant field. -/
theorem LF_zero_eq :
    LF Fq F 0 = Subalgebra.toSubmodule (Places.constField Fq F).toSubalgebra := by
  ext f
  rw [Data.mem_LD, Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
  constructor
  · intro h
    exact Places.mem_constField_of_ord_nonneg Fq F fun P => by
      have h1 := h P
      rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero] at h1
      rcases P with P | P
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
      · exact Places.neg_log_nonneg_of_valuation_le_one P h1
  · intro hf P
    rw [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
    rcases P with P | P
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (Places.ord_nonneg_of_mem_constField Fq F hf (Sum.inl P))
    · exact Places.valuation_le_one_of_neg_log_nonneg P
        (Places.ord_nonneg_of_mem_constField Fq F hf (Sum.inr P))

/-- `ℓ(0) = [k : Fq]` for the full constant field `k`. -/
theorem ellF_zero : ellF Fq F 0 = Module.finrank Fq (Places.constField Fq F) := by
  rw [ellF, Data.ell, show (ffData Fq F).LD 0 = _ from LF_zero_eq]
  rfl

theorem ellF_zero_of_bot (h : Places.constField Fq F = ⊥) : ellF Fq F 0 = 1 := by
  rw [ellF_zero, h, IntermediateField.finrank_bot]

theorem genusF_eq_iota : genusF Fq F = (ffData Fq F).iota 0 := rfl

theorem exists_isCanonicalF : ∃ W : Places.Divisor Fq F, IsCanonicalF Fq F W :=
  Data.exists_isCanonical ffData_axioms

theorem isCanonicalF_add_div {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) {x : F}
    (hx : x ≠ 0) : IsCanonicalF Fq F (W + Places.div x) := by
  have := (ffData Fq F).isCanonical_add_div hW hx
  rwa [ffData_div] at this

/-- **Riemann-Roch** (general constant field): `ℓ(D) - ℓ(W - D) = deg D + ℓ(0) - g`. -/
theorem riemannRochF {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) (D : Places.Divisor Fq F) :
    (ellF Fq F D : ℤ) - ellF Fq F (W - D) = D.deg + ellF Fq F 0 - genusF Fq F :=
  Data.riemannRoch ffData_axioms hW D

theorem riemann_inequalityF (D : Places.Divisor Fq F) :
    D.deg + ellF Fq F 0 - genusF Fq F ≤ ellF Fq F D :=
  Data.riemann_inequality ffData_axioms D

/-! #### The classical statements (full constant field `Fq`, so `ℓ(0) = 1`) -/

section FullConstantField

variable (hk : Places.constField Fq F = ⊥)
include hk

/-- **Riemann-Roch**: `ℓ(D) - ℓ(W - D) = deg D + 1 - g`. -/
theorem riemannRochF' {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (D : Places.Divisor Fq F) :
    (ellF Fq F D : ℤ) - ellF Fq F (W - D) = D.deg + 1 - genusF Fq F := by
  have := riemannRochF hW D
  rw [ellF_zero_of_bot hk] at this
  exact_mod_cast this

/-- Riemann's inequality `ℓ(D) ≥ deg D + 1 - g`. -/
theorem riemann_inequalityF' (D : Places.Divisor Fq F) :
    D.deg + 1 - genusF Fq F ≤ ellF Fq F D := by
  have := riemann_inequalityF (Fq := Fq) (F := F) D
  rw [ellF_zero_of_bot hk] at this
  exact_mod_cast this

/-- `ℓ(W) = g`. -/
theorem ellF_canonical {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) :
    ellF Fq F W = genusF Fq F :=
  Data.ell_canonical ffData_axioms hW

/-- `deg W = 2g - 2`. -/
theorem degF_canonical {W : Places.Divisor Fq F} (hW : IsCanonicalF Fq F W) :
    W.deg = 2 * (genusF Fq F : ℤ) - 2 := by
  have := Data.degD_canonical ffData_axioms hW
  rw [ffData_degD] at this
  rw [this]
  have h1 := ellF_zero_of_bot hk
  simp only [ellF] at h1
  rw [h1]; push_cast; ring

/-- `ℓ(D) = deg D + 1 - g` for `deg D ≥ 2g - 1`. -/
theorem ellF_eq_of_deg {D : Places.Divisor Fq F} (hD : 2 * (genusF Fq F : ℤ) - 1 ≤ D.deg) :
    (ellF Fq F D : ℤ) = D.deg + 1 - genusF Fq F := by
  have h1 := ellF_zero_of_bot hk
  simp only [ellF] at h1
  have hD' : 2 * ((ffData Fq F).genus : ℤ) - 1 ≤ D.deg := hD
  have := Data.ell_eq_of_large_degD ffData_axioms (D := D) (by
    rw [ffData_degD, h1]; push_cast; omega)
  rw [this, h1, ffData_degD]; push_cast; ring

end FullConstantField

end Concrete

end RamanujanPetersson.RR


end

-- ===== S3.RR_D =====
section

/-!
# Riemann-Roch, part D: the pole-divisor family and constant field extensions

For the separating element `x` with pole divisor `B`, `L(n B) = Rfin ∩ x ^ n Rinf`
(`mem_LF_poleB`). For a constant field extension `F' / L` of `F / Fq` (given in coordinates by an
`Fq`-basis `c` of `L`: the images of `c` form an `F`-basis of `F'`, both rings of integers are spanned
coordinatewise, and `x` is kept), `ℓ'(n B') = ℓ(n B)` for every `n`; hence `ℓ'(0) = ℓ(0)`,
`deg B' = deg B`, the genus is invariant (`IsConstExt.genusF_eq`) and a full constant field stays full.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.RR

theorem mem_range_iff_valuation_le_one {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*}
    [Field K] [Algebra S K] [IsFractionRing S K] (f : K) :
    f ∈ (algebraMap S K).range ↔ ∀ P : HeightOneSpectrum S, P.valuation K f ≤ 1 := by
  refine ⟨?_, HeightOneSpectrum.mem_integers_of_valuation_le_one K f⟩
  rintro ⟨r, rfl⟩ P
  exact P.valuation_le_one r

section PoleFamily

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem poleB_inl (P : HeightOneSpectrum (Places.Rfin Fq F)) : poleB Fq F (Sum.inl P) = 0 := by
  have hv : ffv Fq F (Sum.inl P) (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inl P))

theorem poleB_inr (P : HeightOneSpectrum (Places.Rinf Fq F)) :
    poleB Fq F (Sum.inr P) = log (P.valuation F (xF Fq F)) := by
  have hv : ffv Fq F (Sum.inr P) (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inr P))

/-- `L(n B) = Rfin ∩ x ^ n Rinf` for the pole divisor `B` of `x`. -/
theorem mem_LF_poleB (n : ℕ) (f : F) :
    f ∈ LF Fq F (n • poleB Fq F) ↔ f ∈ (algebraMap (Places.Rfin Fq F) F).range ∧
      f * (xF Fq F)⁻¹ ^ n ∈ (algebraMap (Places.Rinf Fq F) F).range := by
  rw [mem_range_iff_valuation_le_one, mem_range_iff_valuation_le_one, Data.mem_LD, Sum.forall]
  refine and_congr (forall_congr' fun P => ?_) (forall_congr' fun P => ?_)
  · rw [Finsupp.smul_apply, poleB_inl, smul_zero, exp_zero]; rfl
  · have hv : P.valuation F (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF Fq F) = exp k := ⟨_, (exp_log hv).symm⟩
    show P.valuation F f ≤ _ ↔ _
    rw [Finsupp.smul_apply, poleB_inr, hk, log_exp, map_mul, map_pow, map_inv₀, hk, ← exp_neg,
      ← exp_nsmul, mul_comm, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_mul_le_exp_iff, smul_neg,
      sub_neg_eq_add, zero_add]

end PoleFamily

section ConstantFieldExtension

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

/-- `F' / L` is the constant field extension `L F` of `F / Fq`, in coordinates: for an `Fq`-basis
`c` of `L`, the elements `c j` form an `F`-basis of `F'`, an element `Σ f_j c_j` lies in the ring
of integers over `L[x]` (resp. over the valuation ring at `x = ∞`) iff every coordinate `f_j` lies in
the corresponding ring of `F`, and the separating element `x` of `F'` is that of `F`
(`Rfin L F' = L ⊗ Rfin Fq F`, `Rinf L F' = L ⊗ Rinf Fq F`). -/
structure IsConstExt {ι : Type*} [Fintype ι] (c : Module.Basis ι Fq L) : Prop where
  linearIndependent : LinearIndependent F fun j => algebraMap L F' (c j)
  span : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j))
  xF_eq : algebraMap F F' (xF Fq F) = xF L F'
  fin : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rfin L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rfin Fq F) F).range
  inf : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rinf L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rinf Fq F) F).range

variable {Fq L}
variable {ι : Type*} [Fintype ι]

/-- The coordinate map `(f_j) ↦ Σ f_j c_j`. -/
noncomputable def coordMap (c : Module.Basis ι Fq L) : (ι → F) →ₗ[Fq] F' where
  toFun f := ∑ j, f j • algebraMap L F' (c j)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.smul_sum, smul_assoc]

variable {F F'}
variable {c : Module.Basis ι Fq L}

theorem coordMap_apply (f : ι → F) : coordMap F F' c f = ∑ j, f j • algebraMap L F' (c j) := rfl

theorem IsConstExt.mem_LF_iff (h : IsConstExt Fq F L F' c) (n : ℕ) (f : ι → F) :
    coordMap F F' c f ∈ LF L F' (n • poleB L F') ↔ ∀ j, f j ∈ LF Fq F (n • poleB Fq F) := by
  simp only [mem_LF_poleB, coordMap_apply]
  rw [h.fin, ← h.xF_eq]
  have e : (∑ j, f j • algebraMap L F' (c j)) * (algebraMap F F' (xF Fq F))⁻¹ ^ n =
      ∑ j, (f j * (xF Fq F)⁻¹ ^ n) • algebraMap L F' (c j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, map_inv₀]; ring
  rw [e, h.inf, forall_and]

/-- The coordinate isomorphism `L(D)^ι ≃ L'(D')` (over `Fq`) for a pair of divisors whose
Riemann-Roch spaces correspond coordinatewise. -/
noncomputable def IsConstExt.psi (_h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    (ι → LF Fq F D) →ₗ[Fq] LF L F' D' where
  toFun f := ⟨coordMap F F' c fun j => (f j : F), (hD _).2 fun j => (f j).2⟩
  map_add' f g := Subtype.ext (by
    simp only [Pi.add_apply, Submodule.coe_add]
    exact map_add (coordMap F F' c) (fun j => (f j : F)) fun j => (g j : F))
  map_smul' a f := Subtype.ext (by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply]
    exact map_smul (coordMap F F' c) a fun j => (f j : F))

theorem IsConstExt.psi_bijective (h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    Function.Bijective (h.psi hD) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : coordMap F F' c (fun j => (f j : F)) = 0 := congrArg Subtype.val hf
    rw [coordMap_apply] at h0
    funext j
    exact Subtype.ext (Fintype.linearIndependent_iff.1 h.linearIndependent _ h0 j)
  · intro y
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1
      (h.span (Submodule.mem_top (x := (y : F'))))
    have hgy : coordMap F F' c g = y := hg
    have hmem := (hD g).1 (by rw [hgy]; exact y.2)
    exact ⟨fun j => ⟨g j, hmem j⟩, Subtype.ext hgy⟩

/-- **Invariance of `ℓ` under constant field extension**: `ℓ'(D') = ℓ(D)` whenever `L'(D')` is
`L(D)` coordinatewise (`L'(D') = L ⊗ L(D)`). -/
theorem IsConstExt.ellF_eq (h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    ellF L F' D' = ellF Fq F D := by
  have := finiteDimensional_LF (Fq := Fq) (F := F) D
  have : Module.Finite Fq L := Module.Finite.of_finite
  have e1 := (LinearEquiv.ofBijective (h.psi hD) (h.psi_bijective hD)).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Module.finrank_mul_finrank Fq L (LF L F' D'), ← Module.finrank_eq_card_basis c] at e1
  have hpos : 0 < Module.finrank Fq L := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos e1).symm

/-- `ℓ'(n B') = ℓ(n B)` for the pole divisors of `x` in the constant field extension. -/
theorem IsConstExt.ellF_poleB (h : IsConstExt Fq F L F' c) (n : ℕ) :
    ellF L F' (n • poleB L F') = ellF Fq F (n • poleB Fq F) :=
  h.ellF_eq (h.mem_LF_iff n)

theorem IsConstExt.ellF_zero (h : IsConstExt Fq F L F' c) : ellF L F' 0 = ellF Fq F 0 := by
  simpa using h.ellF_poleB 0

/-- A full constant field stays full under constant field extension. -/
theorem IsConstExt.constField_eq_bot (h : IsConstExt Fq F L F' c)
    (hk : Places.constField Fq F = ⊥) : Places.constField L F' = ⊥ := by
  have h1 : ellF L F' 0 = 1 := by rw [h.ellF_zero]; exact ellF_zero_of_bot hk
  rw [RamanujanPetersson.RR.ellF_zero] at h1
  exact IntermediateField.finrank_eq_one_iff.1 h1

end ConstantFieldExtension

end RamanujanPetersson.RR


end

-- ===== S3.SB_Core =====
section

/-!
# Stepanov-Bombieri, abstract core (twisted form)

For abstract Riemann-Roch data `d : Data Fq F ι` (RR_A/RR_B), a ring endomorphism `τ` of `F`
moving the valuations along a permutation `π` of the places, a place `P0` with `deg P0 = ℓ(0)`
(rational over the constant field) and `Q0 = p ^ k` (`p` the characteristic of `F`): every
finite set `T` of places such that `τ f ≡ f ^ (Q0 ^ 2)` at `P` for every `P`-integral `f` satisfies
`Q0 * Σ_{P ∈ T, P ≠ P0} deg P ≤ ℓ(0) * (Q0 (Q0 - 1) + Q0 ^ 2 B)`
as soon as `ℓ(0) B ≥ ℓ(0) Q0 + 2g` and `(g + ℓ(0)) ^ 2 < ℓ(0) ^ 2 Q0`.

Proof (Bombieri): `f_a` (`a ∈ S`) elements of `L((Q0-1) P0)` with pairwise distinct pole orders
`a < Q0` at `P0`; the additive map `g ↦ Σ f_a ^ Q0 τ(g_a)` from `L(B P0) ^ S` to
`L(Q0 (Q0-1) P0 + B π(P0))` has a nonzero kernel element (counting); then
`H = Σ f_a ^ Q0 g_a ^ (Q0 ^ 2) = (Σ f_a g_a ^ Q0) ^ Q0` is nonzero (distinct valuations at `P0`),
has its poles at `P0` only and vanishes to order `≥ Q0` on `T`; `deg div H = 0` gives the bound.
No linearity of `τ` over `Fq` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.ZetaSB

open RR

/-! ### Arithmetic in `ℤᵐ⁰` and `ℤ` -/

theorem lt_exp_iff_le_exp_sub_one {x : ℤᵐ⁰} {n : ℤ} : x < exp n ↔ x ≤ exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = exp k := ⟨log x, (exp_log hx).symm⟩
    rw [exp_lt_exp, exp_le_exp]; omega

theorem pow_le_exp_mul {x : ℤᵐ⁰} {n : ℤ} (h : x ≤ exp n) (k : ℕ) :
    x ^ k ≤ exp ((k : ℤ) * n) := by
  calc x ^ k ≤ (exp n) ^ k := pow_le_pow_left' h k
    _ = exp ((k : ℤ) * n) := by rw [← exp_nsmul, nsmul_eq_mul]

theorem lt_one_of_pow_lt_one {x : ℤᵐ⁰} {k : ℕ} (h : x ^ k < 1) : x < 1 := by
  by_contra hx
  push Not at hx
  exact absurd h (not_lt.2 (one_le_pow_of_one_le' hx k))

/-- `Q0 a + Q0 ^ 2 s = Q0 b + Q0 ^ 2 t` with `a, b < Q0` forces `a = b`. -/
theorem eq_of_mul_add_sq_eq {Q0 a b : ℕ} (hQ : 0 < Q0) (ha : a < Q0) (hb : b < Q0) {s t : ℤ}
    (h : (Q0 : ℤ) * a + (Q0 : ℤ) ^ 2 * s = (Q0 : ℤ) * b + (Q0 : ℤ) ^ 2 * t) : a = b := by
  have hQ' : (0 : ℤ) < Q0 := by exact_mod_cast hQ
  have h1 : (a : ℤ) - b = Q0 * (t - s) := by
    have : (Q0 : ℤ) * ((a : ℤ) - b) = Q0 * (Q0 * (t - s)) := by linear_combination h
    exact mul_left_cancel₀ hQ'.ne' this
  have h2 : (a : ℤ) - b = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨t - s, h1⟩ (by rw [abs_lt]; constructor <;> omega)
  omega

/-! ### Divisor helpers -/

section Core

variable {Fq F ι : Type*} [Field Fq] [Fintype Fq] [Field F] [Algebra Fq F]

theorem degD_sum_single (d : Data Fq F ι) (s : Finset ι) (c : ℤ) :
    d.degD (∑ P ∈ s, Finsupp.single P c) = c * ∑ P ∈ s, (d.deg P : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Data.degD]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, d.degD_add, ih, d.degD_single]; ring

theorem sum_single_apply [DecidableEq ι] (s : Finset ι) (c : ℤ) (i : ι) :
    (∑ P ∈ s, Finsupp.single P c) i = if i ∈ s then c else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

theorem single_sub_one_le (P : ι) (n : ℤ) : Finsupp.single P (n - 1) ≤ Finsupp.single P n := by
  classical
  rw [Finsupp.le_def]
  intro i
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

theorem v_le_one_of_mem_single {d : Data Fq F ι} {P0 P : ι} (hP : P ≠ P0) {c : ℤ} {f : F}
    (hf : f ∈ d.LD (Finsupp.single P0 c)) : d.v P f ≤ 1 := by
  classical
  have := (d.mem_LD.1 hf) P
  rwa [Finsupp.single_apply, if_neg (Ne.symm hP), exp_zero] at this

theorem v_le_exp_of_mem_single {d : Data Fq F ι} {P0 : ι} {c : ℤ} {f : F}
    (hf : f ∈ d.LD (Finsupp.single P0 c)) : d.v P0 f ≤ exp c := by
  have := (d.mem_LD.1 hf) P0
  rwa [Finsupp.single_eq_same] at this

/-! ### Elements with distinct pole orders at `P0` -/

open Classical in
/-- The pole orders `a < n` attained at `P0` by elements of `L(a P0)`. -/
noncomputable def ordSet (d : Data Fq F ι) (P0 : ι) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun a => ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ)

open Classical in
/-- A chosen element of `L(a P0)` with pole order exactly `a` at `P0` (`0` if there is none). -/
noncomputable def ordFun (d : Data Fq F ι) (P0 : ι) (a : ℕ) : F :=
  if h : ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ) then h.choose else 0

theorem mem_ordSet {d : Data Fq F ι} {P0 : ι} {n a : ℕ} :
    a ∈ ordSet d P0 n ↔ a < n ∧ ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ) := by
  classical
  simp [ordSet]

theorem ordFun_spec {d : Data Fq F ι} {P0 : ι} {a : ℕ}
    (h : ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ)) :
    ordFun d P0 a ∈ d.LD (Finsupp.single P0 (a : ℤ)) ∧ d.v P0 (ordFun d P0 a) = exp (a : ℤ) := by
  rw [ordFun, dif_pos h]
  exact h.choose_spec

/-- `ℓ((n-1) P0) ≤ deg P0 · #{pole orders a < n attained at P0}`. -/
theorem ell_single_le {d : Data Fq F ι} (hd : d.Axioms) (P0 : ι) (n : ℕ) :
    d.ell (Finsupp.single P0 ((n : ℤ) - 1)) ≤ d.deg P0 * (ordSet d P0 n).card := by
  classical
  induction n with
  | zero =>
    have h : d.degD (Finsupp.single P0 (((0 : ℕ) : ℤ) - 1)) < 0 := by
      rw [d.degD_single]
      have := hd.deg_pos P0
      push_cast
      have : (0 : ℤ) < d.deg P0 := by exact_mod_cast this
      linarith
    rw [Data.ell_eq_zero_of_degD_neg hd h]
    exact Nat.zero_le _
  | succ n ih =>
    have h2 : ((n + 1 : ℕ) : ℤ) - 1 = n := by push_cast; ring
    rw [h2]
    by_cases hn : ∃ f ∈ d.LD (Finsupp.single P0 (n : ℤ)), d.v P0 f = exp (n : ℤ)
    · have hS : ordSet d P0 (n + 1) = insert n (ordSet d P0 n) := by
        ext a
        simp only [mem_ordSet, Finset.mem_insert]
        constructor
        · rintro ⟨ha, hf⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
          · exact Or.inr ⟨ha, hf⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨ha, hf⟩)
          · exact ⟨Nat.lt_succ_self _, hn⟩
          · exact ⟨Nat.lt_succ_of_lt ha, hf⟩
      have hnot : n ∉ ordSet d P0 n := fun h => (lt_irrefl n) (mem_ordSet.1 h).1
      rw [hS, Finset.card_insert_of_notMem hnot]
      have h1 := (Data.ell_sub_le hd.toAxioms0 (single_sub_one_le P0 (n : ℤ))).1
      rw [d.degD_single, d.degD_single] at h1
      have ih' : (d.ell (Finsupp.single P0 ((n : ℤ) - 1)) : ℤ) ≤ d.deg P0 * (ordSet d P0 n).card := by
        exact_mod_cast ih
      have : (d.ell (Finsupp.single P0 (n : ℤ)) : ℤ) ≤ d.deg P0 * ((ordSet d P0 n).card + 1) := by
        linarith
      exact_mod_cast this
    · have hS : ordSet d P0 (n + 1) = ordSet d P0 n := by
        ext a
        simp only [mem_ordSet]
        constructor
        · rintro ⟨ha, hf⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
          · exact ⟨ha, hf⟩
          · exact absurd hf hn
        · rintro ⟨ha, hf⟩
          exact ⟨Nat.lt_succ_of_lt ha, hf⟩
      have hL : d.LD (Finsupp.single P0 (n : ℤ)) = d.LD (Finsupp.single P0 ((n : ℤ) - 1)) := by
        refine le_antisymm (fun f hf => ?_) (d.LD_mono (single_sub_one_le P0 n))
        rw [Data.mem_LD] at hf ⊢
        intro i
        by_cases hi : i = P0
        · rw [hi]
          have h1 := hf P0
          rw [Finsupp.single_eq_same] at h1 ⊢
          have h3 : d.v P0 f ≠ exp (n : ℤ) := fun h => hn ⟨f, d.mem_LD.2 hf, h⟩
          exact lt_exp_iff_le_exp_sub_one.1 (lt_of_le_of_ne h1 h3)
        · have h1 := hf i
          have hi' : P0 ≠ i := Ne.symm hi
          simp only [Finsupp.single_apply, hi', if_false] at h1 ⊢
          exact h1
      rw [hS]
      have : d.ell (Finsupp.single P0 (n : ℤ)) = d.ell (Finsupp.single P0 ((n : ℤ) - 1)) := by
        unfold Data.ell; rw [hL]
      rw [this]
      exact ih

/-! ### The twisted Stepanov-Bombieri bound -/

/-- **Twisted Stepanov-Bombieri bound (abstract).** -/
theorem twisted_stepanov [DecidableEq ι] {d : Data Fq F ι} (hd : d.Axioms) (p : ℕ) [Fact p.Prime] [CharP F p]
    (k Q0 : ℕ) (hQ0def : Q0 = p ^ k)
    (τ : F →+* F) (π : ι ≃ ι) (hτ : ∀ i f, d.v (π i) (τ f) = d.v i f)
    (hπ : ∀ i, d.deg (π i) = d.deg i)
    (P0 : ι) (hP0 : d.deg P0 = d.ell 0) (B : ℕ)
    (hB : d.ell 0 * Q0 + 2 * d.genus ≤ d.ell 0 * B)
    (hQ0 : (d.genus + d.ell 0) ^ 2 < d.ell 0 ^ 2 * Q0)
    (T : Finset ι)
    (hT : ∀ P ∈ T, P ≠ P0 → ∀ f : F, d.v P f ≤ 1 → d.v P (τ f - f ^ (Q0 ^ 2)) < 1) :
    Q0 * ∑ P ∈ T.erase P0, d.deg P ≤ d.ell 0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * B) := by
  classical
  have hQ0pos : 0 < Q0 := hQ0def ▸ pow_pos (Fact.out : p.Prime).pos k
  have hQ1 : (1 : ℤ) ≤ Q0 := by exact_mod_cast hQ0pos
  have hrpos : 0 < d.ell 0 := hP0 ▸ hd.deg_pos P0
  -- elements with distinct pole orders
  obtain ⟨S, f, hSA, hfS, hSell⟩ : ∃ (S : Finset ℕ) (f : ℕ → F), (∀ a ∈ S, a < Q0) ∧
      (∀ a ∈ S, f a ∈ d.LD (Finsupp.single P0 (a : ℤ)) ∧ d.v P0 (f a) = exp (a : ℤ)) ∧
      d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) ≤ d.deg P0 * S.card :=
    ⟨ordSet d P0 Q0, ordFun d P0, fun a ha => (mem_ordSet.1 ha).1,
      fun a ha => ordFun_spec (mem_ordSet.1 ha).2, ell_single_le hd P0 Q0⟩
  have hf0 : ∀ a ∈ S, f a ≠ 0 := fun a ha h => by
    have := (hfS a ha).2
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  -- the target divisor of the twisted map
  obtain ⟨C, hC⟩ : ∃ C : ι →₀ ℤ, C = Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) +
      Finsupp.single (π P0) (B : ℤ) := ⟨_, rfl⟩
  have hmem : ∀ g : S → d.LD (Finsupp.single P0 (B : ℤ)),
      ∑ a : S, f a ^ Q0 * τ (g a) ∈ d.LD C := by
    intro g
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [Data.mem_LD]
    intro i
    rw [map_mul, map_pow]
    have h1 : d.v i (f a) ^ Q0 ≤ exp (Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) i) := by
      have h0 := (d.mem_LD.1 (hfS a a.2).1) i
      refine (pow_le_exp_mul h0 Q0).trans (exp_le_exp.2 ?_)
      simp only [Finsupp.single_apply]
      split_ifs
      · have := hSA a a.2
        have h5 : ((a : ℕ) : ℤ) ≤ (Q0 : ℤ) - 1 := by omega
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      · simp
    have h2 : d.v i (τ (g a)) ≤ exp (Finsupp.single (π P0) (B : ℤ) i) := by
      obtain ⟨j, rfl⟩ := π.surjective i
      rw [hτ, Finsupp.single_apply_left π.injective]
      exact (d.mem_LD.1 (g a).2) j
    calc d.v i (f a) ^ Q0 * d.v i (τ (g a))
        ≤ exp (Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) i) *
          exp (Finsupp.single (π P0) (B : ℤ) i) := mul_le_mul' h1 h2
      _ = exp (C i) := by rw [← exp_add, hC, Finsupp.add_apply]
  -- the dimension count
  have hcount : d.ell C < S.card * d.ell (Finsupp.single P0 (B : ℤ)) := by
    have hr0 : (0 : ℤ) < d.ell 0 := by exact_mod_cast hrpos
    have hRA := Data.riemann_inequality hd (Finsupp.single P0 ((Q0 : ℤ) - 1))
    have hRB := Data.riemann_inequality hd (Finsupp.single P0 (B : ℤ))
    rw [d.degD_single, hP0] at hRA hRB
    have hdegC : d.degD C = (Q0 : ℤ) * ((Q0 : ℤ) - 1) * d.ell 0 + B * d.ell 0 := by
      rw [hC, d.degD_add, d.degD_single, d.degD_single, hπ, hP0]
    have hB' : (d.ell 0 : ℤ) * Q0 + 2 * d.genus ≤ d.ell 0 * B := by exact_mod_cast hB
    have hQ0' : ((d.genus : ℤ) + d.ell 0) ^ 2 < (d.ell 0 : ℤ) ^ 2 * Q0 := by exact_mod_cast hQ0
    have hG0 : (0 : ℤ) ≤ d.genus := by positivity
    have hlarge : 2 * (d.genus : ℤ) - 2 * d.ell 0 < d.degD C := by
      rw [hdegC]
      have : (0 : ℤ) ≤ (Q0 : ℤ) * ((Q0 : ℤ) - 1) * d.ell 0 :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) hr0.le
      nlinarith
    have hEC := Data.ell_eq_of_large_degD hd hlarge
    rw [hdegC] at hEC
    have hSell' : (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) ≤ d.ell 0 * S.card := by
      rw [← hP0]; exact_mod_cast hSell
    have hbb0 : (0 : ℤ) ≤ d.ell (Finsupp.single P0 (B : ℤ)) := by positivity
    -- `G + r < r Q0`
    have h1 : (d.genus : ℤ) + d.ell 0 < d.ell 0 * Q0 := by
      by_contra hc
      push Not at hc
      have h5 : ((d.ell 0 : ℤ) * Q0) ^ 2 ≤ ((d.genus : ℤ) + d.ell 0) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hc 2
      have h6 : (0 : ℤ) ≤ (d.ell 0 : ℤ) ^ 2 * Q0 * (Q0 - 1) :=
        mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith)
      nlinarith
    have hkey : ((d.ell 0 : ℤ) * Q0 - d.genus) * (d.ell 0 * B + d.ell 0 - d.genus) -
        d.ell 0 * d.ell C = (d.ell 0 : ℤ) ^ 2 * Q0 - ((d.genus : ℤ) + d.ell 0) ^ 2 +
        ((d.ell 0 : ℤ) * B - d.ell 0 * Q0 - 2 * d.genus) * (d.ell 0 * Q0 - d.genus - d.ell 0) := by
      rw [hEC]; ring
    have h7 : (0 : ℤ) ≤ ((d.ell 0 : ℤ) * B - d.ell 0 * Q0 - 2 * d.genus) *
        (d.ell 0 * Q0 - d.genus - d.ell 0) := mul_nonneg (by linarith) (by linarith)
    have h3 : ((d.ell 0 : ℤ) * Q0 - d.genus) * (d.ell 0 * B + d.ell 0 - d.genus) ≤
        ((d.ell 0 : ℤ) * Q0 - d.genus) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h4 : ((d.ell 0 : ℤ) * Q0 - d.genus) * d.ell (Finsupp.single P0 (B : ℤ)) ≤
        (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hbb0
    have h5 : (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) ≤
        (d.ell 0 * S.card : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_right hSell' hbb0
    have h8 : (d.ell 0 : ℤ) * d.ell C < d.ell 0 * (S.card * d.ell (Finsupp.single P0 (B : ℤ))) := by
      nlinarith
    exact_mod_cast lt_of_mul_lt_mul_left h8 hr0.le
  -- a nonzero kernel element, by counting
  haveI : Finite (d.LD C) := Data.finite_LD hd.toAxioms0 C
  let Φ : (S → d.LD (Finsupp.single P0 (B : ℤ))) → d.LD C := fun g => ⟨_, hmem g⟩
  have hnotinj : ¬ Function.Injective Φ := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective Φ hinj
    rw [Nat.card_fun, Data.card_LD hd.toAxioms0, Data.card_LD hd.toAxioms0, ← pow_mul,
      Nat.card_eq_finsetCard] at h1
    have h3 := Nat.pow_lt_pow_right (Data.one_lt_q (Fq := Fq))
      (show d.ell C < d.ell (Finsupp.single P0 (B : ℤ)) * S.card by rw [mul_comm]; exact hcount)
    exact absurd h1 (not_le.2 h3)
  obtain ⟨x, y, hxy, hΦ⟩ : ∃ x y, x ≠ y ∧ Φ x = Φ y := by
    by_contra h
    push Not at h
    exact hnotinj fun x y he => by_contra fun hne => h x y hne he
  obtain ⟨g, hg⟩ : ∃ g : S → F, g = fun a => ((x a : F) - (y a : F)) := ⟨_, rfl⟩
  have hgmem : ∀ a, g a ∈ d.LD (Finsupp.single P0 (B : ℤ)) := fun a => by
    rw [hg]; exact sub_mem (x a).2 (y a).2
  have hgne : ∃ a, g a ≠ 0 := by
    by_contra h
    push Not at h
    apply hxy
    funext a
    apply Subtype.ext
    have := h a
    rw [hg] at this
    exact sub_eq_zero.1 this
  have hker : ∑ a : S, f a ^ Q0 * τ (g a) = 0 := by
    have h1 : (Φ x : F) = Φ y := congrArg Subtype.val hΦ
    have h2 : ∑ a : S, f a ^ Q0 * τ (g a) = (Φ x : F) - Φ y := by
      simp only [Φ, hg, map_sub, mul_sub, Finset.sum_sub_distrib]
    rw [h2, h1, sub_self]
  -- the function `H`
  obtain ⟨H, hH⟩ : ∃ H : F, H = ∑ a : S, f a ^ Q0 * g a ^ (Q0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : F, U = ∑ a : S, f a * g a ^ Q0 := ⟨_, rfl⟩
  have hHU : H = U ^ Q0 := by
    rw [hH, hU, hQ0def, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul (g a), sq]
  -- `H ≠ 0`: the terms have distinct valuations at `P0`
  have hHne : H ≠ 0 := by
    obtain ⟨a0, ha0⟩ := hgne
    have hN : (Finset.univ.filter fun a : S => g a ≠ 0).Nonempty := ⟨a0, by simp [ha0]⟩
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _
      (fun a : S => d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2))) hN
    have hj' : g j ≠ 0 := (Finset.mem_filter.1 hj).2
    have htj : d.v P0 (f j ^ Q0 * g j ^ (Q0 ^ 2)) ≠ 0 :=
      (map_ne_zero _).2 (mul_ne_zero (pow_ne_zero _ (hf0 j j.2)) (pow_ne_zero _ hj'))
    have hval : ∀ a : S, g a ≠ 0 → ∃ s : ℤ,
        d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2)) = exp ((Q0 : ℤ) * (a : ℕ) + (Q0 : ℤ) ^ 2 * s) := by
      intro a ha
      obtain ⟨s, hs⟩ : ∃ s : ℤ, d.v P0 (g a) = exp s :=
        ⟨_, (exp_log ((map_ne_zero _).2 ha)).symm⟩
      refine ⟨s, ?_⟩
      rw [map_mul, map_pow, map_pow, (hfS a a.2).2, hs, ← exp_nsmul, ← exp_nsmul, ← exp_add]
      congr 1
    have hlt : ∀ a ∈ (Finset.univ : Finset S) \ {j},
        d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2)) < d.v P0 (f j ^ Q0 * g j ^ (Q0 ^ 2)) := by
      intro a ha
      have haj : a ≠ j := by simpa using ha
      by_cases hga : g a = 0
      · have h0 : f a ^ Q0 * g a ^ (Q0 ^ 2) = 0 := by
          rw [hga, zero_pow (pow_ne_zero 2 hQ0pos.ne'), mul_zero]
        rw [h0, map_zero]
        exact zero_lt_iff.2 htj
      · refine lt_of_le_of_ne (hjmax a (by simp [hga])) fun heq => haj ?_
        obtain ⟨s1, hs1⟩ := hval a hga
        obtain ⟨s2, hs2⟩ := hval j hj'
        rw [hs1, hs2] at heq
        have := le_antisymm (exp_le_exp.1 heq.le) (exp_le_exp.1 heq.ge)
        exact Subtype.ext (eq_of_mul_add_sq_eq hQ0pos (hSA a a.2) (hSA j j.2) this)
    have hv := Valuation.map_sum_eq_of_lt (d.v P0) (Finset.mem_univ j) hlt
    intro h0
    rw [← hH, h0, map_zero] at hv
    exact htj hv.symm
  -- `v_P H ≤ exp (-Q0)` on `T \ {P0}`
  have hHP : ∀ P ∈ T.erase P0, d.v P H ≤ exp (-(Q0 : ℤ)) := by
    intro P hP
    obtain ⟨hPne, hPT⟩ := Finset.mem_erase.1 hP
    have hH' : H = ∑ a : S, f a ^ Q0 * (g a ^ (Q0 ^ 2) - τ (g a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hker, sub_zero, hH]
    have hlt1 : d.v P H < 1 := by
      rw [hH']
      refine Valuation.map_sum_lt _ one_ne_zero fun a _ => ?_
      rw [map_mul, map_pow]
      have h1 : d.v P (f a) ≤ 1 := v_le_one_of_mem_single hPne (hfS a a.2).1
      have h2 : d.v P (g a) ≤ 1 := v_le_one_of_mem_single hPne (hgmem a)
      have h3 : d.v P (g a ^ (Q0 ^ 2) - τ (g a)) < 1 := by
        rw [Valuation.map_sub_swap]; exact hT P hPT hPne (g a) h2
      calc d.v P (f a) ^ Q0 * d.v P (g a ^ (Q0 ^ 2) - τ (g a))
          ≤ 1 * d.v P (g a ^ (Q0 ^ 2) - τ (g a)) := mul_le_mul' (pow_le_one' h1 Q0) le_rfl
        _ < 1 := by rw [one_mul]; exact h3
    have hU1 : d.v P U < 1 := by
      rw [hHU, map_pow] at hlt1
      exact lt_one_of_pow_lt_one hlt1
    have hU2 : d.v P U ≤ exp (-1) := by
      have := lt_exp_iff_le_exp_sub_one.1 (show d.v P U < exp 0 by rwa [exp_zero])
      simpa using this
    rw [hHU, map_pow]
    have := pow_le_exp_mul hU2 Q0
    simpa using this
  -- `H ∈ L(D')`
  obtain ⟨D', hD'⟩ : ∃ D' : ι →₀ ℤ, D' = Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1) +
      (Q0 : ℤ) ^ 2 * B) - ∑ P ∈ T.erase P0, Finsupp.single P (Q0 : ℤ) := ⟨_, rfl⟩
  have hHmem : H ∈ d.LD D' := by
    rw [Data.mem_LD]
    intro i
    rw [hD', Finsupp.sub_apply, sum_single_apply]
    by_cases hi0 : i = P0
    · rw [hi0, Finsupp.single_eq_same, if_neg (Finset.notMem_erase P0 T), sub_zero, hH]
      refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul, map_pow, map_pow, exp_add]
      have h1 := pow_le_exp_mul (v_le_exp_of_mem_single (hfS a a.2).1) Q0
      have h2 := pow_le_exp_mul (v_le_exp_of_mem_single (hgmem a)) (Q0 ^ 2)
      refine mul_le_mul' (h1.trans (exp_le_exp.2 ?_)) (h2.trans (le_of_eq (by push_cast; ring_nf)))
      have := hSA a a.2
      have h5 : ((a : ℕ) : ℤ) ≤ (Q0 : ℤ) - 1 := by omega
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    · have hs0 : Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1) + (Q0 : ℤ) ^ 2 * B) i = 0 := by
        rw [Finsupp.single_apply, if_neg (Ne.symm hi0)]
      rw [hs0, zero_sub]
      by_cases hiT : i ∈ T.erase P0
      · rw [if_pos hiT]
        exact hHP i hiT
      · rw [if_neg hiT, neg_zero, exp_zero, hH]
        refine Valuation.map_sum_le _ fun a _ => ?_
        rw [map_mul, map_pow, map_pow]
        have h1 : d.v i (f a) ≤ 1 := v_le_one_of_mem_single hi0 (hfS a a.2).1
        have h2 : d.v i (g a) ≤ 1 := v_le_one_of_mem_single hi0 (hgmem a)
        calc d.v i (f a) ^ Q0 * d.v i (g a) ^ (Q0 ^ 2) ≤ 1 * 1 :=
              mul_le_mul' (pow_le_one' h1 Q0) (pow_le_one' h2 _)
          _ = 1 := one_mul 1
  -- `deg D' ≥ 0`
  have hdeg : 0 ≤ d.degD D' := by
    by_contra hneg
    push Not at hneg
    have := Data.LD_eq_bot_of_degD_neg hd hneg
    rw [this, Submodule.mem_bot] at hHmem
    exact hHne hHmem
  rw [hD', d.degD_sub, d.degD_single, degD_sum_single, hP0] at hdeg
  have key : (Q0 : ℤ) * ∑ P ∈ T.erase P0, (d.deg P : ℤ) ≤
      (d.ell 0 : ℤ) * ((Q0 : ℤ) * ((Q0 : ℤ) - 1) + (Q0 : ℤ) ^ 2 * B) := by
    linarith
  zify [(show 1 ≤ Q0 from hQ0pos)]
  push_cast
  linarith

end Core

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_Count =====
section

/-!
# Twisted orbit counting (obligation E2, abstract part)

`G` acts on an `Fq`-algebra `B` by `Fq`-algebra automorphisms, `A → B` with `B^G = A` (`Algebra.IsInvariant`),
`L` a finite field and `φ : L →ₐ[Fq] L`. For `y : B →ₐ[Fq] L` and `g : G` put `twist y g = y ∘ g`.
Main result `sum_card_twisted_eq`:
  `Σ_g #{y | y ∘ g = φ ∘ y} = |G| · #{z : A →ₐ[Fq] L | φ ∘ z = z, z lifts to B}`.
The proof uses only the transitivity of `G` on the lifts of a fixed `z` (`exists_twist_eq`, from Mathlib's
`exists_smul_of_under_eq` and `Ideal.Quotient.stabilizerHom_surjective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace RamanujanPetersson.ZetaSB

section Abstract

variable {Fq : Type*} [CommRing Fq]
variable {B : Type*} [CommRing B] [Algebra Fq B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G Fq B]
variable {L : Type*} [Field L] [Algebra Fq L]

/-- `y ∘ g`. -/
noncomputable def twist (y : B →ₐ[Fq] L) (g : G) : B →ₐ[Fq] L :=
  y.comp (MulSemiringAction.toAlgHom Fq B g)

@[simp] theorem twist_apply (y : B →ₐ[Fq] L) (g : G) (b : B) : twist y g b = y (g • b) := rfl

theorem twist_twist (y : B →ₐ[Fq] L) (g h : G) : twist (twist y g) h = twist y (g * h) := by
  ext b; simp [mul_smul]

theorem twist_one (y : B →ₐ[Fq] L) : twist y (1 : G) = y := by
  ext b; simp

theorem comp_twist (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) (g : G) :
    φ.comp (twist y g) = twist (φ.comp y) g := rfl

variable (A : Type*) [CommRing A] [Algebra Fq A] [Algebra A B] [IsScalarTower Fq A B]

/-- Restriction of a point of `B` to `A`. -/
noncomputable def res (y : B →ₐ[Fq] L) : A →ₐ[Fq] L := y.comp (IsScalarTower.toAlgHom Fq A B)

@[simp] theorem res_apply (y : B →ₐ[Fq] L) (a : A) : res A y a = y (algebraMap A B a) := rfl

theorem res_comp (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) : res A (φ.comp y) = φ.comp (res A y) := rfl

variable [SMulCommClass G A B]

theorem res_twist (y : B →ₐ[Fq] L) (g : G) : res A (twist y g) = res A y := by
  ext a; simp [smul_algebraMap]

variable [Algebra.IsInvariant A B G]

/-- Transitivity: two points of `B` with the same restriction to `A = B^G` differ by an element of `G`. -/
theorem exists_twist_eq [Finite G] [Finite L] (y y' : B →ₐ[Fq] L) (h : res A y = res A y') :
    ∃ g : G, y' = twist y g := by
  classical
  have hQ : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  have hQ' : (RingHom.ker y').IsPrime := RingHom.ker_isPrime y'
  have hunder : (RingHom.ker y).under A = (RingHom.ker y').under A := by
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun z : A →ₐ[Fq] L => z a) h
    simp only [res_apply] at this
    rw [this]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hunder
  set Q' : Ideal B := RingHom.ker y' with hQ'def
  set y1 : B →ₐ[Fq] L := twist y g⁻¹ with hy1
  have hker1 : ∀ b : B, b ∈ Q' ↔ y1 b = 0 := by
    intro b
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, hy1, twist_apply]
  have hker2 : ∀ b : B, b ∈ Q' ↔ y' b = 0 := fun b => RingHom.mem_ker
  set P : Ideal A := Q'.under A with hPdef
  have : Q'.LiesOver P := ⟨rfl⟩
  -- the two induced embeddings of the residue ring
  let ι1 : B ⧸ Q' →+* L := Ideal.Quotient.lift Q' (y1 : B →+* L) (fun b hb => (hker1 b).mp hb)
  let ι2 : B ⧸ Q' →+* L := Ideal.Quotient.lift Q' (y' : B →+* L) (fun b hb => (hker2 b).mp hb)
  have hι1 : ∀ b, ι1 (Ideal.Quotient.mk Q' b) = y1 b := fun b => rfl
  have hι2 : ∀ b, ι2 (Ideal.Quotient.mk Q' b) = y' b := fun b => rfl
  have inj1 : Function.Injective ι1 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hι1] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker1 b).mpr hx)
  have inj2 : Function.Injective ι2 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hι2] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker2 b).mpr hx)
  -- the residue ring is a finite field
  have : Finite (B ⧸ Q') := Finite.of_injective ι1 inj1
  have : Q'.IsMaximal := Ideal.Quotient.maximal_of_isField Q' (Finite.isField_of_domain _)
  letI : Field (B ⧸ Q') := Ideal.Quotient.field Q'
  letI : Fintype (B ⧸ Q') := Fintype.ofFinite _
  letI : Fintype L := Fintype.ofFinite L
  set n := Fintype.card (B ⧸ Q') with hn
  have hn1 : 1 < n := Fintype.one_lt_card
  -- both images are the roots of X^n - X
  set S : Finset L := (Polynomial.X ^ n - Polynomial.X : Polynomial L).roots.toFinset with hS
  have hp0 : (Polynomial.X ^ n - Polynomial.X : Polynomial L) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hn1
  have hScard : S.card ≤ n := by
    calc S.card ≤ (Polynomial.X ^ n - Polynomial.X : Polynomial L).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ n - Polynomial.X : Polynomial L).natDegree := Polynomial.card_roots' _
      _ = n := FiniteField.X_pow_card_sub_X_natDegree_eq L hn1
  have himage : ∀ (ι : B ⧸ Q' →+* L), Function.Injective ι →
      Finset.univ.image ι = S := by
    intro ι hι
    have hsub : Finset.univ.image ι ⊆ S := by
      intro x hx
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, FiniteField.pow_card, sub_self]
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ]
    exact hScard
  have hrange : ∀ u : B ⧸ Q', ∃ v : B ⧸ Q', ι1 v = ι2 u := by
    intro u
    have : ι2 u ∈ Finset.univ.image ι1 := by
      rw [himage ι1 inj1, ← himage ι2 inj2]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ u)
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp this
    exact ⟨v, hv⟩
  choose σf hσf using hrange
  have σinj : Function.Injective σf := by
    intro u u' huu
    apply inj2
    rw [← hσf u, ← hσf u', huu]
  have σbij : Function.Bijective σf := Finite.injective_iff_bijective.mp σinj
  have σmul : ∀ u v, σf (u * v) = σf u * σf v := by
    intro u v; apply inj1; rw [map_mul, hσf, hσf, hσf, map_mul]
  have σadd : ∀ u v, σf (u + v) = σf u + σf v := by
    intro u v; apply inj1; rw [map_add, hσf, hσf, hσf, map_add]
  have σone : σf 1 = 1 := by apply inj1; rw [hσf, map_one, map_one]
  have σzero : σf 0 = 0 := by apply inj1; rw [hσf, map_zero, map_zero]
  let σh : (B ⧸ Q') →+* (B ⧸ Q') :=
    { toFun := σf, map_one' := σone, map_mul' := σmul, map_zero' := σzero, map_add' := σadd }
  let σr : (B ⧸ Q') ≃+* (B ⧸ Q') := RingEquiv.ofBijective σh σbij
  have hσr : ∀ u, ι1 (σr u) = ι2 u := fun u => hσf u
  have σcomm : ∀ x : A ⧸ P, σr (algebraMap (A ⧸ P) (B ⧸ Q') x) = algebraMap (A ⧸ P) (B ⧸ Q') x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply inj1
    rw [hσr, Ideal.Quotient.algebraMap_mk_of_liesOver, hι1, hι2, hy1, twist_apply, smul_algebraMap]
    have := congrArg (fun z : A →ₐ[Fq] L => z a) h
    simpa only [res_apply] using this.symm
  let σa : (B ⧸ Q') ≃ₐ[A ⧸ P] (B ⧸ Q') := AlgEquiv.ofRingEquiv (f := σr) σcomm
  obtain ⟨⟨s, hs⟩, hsσ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q' σa
  refine ⟨g⁻¹ * s, ?_⟩
  ext b
  have h1 := congrArg (fun e : (B ⧸ Q') ≃ₐ[A ⧸ P] (B ⧸ Q') => e (Ideal.Quotient.mk Q' b)) hsσ
  simp only [Ideal.Quotient.stabilizerHom_apply] at h1
  -- h1 : mk (s • b) = σa (mk b)
  have h2 : ι1 (Ideal.Quotient.mk Q' (s • b)) = ι2 (Ideal.Quotient.mk Q' b) := by
    rw [show s • b = (⟨s, hs⟩ : MulAction.stabilizer G Q') • b from rfl, h1]; exact hσr _
  rw [hι1, hι2, hy1, twist_apply] at h2
  rw [twist_apply, mul_smul, ← h2]

/-- For a point `y` with `y ∘ t₀ = φ ∘ y`, the twisted solutions are a coset of the stabiliser. -/
theorem card_twistSet_eq [Fintype G] [DecidableEq (B →ₐ[Fq] L)] (φ : L →ₐ[Fq] L) (y : B →ₐ[Fq] L) (t0 : G)
    (ht0 : twist y t0 = φ.comp y) :
    (Finset.univ.filter fun t : G => twist y t = φ.comp y).card =
      (Finset.univ.filter fun s : G => twist y s = y).card := by
  symm
  refine Finset.card_nbij' (fun s => s * t0) (fun t => t * t0⁻¹) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
    rw [← twist_twist, hs, ht0]
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    rw [← twist_twist, ht, ← ht0, twist_twist, mul_inv_cancel, twist_one]
  · intro s _; simp
  · intro t _; simp

/-- The stabilisers along one fibre of `res` add up to `|G|`. -/
theorem sum_card_stab_fiber [Fintype G] [Finite L] [Fintype (B →ₐ[Fq] L)] [DecidableEq (B →ₐ[Fq] L)]
    [DecidableEq (A →ₐ[Fq] L)] (y0 : B →ₐ[Fq] L) :
    ∑ y ∈ Finset.univ.filter (fun y : B →ₐ[Fq] L => res A y = res A y0),
      (Finset.univ.filter fun s : G => twist y s = y).card = Fintype.card G := by
  classical
  have hk : ∀ y : B →ₐ[Fq] L, ∃ k : G, res A y = res A y0 → y = twist y0 k := by
    intro y
    by_cases hy : res A y = res A y0
    · obtain ⟨k, hk⟩ := exists_twist_eq (G := G) A y0 y hy.symm
      exact ⟨k, fun _ => hk⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose k hk using hk
  rw [← Finset.card_sigma]
  rw [← Finset.card_univ (α := G)]
  refine Finset.card_nbij' (fun p => k p.1 * p.2)
    (fun h => ⟨twist y0 h, (k (twist y0 h))⁻¹ * h⟩) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro h _
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
    refine ⟨res_twist A y0 h, ?_⟩
    have e := hk (twist y0 h) (res_twist A y0 h)
    calc twist (twist y0 h) ((k (twist y0 h))⁻¹ * h)
        = twist (twist y0 (k (twist y0 h))) ((k (twist y0 h))⁻¹ * h) := by rw [← e]
      _ = twist y0 h := by rw [twist_twist, mul_inv_cancel_left]
  · rintro ⟨y, s⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp
    obtain ⟨hy, hs⟩ := hp
    have e : twist y0 (k y * s) = y := by rw [← twist_twist, ← hk y hy, hs]
    simp only [e, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro h _
    simp only [mul_inv_cancel_left]

/-- Twisted counting identity. -/
theorem sum_card_twisted_eq [Fintype G] [Finite L] [Fintype (B →ₐ[Fq] L)] [Fintype (A →ₐ[Fq] L)]
    [DecidableEq (B →ₐ[Fq] L)] [DecidableEq (A →ₐ[Fq] L)] (φ : L →ₐ[Fq] L) :
    ∑ g : G, (Finset.univ.filter fun y : B →ₐ[Fq] L => twist y g = φ.comp y).card =
      ∑ z ∈ Finset.univ.filter (fun z : A →ₐ[Fq] L => φ.comp z = z),
        (if ∃ y : B →ₐ[Fq] L, res A y = z then Fintype.card G else 0) := by
  classical
  calc ∑ g : G, (Finset.univ.filter fun y : B →ₐ[Fq] L => twist y g = φ.comp y).card
      = ∑ y : B →ₐ[Fq] L, (Finset.univ.filter fun g : G => twist y g = φ.comp y).card := by
        simp only [Finset.card_filter]; exact Finset.sum_comm
    _ = ∑ z : A →ₐ[Fq] L, ∑ y ∈ Finset.univ.filter (fun y : B →ₐ[Fq] L => res A y = z),
          (Finset.univ.filter fun g : G => twist y g = φ.comp y).card :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ z ∈ Finset.univ.filter (fun z : A →ₐ[Fq] L => φ.comp z = z),
          (if ∃ y : B →ₐ[Fq] L, res A y = z then Fintype.card G else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hz : φ.comp z = z
        · rw [if_pos hz]
          by_cases hex : ∃ y : B →ₐ[Fq] L, res A y = z
          · rw [if_pos hex]
            obtain ⟨y0, rfl⟩ := hex
            rw [← sum_card_stab_fiber A y0]
            refine Finset.sum_congr rfl fun y hy => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            have hφy : res A (φ.comp y) = res A y := by rw [res_comp, hy, hz]
            obtain ⟨t0, ht0⟩ := exists_twist_eq (G := G) A y (φ.comp y) hφy.symm
            exact card_twistSet_eq φ y t0 ht0.symm
          · rw [if_neg hex]
            refine Finset.sum_eq_zero fun y hy => ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            exact absurd ⟨y, hy⟩ hex
        · rw [if_neg hz]
          refine Finset.sum_eq_zero fun y hy => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t _ ht
          apply hz
          rw [← hy, ← res_comp, ← ht, res_twist]

end Abstract

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_Transport =====
section

/-!
# Transport of places along automorphisms of a function field (obligation O1)

`σ : F ≃ₐ[RatFunc Fq] F` restricts to ring automorphisms of `Rfin` and `Rinf`, hence permutes the
places (`placeMap σ`), preserving degrees and valuations: `v_{σ P} (σ f) = v_P f`. These are the
hypotheses `hτ`, `hπ` of `twisted_stepanov` (SB_Core) for `τ = σ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.ZetaSB

open RR

/-- Elements of `ℤᵐ⁰` below `1` are determined by their comparisons with `exp (-n)`. -/
theorem le_of_forall_le_exp_neg {x y : ℤᵐ⁰} (hy : y ≤ 1)
    (h : ∀ n : ℕ, y ≤ exp (-(n : ℤ)) → x ≤ exp (-(n : ℤ))) : x ≤ y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · by_contra hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx le_rfl
    obtain ⟨a, rfl⟩ : ∃ a : ℤ, x = exp a := ⟨_, (exp_log hx0).symm⟩
    have h1 := h (1 - a).toNat zero_le
    rw [exp_le_exp] at h1
    omega
  · obtain ⟨b, rfl⟩ : ∃ b : ℤ, y = exp b := ⟨_, (exp_log hy0).symm⟩
    have hl : b ≤ 0 := by rw [← exp_zero, exp_le_exp] at hy; exact hy
    have h1 := h (-b).toNat (by rw [Int.toNat_of_nonneg (by omega), neg_neg])
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at h1

theorem eq_of_forall_le_exp_neg_iff {x y : ℤᵐ⁰} (hx : x ≤ 1) (hy : y ≤ 1)
    (h : ∀ n : ℕ, x ≤ exp (-(n : ℤ)) ↔ y ≤ exp (-(n : ℤ))) : x = y :=
  le_antisymm (le_of_forall_le_exp_neg hy fun n hn => (h n).mpr hn)
    (le_of_forall_le_exp_neg hx fun n hn => (h n).mp hn)

section Generic

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
variable {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K]

theorem equiv_asIdeal (e : S ≃+* S) (P : HeightOneSpectrum S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = P.asIdeal.map e := by
  rw [← Ideal.comap_symm]; rfl

theorem mem_equiv_pow_iff (e : S ≃+* S) (P : HeightOneSpectrum S) (r : S) (n : ℕ) :
    e r ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ r ∈ P.asIdeal ^ n := by
  rw [equiv_asIdeal, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]
  simp

theorem intValuation_equiv (e : S ≃+* S) (P : HeightOneSpectrum S) (r : S) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  refine eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    mem_equiv_pow_iff]

/-- Valuations are transported along a ring automorphism `σ` of `K` restricting to `e` on `S`. -/
theorem valuation_equiv (e : S ≃+* S) (σ : K →+* K)
    (hσ : ∀ r : S, σ (algebraMap S K r) = algebraMap S K (e r)) (P : HeightOneSpectrum S) (f : K) :
    (HeightOneSpectrum.equivOfRingEquiv e P).valuation K (σ f) = P.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  rw [map_div₀, hσ, hσ, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_equiv, intValuation_equiv]

variable (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra Fq S] [Places.FiniteQuot S]

theorem deg_equiv (e : S ≃+* S) (P : HeightOneSpectrum S) :
    Places.deg Fq (HeightOneSpectrum.equivOfRingEquiv e P) = Places.deg Fq P := by
  have hc : Nat.card (S ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal) =
      Nat.card (S ⧸ P.asIdeal) :=
    (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ e (equiv_asIdeal e P)).toEquiv).symm
  rw [Places.card_residue_eq Fq, Places.card_residue_eq Fq] at hc
  exact Nat.pow_right_injective (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance) hc

end Generic

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `σ` restricted to the finite integral closure `Rfin`. -/
noncomputable def finEquiv (σ : F ≃ₐ[RatFunc Fq] F) : Places.Rfin Fq F ≃+* Places.Rfin Fq F :=
  ((σ.restrictScalars Fq[X]).mapIntegralClosure :
    integralClosure Fq[X] F ≃ₐ[Fq[X]] integralClosure Fq[X] F).toRingEquiv

/-- `σ` restricted to the infinite integral closure `Rinf`. -/
noncomputable def infEquiv (σ : F ≃ₐ[RatFunc Fq] F) : Places.Rinf Fq F ≃+* Places.Rinf Fq F :=
  ((σ.restrictScalars (Places.Oinf Fq)).mapIntegralClosure :
    integralClosure (Places.Oinf Fq) F ≃ₐ[Places.Oinf Fq] integralClosure (Places.Oinf Fq) F).toRingEquiv

@[simp] theorem coe_finEquiv (σ : F ≃ₐ[RatFunc Fq] F) (r : Places.Rfin Fq F) :
    ((finEquiv σ r : Places.Rfin Fq F) : F) = σ r := rfl

@[simp] theorem coe_infEquiv (σ : F ≃ₐ[RatFunc Fq] F) (r : Places.Rinf Fq F) :
    ((infEquiv σ r : Places.Rinf Fq F) : F) = σ r := rfl

/-- The permutation of the places induced by `σ`. -/
noncomputable def placeMap (σ : F ≃ₐ[RatFunc Fq] F) : Places.Place Fq F ≃ Places.Place Fq F :=
  Equiv.sumCongr (HeightOneSpectrum.equivOfRingEquiv (finEquiv σ))
    (HeightOneSpectrum.equivOfRingEquiv (infEquiv σ))

theorem ffv_placeMap (σ : F ≃ₐ[RatFunc Fq] F) (P : Places.Place Fq F) (f : F) :
    ffv Fq F (placeMap σ P) (σ f) = ffv Fq F P f := by
  rcases P with P | P
  · exact valuation_equiv (finEquiv σ) (σ : F →+* F) (fun r => rfl) P f
  · exact valuation_equiv (infEquiv σ) (σ : F →+* F) (fun r => rfl) P f

theorem deg_placeMap (σ : F ≃ₐ[RatFunc Fq] F) (P : Places.Place Fq F) :
    (placeMap σ P).deg = P.deg := by
  rcases P with P | P
  · exact deg_equiv Fq (finEquiv σ) P
  · exact deg_equiv Fq (infEquiv σ) P

/-- The twisted Stepanov bound for an automorphism `σ` of `F` over `RatFunc Fq`. -/
theorem twisted_stepanovF [DecidableEq (Places.Place Fq F)] (σ : F ≃ₐ[RatFunc Fq] F) (p : ℕ) [Fact p.Prime] [CharP F p]
    (k Q0 : ℕ) (hQ0def : Q0 = p ^ k) (P0 : Places.Place Fq F) (hP0 : P0.deg = ellF Fq F 0) (B : ℕ)
    (hB : ellF Fq F 0 * Q0 + 2 * genusF Fq F ≤ ellF Fq F 0 * B)
    (hQ0 : (genusF Fq F + ellF Fq F 0) ^ 2 < ellF Fq F 0 ^ 2 * Q0) (T : Finset (Places.Place Fq F))
    (hT : ∀ P ∈ T, P ≠ P0 → ∀ f : F, ffv Fq F P f ≤ 1 → ffv Fq F P (σ f - f ^ (Q0 ^ 2)) < 1) :
    Q0 * ∑ P ∈ T.erase P0, P.deg ≤ ellF Fq F 0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * B) := by
  exact twisted_stepanov ffData_axioms p k Q0 hQ0def (σ : F →+* F) (placeMap σ)
    (fun P f => ffv_placeMap σ P f) (fun P => deg_placeMap σ P) P0 hP0 B hB hQ0 T hT

end FF

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_GalA =====
section

/-!
# S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound

For a function field `E` over `Fq` that is Galois over `K = RatFunc Fq` with group `G`:
* `G` acts on `Rfin Fq E` (`galActRfin`), invariantly over `Fq[X]` (`isInvariant_poly`);
* an `L`-valued point `y` with `y ∘ g = Frob^m ∘ y` has a kernel `P` on which `g f ≡ f ^ (q ^ m)`
  (`valuation_twist_lt`), so twisted Stepanov bounds the number of such points
  (`card_twisted_le`): `N(g) ≤ ℓ0 (q ^ m + (2 g_E + 1) q ^ (m/2))`;
* if `ℓ0 ∣ m`, `N(g) = 0` unless `g` fixes the constant field (`fix_const_of_twist`).
-/

set_option autoImplicit false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.ZetaSB

open RR

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

instance smulCommClass_gal_poly : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] E where
  smul_comm g a x := by
    change g (a • x) = a • g x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) E,
      AlgEquiv.commutes]

noncomputable instance galActRfin : MulSemiringAction (E ≃ₐ[RatFunc Fq] E) (Places.Rfin Fq E) :=
  inferInstanceAs (MulSemiringAction (E ≃ₐ[RatFunc Fq] E) (integralClosure Fq[X] E))

instance smulCommClass_gal_poly_Rfin : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] (Places.Rfin Fq E) :=
  inferInstanceAs (SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] (integralClosure Fq[X] E))

theorem coe_gal_smul (g : E ≃ₐ[RatFunc Fq] E) (b : Places.Rfin Fq E) :
    ((g • b : Places.Rfin Fq E) : E) = g (b : E) := rfl

theorem gal_algebraMap_Fq (g : E ≃ₐ[RatFunc Fq] E) (c : Fq) : g (algebraMap Fq E c) = algebraMap Fq E c := by
  rw [IsScalarTower.algebraMap_apply Fq (RatFunc Fq) E, AlgEquiv.commutes]

instance smulCommClass_gal_Fq_Rfin : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq (Places.Rfin Fq E) where
  smul_comm g c b := by
    apply Subtype.ext
    change g ((c • b : Places.Rfin Fq E) : E) = ((c • (g • b) : Places.Rfin Fq E) : E)
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, coe_gal_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
      gal_algebraMap_Fq]

/-- Fixed points of the full Galois group in `Rfin` are polynomials. -/
theorem isInvariant_poly [IsGalois (RatFunc Fq) E] :
    Algebra.IsInvariant Fq[X] (Places.Rfin Fq E) (E ≃ₐ[RatFunc Fq] E) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ g : E ≃ₐ[RatFunc Fq] E, g (b : E) = b := fun g => congrArg Subtype.val (hb g)
  have hmem : (b : E) ∈ (⊥ : IntermediateField (RatFunc Fq) E) := by
    rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (RatFunc Fq) E)]
    exact fun g => hfix g
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hint : IsIntegral Fq[X] c := by
    have h2 : IsIntegral Fq[X] (b : E) := b.2
    rw [← hc] at h2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom Fq[X] (RatFunc Fq) E)
      (algebraMap (RatFunc Fq) E).injective).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha, ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) E]
  rfl

/-- If `g • b ≡ b ^ Q` modulo `P` for every integral `b` (with `Q` a power of the characteristic),
then `g f ≡ f ^ Q` at `P` for every `P`-integral `f`. -/
theorem valuation_twist_lt (g : E ≃ₐ[RatFunc Fq] E) (P : HeightOneSpectrum (Places.Rfin Fq E))
    (p k : ℕ) [hp : Fact p.Prime] [CharP E p]
    (h : ∀ b : Places.Rfin Fq E, g • b - b ^ (p ^ k) ∈ P.asIdeal) (f : E) (hf : P.valuation E f ≤ 1) :
    P.valuation E (g f - f ^ (p ^ k)) < 1 := by
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  have hfixP : HeightOneSpectrum.equivOfRingEquiv (finEquiv g) P = P := by
    have := P.isMaximal
    apply HeightOneSpectrum.ext
    rw [equiv_asIdeal]
    have hle : P.asIdeal.map (finEquiv g) ≤ P.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap]
      have h1 := h b
      have h2 : b ^ (p ^ k) ∈ P.asIdeal := Ideal.pow_mem_of_mem _ hb _ hpk
      have h3 : finEquiv g b = (g • b - b ^ (p ^ k)) + b ^ (p ^ k) := by
        rw [sub_add_cancel]; rfl
      rw [h3]; exact Ideal.add_mem _ h1 h2
    exact (Ideal.map_isMaximal_of_equiv (finEquiv g) (p := P.asIdeal)).eq_of_le P.isMaximal.ne_top hle
  have hv : ∀ x : E, P.valuation E (g x) = P.valuation E x := by
    intro x
    have := valuation_equiv (finEquiv g) (g : E →+* E) (fun r => rfl) P x
    rwa [hfixP] at this
  obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_of_integer hf (1 : (ℤᵐ⁰)ˣ)
  obtain ⟨e, he, hfe⟩ : ∃ e : E, P.valuation E e < 1 ∧ f = algebraMap (Places.Rfin Fq E) E a + e :=
    ⟨f - algebraMap (Places.Rfin Fq E) E a, by rw [Valuation.map_sub_swap]; simpa using ha, by ring⟩
  subst hfe
  have hfrob : ∀ x y : E, (x + y) ^ (p ^ k) = x ^ (p ^ k) + y ^ (p ^ k) := fun x y => add_pow_char_pow x y p k
  have h1 : P.valuation E (algebraMap (Places.Rfin Fq E) E (g • a - a ^ (p ^ k))) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h a
  have h2 : P.valuation E (g e - e ^ (p ^ k)) < 1 := by
    refine Valuation.map_sub_lt _ (by rw [hv]; exact he) ?_
    rw [map_pow]; exact pow_lt_one₀ zero_le he hpk.ne'
  have hsplit : g (algebraMap (Places.Rfin Fq E) E a + e) - (algebraMap (Places.Rfin Fq E) E a + e) ^ (p ^ k) =
      algebraMap (Places.Rfin Fq E) E (g • a - a ^ (p ^ k)) + (g e - e ^ (p ^ k)) := by
    rw [hfrob, map_add, map_sub, map_pow]
    change g (a : E) + g e - ((a : E) ^ (p ^ k) + e ^ (p ^ k)) =
      ((g • a : Places.Rfin Fq E) : E) - (a : E) ^ (p ^ k) + (g e - e ^ (p ^ k))
    rw [coe_gal_smul]; ring
  rw [hsplit]; exact Valuation.map_add_lt _ h1 h2

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- The kernel of a twisted Frobenius point satisfies the congruence of `valuation_twist_lt`. -/
theorem sub_mem_kerPlace (g : E ≃ₐ[RatFunc Fq] E) (Q : ℕ) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ Q)
    (y : Places.Rfin Fq E →ₐ[Fq] L) (hy : twist y g = φ.comp y) (b : Places.Rfin Fq E) :
    g • b - b ^ Q ∈ (Places.kerPlace Fq L y).asIdeal := by
  change g • b - b ^ Q ∈ RingHom.ker y
  rw [RingHom.mem_ker, map_sub, map_pow]
  have := congrArg (fun z : Places.Rfin Fq E →ₐ[Fq] L => z b) hy
  simp only [twist_apply, AlgHom.comp_apply, hφ] at this
  rw [this, sub_self]

/-- Twisted points are at most the total degree of their kernels. -/
theorem card_twisted_le_sum [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    [DecidableEq (HeightOneSpectrum (Places.Rfin Fq E))] (g : E ≃ₐ[RatFunc Fq] E) (φ : L →ₐ[Fq] L) :
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card ≤
      ∑ P ∈ (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).image
        (Places.kerPlace Fq L), Places.deg Fq P := by
  classical
  rw [Finset.card_eq_sum_card_image (Places.kerPlace Fq L)]
  refine Finset.sum_le_sum fun P _ => ?_
  calc _ ≤ (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => Places.kerPlace Fq L y = P).card :=
        Finset.card_le_card fun y hy => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy.2
    _ = Nat.card {y : Places.Rfin Fq E →ₐ[Fq] L // Places.kerPlace Fq L y = P} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ Places.deg Fq P := by
        rw [Places.card_fiber]; split_ifs <;> simp

/-- **Twisted point bound.** `N(g) ≤ ℓ0 (Q0 ^ 2 + (2 g + 1) Q0)` when `φ = Frob_{Q0 ^ 2}`, `Q0 = p ^ k`,
`E` has a place `P0` of degree `ℓ0 = ℓ(0)` and `(g + ℓ0) ^ 2 < ℓ0 ^ 2 Q0`. -/
theorem card_twisted_le [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    (g : E ≃ₐ[RatFunc Fq] E) (p : ℕ) [hp : Fact p.Prime] [CharP E p] (k Q0 : ℕ) (hQ0def : Q0 = p ^ k)
    (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Q0 ^ 2))
    (P0 : Places.Place Fq E) (hP0 : P0.deg = ellF Fq E 0)
    (hQ0 : (genusF Fq E + ellF Fq E 0) ^ 2 < ellF Fq E 0 ^ 2 * Q0) :
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card ≤
      ellF Fq E 0 * (Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0) := by
  classical
  set s := Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y with hs
  set T := s.image (Places.kerPlace Fq L) with hT
  set T' : Finset (Places.Place Fq E) := T.map Function.Embedding.inl with hT'
  set ℓ0 := ellF Fq E 0 with hℓ0
  set gE := genusF Fq E with hgE
  have hQ2 : Q0 ^ 2 = p ^ (k * 2) := by rw [hQ0def, ← pow_mul]
  have hℓpos : 1 ≤ ℓ0 := by
    rcases Nat.eq_zero_or_pos ℓ0 with h0 | h0
    · rw [h0] at hQ0; simp at hQ0
    · exact h0
  have hB : ℓ0 * Q0 + 2 * gE ≤ ℓ0 * (Q0 + 2 * gE) := by rw [mul_add]; nlinarith
  have hmain := twisted_stepanovF g p k Q0 hQ0def P0 hP0 (Q0 + 2 * gE) hB hQ0 T' (by
      intro P hP _ f hf
      rw [hT', Finset.mem_map] at hP
      obtain ⟨P', hP', rfl⟩ := hP
      rw [hT, Finset.mem_image] at hP'
      obtain ⟨y, hy, rfl⟩ := hP'
      rw [hs, Finset.mem_filter] at hy
      change (Places.kerPlace Fq L y).valuation E (g f - f ^ (Q0 ^ 2)) < 1
      rw [hQ2]
      refine valuation_twist_lt g _ p (k * 2) (fun b => ?_) f hf
      rw [← hQ2]
      exact sub_mem_kerPlace L g (Q0 ^ 2) φ hφ y hy.2 b)
  have hle := card_twisted_le_sum L g φ
  rw [← hs, ← hT] at hle
  have hsumT : ∑ P ∈ T, Places.deg Fq P = ∑ P ∈ T', P.deg := by
    rw [hT', Finset.sum_map]; rfl
  have hsplit : ∑ P ∈ T', P.deg ≤ ∑ P ∈ T'.erase P0, P.deg + ℓ0 := by
    by_cases hP0T : P0 ∈ T'
    · rw [← Finset.add_sum_erase _ _ hP0T, hP0, add_comm]
    · rw [Finset.erase_eq_of_notMem hP0T]; exact Nat.le_add_right _ _
  have hQ0pos : 0 < Q0 := hQ0def ▸ pow_pos hp.out.pos k
  have hS : ∑ P ∈ T'.erase P0, P.deg ≤ ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hQ0pos
    calc Q0 * ∑ P ∈ T'.erase P0, P.deg ≤ ℓ0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * (Q0 + 2 * gE)) := hmain
      _ = Q0 * (ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE))) := by ring
  have hX : ℓ0 * (Q0 ^ 2 + (2 * gE + 1) * Q0) = ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE)) + ℓ0 := by
    obtain ⟨Q1, rfl⟩ : ∃ Q1, Q0 = Q1 + 1 := ⟨Q0 - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [hX]
  calc s.card ≤ ∑ P ∈ T, Places.deg Fq P := hle
    _ ≤ _ := by rw [hsumT]; exact hsplit.trans (Nat.add_le_add_right hS _)

/-- If `ℓ0 ∣ m`, a twisted Frobenius point forces `g` to fix the constant field. -/
theorem fix_const_of_twist {m : ℕ} (hm : Module.finrank Fq (Places.constField Fq E) ∣ m)
    (g : E ≃ₐ[RatFunc Fq] E) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m))
    (y : Places.Rfin Fq E →ₐ[Fq] L) (hy : twist y g = φ.comp y) (c : Places.constField Fq E) :
    g (c : E) = c := by
  classical
  have hgc : IsIntegral Fq (g (c : E)) := by
    have hc := Places.isIntegral_of_mem_constField Fq E c
    exact hc.map ((g : E →ₐ[RatFunc Fq] E).restrictScalars Fq)
  let gc : Places.constField Fq E := ⟨g c, mem_algebraicClosure_iff.mpr hgc.isAlgebraic⟩
  let ψ : Places.constField Fq E →ₐ[Fq] L := y.comp (Places.constToRfin Fq E)
  have hconst : ∀ x : Places.constField Fq E, x ^ (Fintype.card Fq ^ m) = x := by
    intro x
    have : Finite (Places.constField Fq E) := Module.finite_of_finite Fq
    let _ : Fintype (Places.constField Fq E) := Fintype.ofFinite _
    obtain ⟨j, hj⟩ := hm
    have hcard : Fintype.card (Places.constField Fq E) =
        Fintype.card Fq ^ Module.finrank Fq (Places.constField Fq E) := Module.card_eq_pow_finrank
    rw [hj, pow_mul, ← hcard]
    exact Places.pow_card_pow_eq x j
  have hψ : ψ gc = ψ c := by
    have h1 : Places.constToRfin Fq E gc = g • Places.constToRfin Fq E c := Subtype.ext rfl
    change y (Places.constToRfin Fq E gc) = y (Places.constToRfin Fq E c)
    rw [h1, ← twist_apply, hy, AlgHom.comp_apply, hφ, ← map_pow, ← map_pow, hconst]
  have := ψ.toRingHom.injective hψ
  exact congrArg Subtype.val this

end FF

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_GalB =====
section

/-!
# S3-ZetaSB, E2b part B (generic half): Frobenius degree, lifting points, counting on `Fq[X]`

* `finrank_dvd_of_fixed` (B0): a finite field embedded in `L` with image fixed by `x ↦ x ^ (q ^ m)` has
  degree dividing `m`;
* `exists_algHom_comp_eq`, `exists_lift` (B2): `Fq`-points of `R` lift to `S` (integral, free of finite rank)
  when `m * (rank)! ∣ [L : Fq]`;
* `card_fixed_poly_ge` (B1): at least `q ^ m` points `Fq[X] → L` are fixed by `Frob^m`;
* group and constant-field facts used in the assembly.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.ZetaSB

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- (B0) A finite field embedded in `L` with image fixed by `x ↦ x ^ (q ^ m)` has degree dividing `m`. -/
theorem finrank_dvd_of_fixed {κ L : Type*} [Field κ] [Algebra Fq κ] [Finite κ] [Field L] [Algebra Fq L]
    (χ : κ →ₐ[Fq] L) (m : ℕ) (hχ : ∀ x, χ x ^ (Fintype.card Fq ^ m) = χ x) :
    finrank Fq κ ∣ m := by
  have h : ∀ x : κ, x ^ (Fintype.card Fq ^ m) = x := fun x => by
    have := hχ x
    rw [← map_pow] at this
    exact (χ : κ →+* L).injective this
  have h1 : FiniteField.frobeniusAlgHom Fq κ ^ m = 1 := by
    refine AlgHom.ext fun x => ?_
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply]
    exact h x
  rw [← FiniteField.orderOf_frobeniusAlgHom Fq κ]
  exact orderOf_dvd_of_pow_eq_one h1

/-- Abstract lifting: an embedding `κ → L` extends along `κ → κ'` when `[κ' : Fq] ∣ [L : Fq]`. -/
theorem exists_algHom_comp_eq {κ κ' L : Type*} [Field κ] [Field κ'] [Field L] [Algebra Fq κ] [Algebra Fq κ']
    [Algebra Fq L] [Finite L] [Module.Finite Fq κ'] (ι : κ →ₐ[Fq] κ') (z : κ →ₐ[Fq] L)
    (h : finrank Fq κ' ∣ finrank Fq L) : ∃ ψ : κ' →ₐ[Fq] L, ψ.comp ι = z := by
  letI : Algebra κ κ' := ι.toRingHom.toAlgebra
  letI : Algebra κ L := z.toRingHom.toAlgebra
  haveI : IsScalarTower Fq κ κ' := IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  haveI : IsScalarTower Fq κ L := IsScalarTower.of_algebraMap_eq fun c => (z.commutes c).symm
  haveI : Module.Finite Fq L := Module.Finite.of_finite
  haveI : Module.Finite Fq κ := Module.Finite.of_injective (ι.toLinearMap) (ι : κ →+* κ').injective
  have h1 := Module.finrank_mul_finrank Fq κ κ'
  have h2 := Module.finrank_mul_finrank Fq κ L
  have hpos : 0 < finrank Fq κ := Module.finrank_pos
  have hd : finrank κ κ' ∣ finrank κ L := by
    rw [← h1, ← h2] at h
    exact (Nat.mul_dvd_mul_iff_left hpos).mp h
  obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  exact ⟨ψ.restrictScalars Fq, AlgHom.ext fun x => ψ.commutes x⟩

/-- The images of an `R`-basis of `S` span a residue field of `S` over a residue field of `R`. -/
theorem span_basis_quot_eq_top {R S k k' : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
    [Module.Finite R S] [Field k] [CommRing k'] (π : R →+* k) (π' : S →+* k') (hπ' : Function.Surjective π')
    (ι : k →+* k') (hcomm : ∀ r, ι (π r) = π' (algebraMap R S r)) :
    letI := ι.toAlgebra
    Submodule.span k (Set.range fun i => π' (Module.Free.chooseBasis R S i)) = ⊤ := by
  letI := ι.toAlgebra
  classical
  set b := Module.Free.chooseBasis R S
  rw [eq_top_iff]
  rintro x -
  obtain ⟨s, rfl⟩ := hπ' x
  rw [← b.sum_repr s, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, ← hcomm]
  have := Submodule.smul_mem (Submodule.span k (Set.range fun i => π' (b i))) (π (b.repr s i))
    (Submodule.subset_span ⟨i, rfl⟩)
  rw [Algebra.smul_def] at this
  exact this

/-- (B2) Points of `R` fixed by `Frob^m` lift to `S` when `m * (rank_R S)! ∣ [L : Fq]`. -/
theorem exists_lift {R S L : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S] [Algebra Fq R] [Algebra Fq S]
    [IsScalarTower Fq R S] [Algebra.IsIntegral R S] [Module.Free R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [Field L] [Algebra Fq L] [Finite L] (m : ℕ)
    (z : R →ₐ[Fq] L) (hz : ∀ r, z r ^ (Fintype.card Fq ^ m) = z r)
    (hL : m * (finrank R S).factorial ∣ finrank Fq L) :
    ∃ y : S →ₐ[Fq] L, y.comp (IsScalarTower.toAlgHom Fq R S) = z := by
  classical
  set p := RingHom.ker z with hp
  haveI : p.IsPrime := RingHom.ker_isPrime z
  let zb : R ⧸ p →ₐ[Fq] L := Ideal.kerLiftAlg z
  have zb_inj : Function.Injective zb := Ideal.kerLiftAlg_injective z
  haveI : Finite (R ⧸ p) := Finite.of_injective zb zb_inj
  haveI hpmax : p.IsMaximal := Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain _)
  have hle : RingHom.ker (algebraMap R S) ≤ p := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le
  obtain ⟨P, hPmax, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p hle
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hle' : p ≤ P.comap (IsScalarTower.toAlgHom Fq R S) := hPp.ge
  let ι : R ⧸ p →ₐ[Fq] S ⧸ P := Ideal.quotientMapₐ P (IsScalarTower.toAlgHom Fq R S) hle'
  have hdeg1 : finrank Fq (R ⧸ p) ∣ m := by
    refine finrank_dvd_of_fixed zb m fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hz a
  letI : Algebra (R ⧸ p) (S ⧸ P) := ι.toRingHom.toAlgebra
  haveI : IsScalarTower Fq (R ⧸ p) (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  have hspan := span_basis_quot_eq_top (Ideal.Quotient.mk p) (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    ι.toRingHom (fun r => rfl)
  haveI : Module.Finite (R ⧸ p) (S ⧸ P) := by
    refine ⟨⟨Finset.univ.image fun i => Ideal.Quotient.mk P (Module.Free.chooseBasis R S i), ?_⟩⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan
  haveI : Module.Finite Fq (R ⧸ p) := Module.Finite.of_finite
  haveI : Module.Finite Fq (S ⧸ P) := Module.Finite.trans (R ⧸ p) (S ⧸ P)
  have hrel : finrank (R ⧸ p) (S ⧸ P) ≤ finrank R S := by
    rw [Module.finrank_eq_card_chooseBasisIndex R S]
    exact finrank_le_of_span_eq_top hspan
  have hdvd2 : finrank (R ⧸ p) (S ⧸ P) ∣ (finrank R S).factorial :=
    Nat.dvd_factorial Module.finrank_pos hrel
  have htow : finrank Fq (S ⧸ P) = finrank Fq (R ⧸ p) * finrank (R ⧸ p) (S ⧸ P) :=
    (Module.finrank_mul_finrank Fq (R ⧸ p) (S ⧸ P)).symm
  have hdvd : finrank Fq (S ⧸ P) ∣ finrank Fq L := by
    rw [htow]; exact (Nat.mul_dvd_mul hdeg1 hdvd2).trans hL
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_eq ι zb hdvd
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ Fq P), AlgHom.ext fun r => ?_⟩
  have := congrArg (fun f : R ⧸ p →ₐ[Fq] L => f (Ideal.Quotient.mk p r)) hψ
  exact this

/-- (B1) At least `q ^ m` points `Fq[X] → L` are fixed by `φ = Frob^m` when `m ∣ [L : Fq]`. -/
theorem card_fixed_poly_ge (p : ℕ) [Fact p.Prime] [CharP Fq p] {L : Type*} [Field L] [Algebra Fq L] [Finite L]
    [Fintype (Fq[X] →ₐ[Fq] L)] [DecidableEq (Fq[X] →ₐ[Fq] L)] (m : ℕ) (hm : m ≠ 0)
    (hL : m ∣ finrank Fq L) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m)) :
    Fintype.card Fq ^ m ≤ (Finset.univ.filter fun z : Fq[X] →ₐ[Fq] L => φ.comp z = z).card := by
  classical
  haveI : NeZero m := ⟨hm⟩
  let Lm := FiniteField.Extension Fq p m
  letI : Fintype Lm := Fintype.ofFinite Lm
  obtain ⟨χ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := Fq) (K := Lm) (L := L)
    (by rw [FiniteField.finrank_extension]; exact hL)
  have hcard : Fintype.card Lm = Fintype.card Fq ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  let f : Lm → (Fq[X] →ₐ[Fq] L) := fun c => Polynomial.aeval (χ c)
  calc Fintype.card Fq ^ m = (Finset.univ : Finset Lm).card := by rw [Finset.card_univ, hcard]
    _ ≤ _ := by
      refine Finset.card_le_card_of_injOn f (fun c _ => ?_) (fun c _ c' _ h => ?_)
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Polynomial.algHom_ext ?_⟩
        rw [AlgHom.comp_apply, Polynomial.aeval_X, hφ, ← map_pow, ← hcard, FiniteField.pow_card]
      · have := congrArg (fun z : Fq[X] →ₐ[Fq] L => z X) h
        simp only [f, Polynomial.aeval_X] at this
        exact (χ : Lm →+* L).injective this

/-- In a finite group, `|H| ≤ |A| · |H ∩ ker ρ|`. -/
theorem card_le_mul_card_inf_ker {G A : Type*} [Group G] [Group A] [Finite G] [Finite A] (ρ : G →* A)
    (H : Subgroup G) : Nat.card H ≤ Nat.card A * Nat.card (H ⊓ ρ.ker : Subgroup G) := by
  let ρ' := ρ.comp H.subtype
  have h1 : Nat.card ρ'.ker * Nat.card ρ'.range = Nat.card H := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ρ'.range ≤ Nat.card A := Subgroup.card_le_card_group _
  have h3 : Nat.card ρ'.ker = Nat.card (H ⊓ ρ.ker : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩,
          MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [← h1, h3, mul_comm]
  exact Nat.mul_le_mul_right _ h2

/-- Polynomials integral over the constants are constant. -/
theorem eq_C_of_isIntegral {p : Fq[X]} (h : IsIntegral Fq p) : p = C (p.coeff 0) := by
  obtain ⟨f, hf, hfp⟩ := h
  have hcomp : f.comp p = 0 := by rw [Polynomial.comp, ← Polynomial.algebraMap_eq]; exact hfp
  have hdeg : f.natDegree * p.natDegree = 0 := by rw [← Polynomial.natDegree_comp, hcomp, natDegree_zero]
  have hf0 : f.natDegree ≠ 0 := by
    intro h0
    have h1 : f = 1 := (Polynomial.Monic.natDegree_eq_zero hf).mp h0
    rw [h1, Polynomial.one_comp] at hcomp
    exact one_ne_zero hcomp
  have h2 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.mp hdeg with h | h
    · exact absurd h hf0
    · exact h
  exact Polynomial.eq_C_of_natDegree_eq_zero h2

/-- Rational functions integral over the constants are constants. -/
theorem ratFunc_eq_of_isIntegral {r : RatFunc Fq} (h : IsIntegral Fq r) :
    ∃ a : Fq, algebraMap Fq (RatFunc Fq) a = r := by
  have h2 : IsIntegral Fq[X] r := h.tower_top
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : IsIntegral Fq p := by
    rw [← hp] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom Fq Fq[X] (RatFunc Fq))
      (IsFractionRing.injective Fq[X] (RatFunc Fq))).mp h
  refine ⟨p.coeff 0, ?_⟩
  rw [← hp, IsScalarTower.algebraMap_apply Fq Fq[X] (RatFunc Fq), Polynomial.algebraMap_eq,
    ← eq_C_of_isIntegral h3]

/-- `Hom_Fq(S, L)` is finite for a Dedekind `S` with finite residue fields and an element of infinite order. -/
theorem finite_algHom_of_pow {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S]
    [Places.FiniteQuot S] [Infinite S] {t : S} (ht : ∀ N : ℕ, 2 ≤ N → t ^ N ≠ t)
    (L : Type*) [Field L] [Algebra Fq L] [Finite L] : Finite (S →ₐ[Fq] L) := by
  classical
  have : Module.Finite Fq L := Module.Finite.of_finite
  set T := (Places.finite_deg_dvd_of Fq ht (Module.finrank_pos (R := Fq) (M := L)).ne').toFinset
  have hmem : ∀ φ : S →ₐ[Fq] L, Places.kerPlace Fq L φ ∈ T := fun φ => by
    rw [Set.Finite.mem_toFinset]
    have := (Places.kerPlace Fq L φ).isMaximal
    letI : Field (S ⧸ (Places.kerPlace Fq L φ).asIdeal) := Ideal.Quotient.field _
    exact Places.finrank_dvd_of_algHom_field Fq (Places.fiberEquiv Fq L _ ⟨φ, rfl⟩)
  have hfib : ∀ P, {φ : S →ₐ[Fq] L | Places.kerPlace Fq L φ = P}.Finite := fun P => by
    have : Finite (S ⧸ P.asIdeal →ₐ[Fq] L) := Places.finite_algHom Fq
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (Places.fiberEquiv Fq L P).symm)
  exact Set.finite_univ_iff.mp ((T.finite_toSet.biUnion fun P _ => hfib P).subset fun φ _ =>
    Set.mem_biUnion (hmem φ) rfl)

/-- The kernel of a `Frob^m`-fixed point has degree dividing `m`. -/
theorem deg_kerPlace_dvd {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S]
    [Places.FiniteQuot S] [Infinite S] (L : Type*) [Field L] [Algebra Fq L] [Finite L] (m : ℕ)
    (w : S →ₐ[Fq] L) (hw : ∀ a, w a ^ (Fintype.card Fq ^ m) = w a) :
    Places.deg Fq (Places.kerPlace Fq L w) ∣ m := by
  have := (Places.kerPlace Fq L w).isMaximal
  letI : Field (S ⧸ (Places.kerPlace Fq L w).asIdeal) := Ideal.Quotient.field _
  refine finrank_dvd_of_fixed (Places.fiberEquiv Fq L _ ⟨w, rfl⟩) m fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hw a

end Generic

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_GalC =====
section

/-!
# S3-ZetaSB, E2b part C: the Galois-twist lower bound for a Galois function field

For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`, group `G`, `Hs = Gal(E/F)` as the fixing subgroup of `ι F`):
* `constRes : G →* Aut(k'/Fq)` (restriction to the constant field `k'` of `E`) has range of size `ℓ0 = [k' : Fq]`
  (`card_gal_eq : |G| = ℓ0 |ker|`), and `|Hs| ≤ ℓ0 |Hs ⊓ ker|`;
* the `F`-side count `Σ_{h ∈ Hs} N(h) ≤ |Hs| · N_m(F)` and the `K`-side count `|G| q ^ m ≤ Σ_{g ∈ G} N(g)`;
* `lower_bound_core`: `q ^ m ≤ N_m(F) + |G| (2 g_E + 1) q ^ (m/2)` when `q ^ m = Q0 ^ 2` is large and `E` has a
  place of degree `ℓ0`.
-/

set_option autoImplicit false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

instance finite_constField : Finite (Places.constField Fq E) := Module.finite_of_finite Fq

variable (Fq E) in
/-- Restriction of `Gal(E/K)` to the constant field `k'` of `E`. -/
noncomputable def constRes :
    (E ≃ₐ[RatFunc Fq] E) →* (Places.constField Fq E ≃ₐ[Fq] Places.constField Fq E) :=
  (AlgEquiv.restrictNormalHom (Places.constField Fq E)).comp (AlgEquiv.restrictScalarsHom Fq)

theorem constRes_apply (g : E ≃ₐ[RatFunc Fq] E) (c : Places.constField Fq E) :
    ((constRes Fq E g c : Places.constField Fq E) : E) = g c := by
  change ((AlgEquiv.restrictNormalHom (Places.constField Fq E) (AlgEquiv.restrictScalarsHom Fq g) c :
    Places.constField Fq E) : E) = g c
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

theorem mem_ker_constRes (g : E ≃ₐ[RatFunc Fq] E) :
    g ∈ (constRes Fq E).ker ↔ ∀ c : Places.constField Fq E, g (c : E) = c := by
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  refine forall_congr' fun c => ?_
  rw [AlgEquiv.one_apply, ← constRes_apply, Subtype.ext_iff]

variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq) in
/-- `ι : F → E` on the rings of finite integers. -/
noncomputable def finMap (ι : F →ₐ[RatFunc Fq] E) : Places.Rfin Fq F →ₐ[Fq[X]] Places.Rfin Fq E :=
  (ι.restrictScalars Fq[X]).mapIntegralClosure

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

theorem frob_pow_apply (m : ℕ) (x : L) :
    (FiniteField.frobeniusAlgHom Fq L ^ m) x = x ^ (Fintype.card Fq ^ m) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

end FF

end RamanujanPetersson.ZetaSB


end

-- ===== S3.SB_Upper =====
section

/-!
# S3-ZetaSB, D1: the Galois-twist upper bound

For `F ⊆ E` with `E / K` Galois (`K = RatFunc Fq`) and `F` with full constant field `Fq`:
* `exists_lift_tower` (U1): Frobenius-fixed points of `R` lift to `S` for a tower `R0 → R → S` with `S` free of
  finite rank over `R0`;
* `piInfR_mem`, `Cinf` (U2): every place over `x = ∞` contains `1/x`, so these places are finite in number;
  `Cinf` is the sum of their degrees;
* `numPoints_le_fixed_add` (U3): `N_m(F) ≤ #{w : Rfin F → L, Frob^m-fixed} + Cinf`;
* `card_Hs_eq` (U4): `|Gal(E/F)| = ℓ0 · |Gal(E/F) ⊓ ker constRes|`;
* `sum_twisted_H_eq` (U5): `Σ_{h ∈ Gal(E/F)} N(h) = |Gal(E/F)| · #{w fixed}`;
* `upper_bound_core` (U6): `N_m(F) ≤ q ^ m + (2 g_E + 1) q ^ (m/2) + Cinf`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section Generic

variable {Fq : Type*} [Field Fq] [Fintype Fq]

end Generic

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (Fq F) in
/-- The image of `1/x` in `Rinf F`. -/
noncomputable abbrev piInfR : Places.Rinf Fq F :=
  algebraMap (Places.Oinf Fq) (Places.Rinf Fq F) (Places.piInf Fq)

theorem piInfR_ne_zero : piInfR Fq F ≠ 0 := by
  rw [Ne, ← map_zero (algebraMap (Places.Oinf Fq) (Places.Rinf Fq F)),
    (Places.algebraMap_Oinf_Rinf_injective Fq F).eq_iff]
  exact Places.piInf_ne_zero Fq

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

end FF

end RamanujanPetersson.ZetaSB


end

-- ===== S3.Zeta_A =====
section

/-!
# S3-ZetaSB, O5 part A: effective divisors and the Newton identity

`A_n` = number of effective divisors of degree `n` (finite: they are supported on the places of degree `≤ n`).
Newton identity (the coefficientwise form of `t Z'(t) = Z(t) · Σ_m N_m t^m`):
`n A_n = Σ_{m=1}^n N_m A_{n-m}`, proved by the bijection `D ↦ D - k P` (no infinite products).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.ZetaSB

open Places

section Eff

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem finite_place_deg_le (n : ℕ) : {P : Place Fq F | P.deg ≤ n}.Finite :=
  ((Finset.range (n + 1)).finite_toSet.biUnion fun d _ => finite_place_deg_eq Fq F d).subset fun _ hP =>
    Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hP))) rfl

variable {Fq F}

end Eff

end RamanujanPetersson.ZetaSB


end

-- ===== S4.Def_RP_PicDescent_D2 =====
section

/-!
# S4-PicDescent, part D2: unramified Dedekind extensions, generic

* `A → B` Dedekind, finite, torsion free, formally unramified (`B ≅ A ⊗ L` for a separable `L`):
  every place `w` of `B` has ramification index `1` over `w.under A`, so
  `valuation_under : (w.under A).valuation K x = w.valuation L x'` (orders agree);
  the fibre over `v` is finite and nonempty, `Σ_{w | v} f(w|v) = [B : A]`, `#(A/v)^f = #(B/w)`.
* `pullH σ w = σ⁻¹(w)` for a ring automorphism `σ` of `B`: `valuation_pullH`
  (`(σ⁻¹ w).valuation x = w.valuation (σ x)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Unram

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

instance liesOver_under' (w : HeightOneSpectrum B) : w.asIdeal.LiesOver (w.under A).asIdeal := ⟨rfl⟩

end Unram

section Equiv

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

end Equiv

end RamanujanPetersson.PicDescent


end


