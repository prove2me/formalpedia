-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ1
-- name    : RPLib_S3_DWSTateQ1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:53.995227+00:00
-- url     : https://prove2.me/theorems/994f20ee-9b94-4300-a040-16507ce56ed6
-- title:
--   Weight-two Ramanujan-Petersson library: imaginary quadratic orders `ℤ[ω]`, `ω² = a + b ω`, as Mathlib `QuadraticAlgebra`s
-- statement:
--   Imaginary quadratic orders `ℤ[ω]`, `ω² = a + b ω`, as Mathlib `QuadraticAlgebra`s.
--
--   Pure algebra (no elliptic curves). Throughout `b² + 4a < 0` (negative discriminant `D = b² + 4a`).
--   * `four_norm`, `norm_nonneg`, `norm_eq_zero_iff`, `norm_pos`: the norm is positive definite.
--   * `noZeroDivisors`, `isDomain`.
--   * `lat A k hk` (`hk : A ∣ a + k b - k²`): the ideal `ℤA + ℤ(ω - k)` = `{z | A ∣ re z + k im z}` of the binary
--     quadratic form `(A, 2k - b, C)`, `A C = k² - k b - a`; `mem_lat`, `star_mem_lat` (conjugate ideal = `lat A (b - k)`),
--     `lat_eq_span`, and `lat_mul_lat_star` : `I · Ī = (A)` for a primitive form.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib

/-!
# S3-DWS-Tate, part Q1: imaginary quadratic orders `ℤ[ω]`, `ω² = a + b ω`, as Mathlib `QuadraticAlgebra`s

Pure algebra (no elliptic curves). Throughout `b² + 4a < 0` (negative discriminant `D = b² + 4a`).
* `four_norm`, `norm_nonneg`, `norm_eq_zero_iff`, `norm_pos`: the norm is positive definite.
* `noZeroDivisors`, `isDomain`.
* `lat A k hk` (`hk : A ∣ a + k b - k²`): the ideal `ℤA + ℤ(ω - k)` = `{z | A ∣ re z + k im z}` of the binary
  quadratic form `(A, 2k - b, C)`, `A C = k² - k b - a`; `mem_lat`, `star_mem_lat` (conjugate ideal = `lat A (b - k)`),
  `lat_eq_span`, and `lat_mul_lat_star` : `I · Ī = (A)` for a primitive form.
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra Pointwise

variable {a b : ℤ}

theorem four_norm (z : QuadraticAlgebra ℤ a b) :
    4 * z.norm = (2 * z.re + b * z.im) ^ 2 - (b ^ 2 + 4 * a) * z.im ^ 2 := by
  rw [norm_def]; ring

theorem norm_nonneg (h : b ^ 2 + 4 * a < 0) (z : QuadraticAlgebra ℤ a b) : 0 ≤ z.norm := by
  have h4 := four_norm z
  nlinarith [sq_nonneg (2 * z.re + b * z.im), sq_nonneg z.im]

theorem norm_eq_zero_iff (h : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b} : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h4 := four_norm z
    rw [hz, mul_zero] at h4
    have him : z.im = 0 := by
      by_contra hne
      have hpos : 0 < z.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      nlinarith [sq_nonneg (2 * z.re + b * z.im)]
    have hre : z.re ^ 2 = 0 := by
      rw [him] at h4
      nlinarith
    ext
    · simpa using hre
    · simpa using him
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

theorem norm_pos (h : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b} (hz : z ≠ 0) : 0 < z.norm :=
  lt_of_le_of_ne (norm_nonneg h z) (fun h0 => hz ((norm_eq_zero_iff h).mp h0.symm))

theorem noZeroDivisors (h : b ^ 2 + 4 * a < 0) : NoZeroDivisors (QuadraticAlgebra ℤ a b) where
  eq_zero_or_eq_zero_of_mul_eq_zero {z w} hzw := by
    have h1 := congrArg QuadraticAlgebra.norm hzw
    rw [map_mul, QuadraticAlgebra.norm_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl ((norm_eq_zero_iff h).mp h2)
    · exact Or.inr ((norm_eq_zero_iff h).mp h2)

theorem isDomain (h : b ^ 2 + 4 * a < 0) : IsDomain (QuadraticAlgebra ℤ a b) := by
  have := noZeroDivisors h
  exact NoZeroDivisors.to_isDomain _

/-! ### The ideal `ℤA + ℤ(ω - k)` of a form -/

/-- The ideal `ℤA + ℤ(ω - k)`, as `{z | A ∣ re z + k im z}`; it is an ideal when `A ∣ a + k b - k²`. -/
def lat (A k : ℤ) (hk : A ∣ a + k * b - k ^ 2) : Ideal (QuadraticAlgebra ℤ a b) where
  carrier := {z | A ∣ z.re + k * z.im}
  add_mem' := by
    intro z w hz hw
    have : (z + w).re + k * (z + w).im = (z.re + k * z.im) + (w.re + k * w.im) := by
      simp only [re_add, im_add]; ring
    show A ∣ (z + w).re + k * (z + w).im
    rw [this]; exact dvd_add hz hw
  zero_mem' := by
    show A ∣ (0 : QuadraticAlgebra ℤ a b).re + k * (0 : QuadraticAlgebra ℤ a b).im
    simp
  smul_mem' := by
    intro c z hz
    have : (c * z).re + k * (c * z).im =
        (c.re + k * c.im) * (z.re + k * z.im) + c.im * z.im * (a + k * b - k ^ 2) := by
      simp only [re_mul, im_mul]; ring
    show A ∣ (c * z).re + k * (c * z).im
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hz _) (dvd_mul_of_dvd_right hk _)

variable {A k : ℤ} {hk : A ∣ a + k * b - k ^ 2}

theorem mem_lat {z : QuadraticAlgebra ℤ a b} : z ∈ lat A k hk ↔ A ∣ z.re + k * z.im := Iff.rfl

theorem conj_dvd (hk : A ∣ a + k * b - k ^ 2) : A ∣ a + (b - k) * b - (b - k) ^ 2 := by
  have : a + (b - k) * b - (b - k) ^ 2 = a + k * b - k ^ 2 := by ring
  rw [this]; exact hk

/-- The conjugate of `lat A k` is `lat A (b - k)`. -/
theorem star_mem_lat {z : QuadraticAlgebra ℤ a b} :
    star z ∈ lat A k hk ↔ z ∈ lat A (b - k) (conj_dvd hk) := by
  rw [mem_lat, mem_lat, re_star, im_star]
  have : z.re + b * z.im + k * -z.im = z.re + (b - k) * z.im := by ring
  rw [this]

theorem A_mem_lat : (A : QuadraticAlgebra ℤ a b) ∈ lat A k hk := by
  rw [mem_lat]; simp

theorem gen_mem_lat : (⟨-k, 1⟩ : QuadraticAlgebra ℤ a b) ∈ lat A k hk := by
  rw [mem_lat]; simp

theorem mem_lat_iff_exists {z : QuadraticAlgebra ℤ a b} :
    z ∈ lat A k hk ↔ ∃ m n : ℤ, z = m * (A : QuadraticAlgebra ℤ a b) + n * ⟨-k, 1⟩ := by
  rw [mem_lat]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, z.im, ?_⟩
    ext
    · simp only [re_add, re_mul, re_intCast, im_intCast, mul_zero, add_zero, Int.cast_id]
      linarith
    · simp
  · rintro ⟨m, n, rfl⟩
    refine ⟨m, ?_⟩
    simp only [re_add, re_mul, re_intCast, im_intCast, mul_zero, add_zero, im_add, im_mul, zero_mul,
      mul_one, zero_add, Int.cast_id]
    ring

theorem lat_eq_span :
    lat A k hk = Ideal.span {(A : QuadraticAlgebra ℤ a b), ⟨-k, 1⟩} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨m, n, rfl⟩ := mem_lat_iff_exists.mp hz
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact A_mem_lat
    · exact gen_mem_lat

/-- **`I Ī = (A)`** for the ideal of a primitive form `(A, 2k - b, C)` (`a + k b - k² = -A C`). -/
theorem lat_mul_lat_star {C : ℤ} (hC : a + k * b - k ^ 2 = -(A * C))
    (hprim : ∃ u v w : ℤ, u * A + v * (2 * k - b) + w * C = 1) :
    lat A k hk * lat A (b - k) (conj_dvd hk) = Ideal.span {(A : QuadraticAlgebra ℤ a b)} := by
  rw [lat_eq_span, lat_eq_span, Ideal.span_mul_span']
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨A, rfl⟩
    · exact ⟨⟨-(b - k), 1⟩, rfl⟩
    · exact ⟨⟨-k, 1⟩, mul_comm _ _⟩
    · refine ⟨((-C : ℤ) : QuadraticAlgebra ℤ a b), ?_⟩
      ext
      · simp only [re_mul, re_intCast, im_intCast, Int.cast_id]
        linear_combination hC
      · simp only [im_mul, re_intCast, im_intCast, Int.cast_id]
        ring
  · obtain ⟨u, v, w, huvw⟩ := hprim
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set J := Ideal.span ((({(A : QuadraticAlgebra ℤ a b), ⟨-k, 1⟩} : Set _)) *
      ({(A : QuadraticAlgebra ℤ a b), ⟨-(b - k), 1⟩} : Set _))
    have m1 : (A : QuadraticAlgebra ℤ a b) * A ∈ J :=
      Ideal.subset_span (Set.mul_mem_mul (Set.mem_insert _ _) (Set.mem_insert _ _))
    have m2 : (A : QuadraticAlgebra ℤ a b) * ⟨-(b - k), 1⟩ ∈ J :=
      Ideal.subset_span (Set.mul_mem_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    have m3 : (⟨-k, 1⟩ : QuadraticAlgebra ℤ a b) * A ∈ J :=
      Ideal.subset_span (Set.mul_mem_mul (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _))
    have m4 : (⟨-k, 1⟩ : QuadraticAlgebra ℤ a b) * ⟨-(b - k), 1⟩ ∈ J :=
      Ideal.subset_span (Set.mul_mem_mul (Set.mem_insert_of_mem _ rfl) (Set.mem_insert_of_mem _ rfl))
    have key : (A : QuadraticAlgebra ℤ a b) =
        (u : QuadraticAlgebra ℤ a b) * ((A : QuadraticAlgebra ℤ a b) * A) +
        (v : QuadraticAlgebra ℤ a b) * ((A : QuadraticAlgebra ℤ a b) * ⟨-(b - k), 1⟩ - ⟨-k, 1⟩ * A) +
        (-w : QuadraticAlgebra ℤ a b) * ((⟨-k, 1⟩ : QuadraticAlgebra ℤ a b) * ⟨-(b - k), 1⟩) := by
      ext
      · simp only [re_add, re_mul, im_mul, re_sub, im_sub, re_intCast, im_intCast, re_neg, im_neg,
          im_add, Int.cast_id]
        linear_combination (-A) * huvw + w * hC
      · simp only [re_add, re_mul, im_mul, re_sub, im_sub, re_intCast, im_intCast, re_neg, im_neg,
          im_add, Int.cast_id]
        ring
    rw [key]
    exact J.add_mem (J.add_mem (J.mul_mem_left _ m1) (J.mul_mem_left _ (J.sub_mem m2 m3)))
      (J.mul_mem_left _ m4)

end RPLib.DWS.QA


