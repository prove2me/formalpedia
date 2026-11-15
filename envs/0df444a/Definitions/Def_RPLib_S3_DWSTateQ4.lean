-- Prove2me | Definitions.Def_RPLib_S3_DWSTateQ4
-- name    : RPLib_S3_DWSTateQ4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:24:49.446376+00:00
-- url     : https://prove2.me/theorems/9b2b99bf-01f8-4ad3-8f42-00a9e45f1bb4
-- title:
--   Weight-two Ramanujan-Petersson library: invertible ideals are form ideals (d2, d4)
-- statement:
--   Invertible ideals are form ideals (d2, d4).
--
--   Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
--   * `exists_hermite`: every nonzero ideal is `(g) · (ℤA + ℤ(ω - k))` with `g, A > 0`, `A ∣ a + k b - k²`.
--   * `isPrimitive_of_inv`: if moreover `I J = (ν)`, `ν ≠ 0`, the form `(A, 2k - b, -c)` is primitive.
--   * **(d4)** `exists_formIdeal_rel`: every invertible ideal is in the class of some `I_f`, `f` primitive of
--     discriminant `D`.
--   * **(d2)** `formIdeal_mul_conj`: `I_f · I_{f̄} = (f.a)` for `f` primitive (`f̄ = (a, -b, c)`).
--   * `exists_act_not_dvd`, `exists_rep_not_dvd`: every class has a representative `f` with `p ∤ f.a`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. A. Cox, Primes of the Form x^2 + ny^2, 2nd ed., Wiley 2013, Sections 2, 7 and 11; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ3

/-!
# S3-DWS-Tate, part Q4: invertible ideals are form ideals (d2, d4)

Pure algebra. `R = QuadraticAlgebra ℤ a b`, `D = b² + 4a < 0`.
* `exists_hermite`: every nonzero ideal is `(g) · (ℤA + ℤ(ω - k))` with `g, A > 0`, `A ∣ a + k b - k²`.
* `isPrimitive_of_inv`: if moreover `I J = (ν)`, `ν ≠ 0`, the form `(A, 2k - b, -c)` is primitive.
* **(d4)** `exists_formIdeal_rel`: every invertible ideal is in the class of some `I_f`, `f` primitive of
  discriminant `D`.
* **(d2)** `formIdeal_mul_conj`: `I_f · I_{f̄} = (f.a)` for `f` primitive (`f̄ = (a, -b, c)`).
* `exists_act_not_dvd`, `exists_rep_not_dvd`: every class has a representative `f` with `p ∤ f.a`.
-/

set_option autoImplicit false

namespace RPLib.DWS.QA

open QuadraticAlgebra RamanujanPetersson.Hurwitz MatrixGroups

variable {a b : ℤ}

theorem lat_congr {A k k' : ℤ} (h : k = k') (hk : A ∣ a + k * b - k ^ 2)
    (hk' : A ∣ a + k' * b - k' ^ 2) :
    (lat A k hk : Ideal (QuadraticAlgebra ℤ a b)) = lat A k' hk' := by
  subst h; rfl

/-- Every ideal of `ℤ` is `(g)` with `g ≥ 0`. -/
theorem exists_gen (H : Ideal ℤ) : ∃ g : ℤ, 0 ≤ g ∧ ∀ n, n ∈ H ↔ g ∣ n := by
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal H
  refine ⟨|g|, abs_nonneg g, fun n => ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton, abs_dvd]

/-- The ideal of `ℤ` of imaginary parts of elements of `I`. -/
def imIdeal (I : Ideal (QuadraticAlgebra ℤ a b)) : Ideal ℤ where
  carrier := {n | ∃ z ∈ I, z.im = n}
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, I.add_mem hz hw, im_add z w⟩
  zero_mem' := ⟨0, I.zero_mem, im_zero⟩
  smul_mem' := by
    rintro c _ ⟨z, hz, rfl⟩
    exact ⟨(c : QuadraticAlgebra ℤ a b) * z, I.mul_mem_left _ hz, by rw [im_intCast_mul, smul_eq_mul]⟩

theorem mem_imIdeal {I : Ideal (QuadraticAlgebra ℤ a b)} {n : ℤ} :
    n ∈ imIdeal I ↔ ∃ z ∈ I, z.im = n := Iff.rfl

/-- **Hermite form**: a nonzero ideal is `(g) · lat A k` with `g, A > 0`. -/
theorem exists_hermite (hD : b ^ 2 + 4 * a < 0) {I : Ideal (QuadraticAlgebra ℤ a b)} (hI : I ≠ ⊥) :
    ∃ g A k : ℤ, ∃ hk : A ∣ a + k * b - k ^ 2, 0 < g ∧ 0 < A ∧
      I = Ideal.span {(g : QuadraticAlgebra ℤ a b)} * lat A k hk := by
  obtain ⟨G, hG0, hG⟩ := exists_gen (I.comap (Int.castRingHom (QuadraticAlgebra ℤ a b)))
  obtain ⟨g, hg0, hg⟩ := exists_gen (imIdeal I)
  have mG : ∀ n : ℤ, (n : QuadraticAlgebra ℤ a b) ∈ I ↔ G ∣ n := fun n => by
    rw [← hG n, Ideal.mem_comap, eq_intCast]
  have mg : ∀ z ∈ I, g ∣ z.im := fun z hz => (hg _).mp (mem_imIdeal.mpr ⟨z, hz, rfl⟩)
  obtain ⟨z0, hz0, hz0im⟩ := mem_imIdeal.mp ((hg g).mpr dvd_rfl)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hN : ((w.norm : ℤ) : QuadraticAlgebra ℤ a b) ∈ I := by
    rw [← mul_star_eq_norm]; exact I.mul_mem_right _ hw
  have hGdvd : G ∣ w.norm := (mG _).mp hN
  have hwpos : 0 < w.norm := norm_pos hD hw0
  have hGpos : 0 < G := by
    rcases hG0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hGdvd; exact absurd (zero_dvd_iff.mp hGdvd) hwpos.ne'
  have hGω : (G : QuadraticAlgebra ℤ a b) * ⟨0, 1⟩ ∈ I := I.mul_mem_right _ ((mG G).mpr dvd_rfl)
  have hgG : g ∣ G := by
    have h := mg _ hGω
    rw [im_intCast_mul] at h
    simpa using h
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hgG; exact absurd (zero_dvd_iff.mp hgG) hGpos.ne'
  obtain ⟨A, hA⟩ := hgG
  have hApos : 0 < A := by nlinarith
  have hre : g ∣ z0.re := by
    have h1 := mg _ (I.mul_mem_right (⟨0, 1⟩ : QuadraticAlgebra ℤ a b) hz0)
    have e : (z0 * ⟨0, 1⟩ : QuadraticAlgebra ℤ a b).im = z0.re + b * g := by
      simp only [im_mul, hz0im]; ring
    rw [e] at h1
    exact (dvd_add_left (dvd_mul_left g b)).mp h1
  obtain ⟨m0, hm0⟩ := hre
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, m0 = -k := ⟨-m0, by ring⟩
  have hz0eq : z0 = (g : QuadraticAlgebra ℤ a b) * ⟨-k, 1⟩ := by
    ext
    · simp only [re_mul, re_intCast, im_intCast, Int.cast_id, hm0]; ring
    · simp only [im_mul, re_intCast, im_intCast, Int.cast_id, hz0im]; ring
  have hint : ((g * (a + k * b - k ^ 2) : ℤ) : QuadraticAlgebra ℤ a b) ∈ I := by
    have e : ((g * (a + k * b - k ^ 2) : ℤ) : QuadraticAlgebra ℤ a b) =
        z0 * ⟨0, 1⟩ - ((b - k : ℤ) : QuadraticAlgebra ℤ a b) * z0 := by
      rw [hz0eq]
      ext
      · simp only [re_sub, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]; ring
      · simp only [im_sub, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]; ring
    rw [e]; exact I.sub_mem (I.mul_mem_right _ hz0) (I.mul_mem_left _ hz0)
  have hk : A ∣ a + k * b - k ^ 2 := by
    have h1 := (mG _).mp hint
    rw [hA] at h1
    exact (mul_dvd_mul_iff_left hgpos.ne').mp h1
  refine ⟨g, A, k, hk, hgpos, hApos, le_antisymm ?_ ?_⟩
  · intro z hz
    rw [Ideal.mem_span_singleton_mul]
    obtain ⟨m, hm⟩ := mg z hz
    have hn : ((z.re - m * z0.re : ℤ) : QuadraticAlgebra ℤ a b) ∈ I := by
      have e : ((z.re - m * z0.re : ℤ) : QuadraticAlgebra ℤ a b) =
          z - (m : QuadraticAlgebra ℤ a b) * z0 := by
        ext
        · simp only [re_sub, re_intCast_mul, re_intCast, Int.cast_id]
        · simp only [im_sub, im_intCast_mul, im_intCast, Int.cast_id, hm, hz0im]; ring
      rw [e]; exact I.sub_mem hz (I.mul_mem_left _ hz0)
    obtain ⟨l, hl⟩ := (mG _).mp hn
    refine ⟨⟨A * l - m * k, m⟩, ?_, ?_⟩
    · rw [mem_lat]
      show A ∣ (A * l - m * k) + k * m
      exact ⟨l, by ring⟩
    · ext
      · simp only [re_intCast_mul]
        show g * (A * l - m * k) = z.re
        linear_combination -hl - m * hm0 - l * hA
      · simp only [im_intCast_mul]
        show g * m = z.im
        linear_combination -hm
  · rw [lat_eq_span, span_pair_mul, Ideal.span_le]
    rintro z (rfl | rfl)
    · have h : ((g * A : ℤ) : QuadraticAlgebra ℤ a b) ∈ I := by
        rw [← hA]; exact (mG G).mpr dvd_rfl
      rw [Int.cast_mul] at h
      exact h
    · rw [← hz0eq]; exact hz0

/-- **Invertible ideals give primitive forms.** -/
theorem isPrimitive_of_inv (hD : b ^ 2 + 4 * a < 0) {g A k c : ℤ} {hk : A ∣ a + k * b - k ^ 2}
    (hc : a + k * b - k ^ 2 = A * c) {I J : Ideal (QuadraticAlgebra ℤ a b)}
    {ν : QuadraticAlgebra ℤ a b} (hν : ν ≠ 0)
    (hI : I = Ideal.span {(g : QuadraticAlgebra ℤ a b)} * lat A k hk)
    (hIJ : I * J = Ideal.span {ν}) : (⟨A, 2 * k - b, -c⟩ : BQF).IsPrimitive := by
  haveI := isDomain hD
  set f : BQF := ⟨A, 2 * k - b, -c⟩ with hf
  obtain ⟨A1, hA1⟩ := f.content_dvd_a
  obtain ⟨B1, hB1⟩ := f.content_dvd_b
  obtain ⟨C1, hC1⟩ := f.content_dvd_c
  set c0 : ℤ := (f.content : ℤ) with hc0
  have hA1' : A = c0 * A1 := hA1
  have hB1' : 2 * k - b = c0 * B1 := hB1
  have hC1' : -c = c0 * C1 := hC1
  set z : QuadraticAlgebra ℤ a b := ⟨-(b - k), 1⟩ with hz
  have hlat : Ideal.span {z} * lat A k hk ≤
      Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * lat A k hk := by
    rw [lat_eq_span, span_pair_mul, span_pair_mul, Ideal.span_le]
    rintro w (rfl | rfl)
    · have e : z * (A : QuadraticAlgebra ℤ a b) =
          (A1 : QuadraticAlgebra ℤ a b) * ((c0 : QuadraticAlgebra ℤ a b) * ⟨-k, 1⟩) +
          (B1 : QuadraticAlgebra ℤ a b) * ((c0 : QuadraticAlgebra ℤ a b) * (A : QuadraticAlgebra ℤ a b)) := by
        ext
        · simp only [hz, re_add, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]
          linear_combination (-k) * hA1' + A * hB1'
        · simp only [hz, im_add, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]
          linear_combination hA1'
      rw [e]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    · have e : z * (⟨-k, 1⟩ : QuadraticAlgebra ℤ a b) =
          ((-C1 : ℤ) : QuadraticAlgebra ℤ a b) *
            ((c0 : QuadraticAlgebra ℤ a b) * (A : QuadraticAlgebra ℤ a b)) := by
        ext
        · simp only [hz, re_mul, im_mul, re_intCast, im_intCast, Int.cast_id]
          linear_combination hc - A * hC1'
        · simp only [hz, im_mul, re_mul, re_intCast, im_intCast, Int.cast_id]
          ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
  have h2 : Ideal.span {z} * (I * J) ≤ Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * (I * J) := by
    rw [hI]
    calc Ideal.span {z} * (Ideal.span {(g : QuadraticAlgebra ℤ a b)} * lat A k hk * J)
        = Ideal.span {(g : QuadraticAlgebra ℤ a b)} * (Ideal.span {z} * lat A k hk) * J := by ring
      _ ≤ Ideal.span {(g : QuadraticAlgebra ℤ a b)} *
          (Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * lat A k hk) * J :=
          Ideal.mul_mono_left (Ideal.mul_mono_right hlat)
      _ = Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} *
          (Ideal.span {(g : QuadraticAlgebra ℤ a b)} * lat A k hk * J) := by ring
  rw [hIJ, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton] at h2
  have hmem : z * ν ∈ Ideal.span {(c0 : QuadraticAlgebra ℤ a b) * ν} :=
    h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  have hw' : w * (c0 : QuadraticAlgebra ℤ a b) = z := by
    apply mul_right_cancel₀ hν
    rw [mul_assoc]; exact hw
  have him : c0 * w.im = 1 := by
    have h := congrArg QuadraticAlgebra.im hw'
    rw [mul_comm, im_intCast_mul] at h
    exact h
  have hc0nn : 0 ≤ c0 := by rw [hc0]; positivity
  have h1 : c0 = 1 := Int.eq_one_of_dvd_one hc0nn ⟨w.im, him.symm⟩
  show f.content = 1
  have h1' : ((f.content : ℕ) : ℤ) = 1 := h1
  exact_mod_cast h1'

/-- **(d4)** Every invertible ideal is in the class of the ideal of a primitive positive definite form of
discriminant `D`. -/
theorem exists_formIdeal_rel (hD : b ^ 2 + 4 * a < 0) {I J : Ideal (QuadraticAlgebra ℤ a b)}
    {ν : QuadraticAlgebra ℤ a b} (hν : ν ≠ 0) (hIJ : I * J = Ideal.span {ν}) :
    ∃ f ∈ primForms (b ^ 2 + 4 * a), IdealRel I (formIdeal f) := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Submodule.bot_mul] at hIJ
    exact hν (Ideal.span_singleton_eq_bot.mp hIJ.symm)
  obtain ⟨g, A, k, hk, hg, hA, hIeq⟩ := exists_hermite hD hI
  have hk' := hk
  obtain ⟨c, hc⟩ := hk'
  have hprim := isPrimitive_of_inv hD hc hν hIeq hIJ
  have hdisc : (⟨A, 2 * k - b, -c⟩ : BQF).disc = b ^ 2 + 4 * a := by
    show (2 * k - b) ^ 2 - 4 * A * (-c) = b ^ 2 + 4 * a
    linear_combination (-4) * hc
  refine ⟨⟨A, 2 * k - b, -c⟩, ⟨hdisc, ⟨hA, by rw [hdisc]; exact hD⟩, hprim⟩, 1, g, one_ne_zero,
    intCast_ne_zero' hg.ne', ?_⟩
  rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, one_mul, hIeq, formIdeal_eq_lat hdisc]
  congr 1
  exact lat_congr (by show k = (b + (2 * k - b)) / 2; omega) _ _

/-- The conjugate form `(a, -b, c)`. -/
def conjF (f : BQF) : BQF := ⟨f.a, -f.b, f.c⟩

theorem disc_conjF (f : BQF) : (conjF f).disc = f.disc := by
  simp only [conjF, BQF.disc]; ring

theorem bezout_of_isPrimitive {f : BQF} (hf : f.IsPrimitive) :
    ∃ u v w : ℤ, u * f.a + v * f.b + w * f.c = 1 := by
  have h1 : ((f.content : ℕ) : ℤ) = f.a * Int.gcdA f.a (Int.gcd f.b f.c) +
      (Int.gcd f.b f.c : ℤ) * Int.gcdB f.a (Int.gcd f.b f.c) := Int.gcd_eq_gcd_ab _ _
  have h2 := Int.gcd_eq_gcd_ab f.b f.c
  have hc : ((f.content : ℕ) : ℤ) = 1 := by rw [show f.content = 1 from hf]; rfl
  refine ⟨Int.gcdA f.a (Int.gcd f.b f.c), Int.gcdB f.a (Int.gcd f.b f.c) * Int.gcdA f.b f.c,
    Int.gcdB f.a (Int.gcd f.b f.c) * Int.gcdB f.b f.c, ?_⟩
  linear_combination -h1 + hc - Int.gcdB f.a (Int.gcd f.b f.c) * h2

/-- **(d2)** `I_f · I_{f̄} = (f.a)` for a primitive form `f` of discriminant `D`: `I_f` is invertible. -/
theorem formIdeal_mul_conj {f : BQF} (hf : f.disc = b ^ 2 + 4 * a) (hp : f.IsPrimitive) :
    (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) * formIdeal (conjF f) =
      Ideal.span {(f.a : QuadraticAlgebra ℤ a b)} := by
  have hf' : (conjF f).disc = b ^ 2 + 4 * a := (disc_conjF f).trans hf
  have h2 := two_mul_kf hf
  rw [formIdeal_eq_lat hf, formIdeal_eq_lat hf']
  obtain ⟨u, v, w, huvw⟩ := bezout_of_isPrimitive hp
  have e : lat (conjF f).a ((b + (conjF f).b) / 2) (kf_dvd hf') =
      (lat f.a (b - (b + f.b) / 2) (conj_dvd (kf_dvd hf)) : Ideal (QuadraticAlgebra ℤ a b)) :=
    lat_congr (by show (b + -f.b) / 2 = b - (b + f.b) / 2; omega) _ _
  rw [e]
  exact lat_mul_lat_star (kf_rel hf)
    ⟨u, v, w, by rw [show 2 * ((b + f.b) / 2) - b = f.b by omega]; exact huvw⟩

/-- A primitive form takes a value prime to `p` at a first column of some `γ ∈ SL(2, ℤ)`. -/
theorem exists_act_not_dvd {f : BQF} (hf : f.IsPrimitive) {p : ℕ} (hp : p.Prime) :
    ∃ γ : SL(2, ℤ), ¬ (p : ℤ) ∣ (act γ f).a := by
  by_contra h
  push_neg at h
  have h1 : (p : ℤ) ∣ f.a := by
    have h0 := h ⟨!![1, 0; 0, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩
    have e : (act ⟨!![1, 0; 0, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩ f).a = f.a := by
      show f.eval 1 0 = f.a
      simp [BQF.eval]
    rwa [e] at h0
  have h2 : (p : ℤ) ∣ f.c := by
    have h0 := h ModularGroup.S
    rwa [act_S] at h0
  have h3 : (p : ℤ) ∣ f.a + f.b + f.c := by
    have h0 := h ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩
    have e : (act ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩ f).a = f.a + f.b + f.c := by
      show f.eval 1 1 = f.a + f.b + f.c
      simp [BQF.eval]
    rwa [e] at h0
  have h4 : (p : ℤ) ∣ f.b := by
    have h5 := dvd_sub (dvd_sub h3 h1) h2
    have e : f.a + f.b + f.c - f.a - f.c = f.b := by ring
    rwa [e] at h5
  have h6 := f.dvd_content h1 h4 h2
  rw [show f.content = 1 from hf] at h6
  exact hp.one_lt.ne' (Nat.dvd_one.mp h6)

/-- Every form class has a representative whose first coefficient is prime to `p`. -/
theorem exists_rep_not_dvd {D : ℤ} {f : BQF} (hf : f ∈ primForms D) {p : ℕ} (hp : p.Prime) :
    ∃ γ : SL(2, ℤ), act γ f ∈ primForms D ∧ ¬ (p : ℤ) ∣ (act γ f).a := by
  obtain ⟨γ, hγ⟩ := exists_act_not_dvd hf.2.2 hp
  refine ⟨γ, ?_, hγ⟩
  rw [act_eq_smul]
  exact (primForms D).smul_mem γ⁻¹ hf

/-- **Representatives prime to `p`.** Every invertible ideal is in the class of `I_f` for a primitive positive
definite form `f` of discriminant `D` with `p ∤ f.a`; then `I_f · I_{f̄} = (f.a)`. -/
theorem exists_formIdeal_rel_not_dvd (hD : b ^ 2 + 4 * a < 0) {I J : Ideal (QuadraticAlgebra ℤ a b)}
    {ν : QuadraticAlgebra ℤ a b} (hν : ν ≠ 0) (hIJ : I * J = Ideal.span {ν}) {p : ℕ} (hp : p.Prime) :
    ∃ f ∈ primForms (b ^ 2 + 4 * a), ¬ (p : ℤ) ∣ f.a ∧ IdealRel I (formIdeal f) ∧
      (formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) * formIdeal (conjF f) =
        Ideal.span {(f.a : QuadraticAlgebra ℤ a b)} := by
  obtain ⟨f, hf, hrel⟩ := exists_formIdeal_rel hD hν hIJ
  obtain ⟨γ, hγf, hγp⟩ := exists_rep_not_dvd hf hp
  exact ⟨act γ f, hγf, hγp, hrel.trans hD (idealRel_act hf γ), formIdeal_mul_conj hγf.1 hγf.2.2⟩

end RPLib.DWS.QA


