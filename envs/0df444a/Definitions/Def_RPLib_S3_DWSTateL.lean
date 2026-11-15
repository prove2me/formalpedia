-- Prove2me | Definitions.Def_RPLib_S3_DWSTateL
-- name    : RPLib_S3_DWSTateL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:43:58.830195+00:00
-- url     : https://prove2.me/theorems/3bcc64ee-dbeb-47df-afab-072bfd2fd7a4
-- title:
--   Weight-two Ramanujan-Petersson library: proper ⇒ invertible; `R`-stable quotients are kernel-ideal quotients (b7c, b7)
-- statement:
--   Proper ⇒ invertible; `R`-stable quotients are kernel-ideal quotients (b7c, b7).
--
--   Algebra (`R` a domain, `I = annOf I' n = {x | x I' ⊆ nR}`):
--   * `annOf_mul_eq_of_inv`: if `I' I'' = (M)`, `M ≠ 0` and `n ∈ I'`, then `I · I' = (n)`.
--   * `mem_of_annOf_dvd`: if `I · I' = (n)` and `t I ⊆ nR` then `t ∈ I'`.
--   * `QA.exists_inv_of_proper` (`R = QuadraticAlgebra ℤ a b`, `D < 0`): `n ∈ I'` and properness
--     (`y I' ⊆ n I'` ⇒ `n ∣ y`) make the Hermite form of `I'` primitive, so `I' Ī' = (M)`.
--   * `QA.annOf_mul_eq`: proper ⇒ `I · I' = (n)`.
--
--   Curves:
--   * **`exists_good_kerI_eq`** (b7c): an `R`-linear prime-to-`p` Vélu quotient `E → E₁` with kernel `G` has
--     `G = E[I]` for a good ideal `I`.
--   * **`exists_quotClass_of_isQuot`**, **`exists_quotClass_of_isog`** (b7): a prime-to-`p` Frobenius-equivariant
--     isogeny `u : E → E₁` (with `w u = [N]`, `u w = [N]`) between Frobenius-normalised `R`-structures gives
--     `QuotClass E₁ hD s c` for some class `c`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateK

/-!
# S3-DWS-Tate, part L: proper ⇒ invertible; `R`-stable quotients are kernel-ideal quotients (b7c, b7)

Algebra (`R` a domain, `I = annOf I' n = {x | x I' ⊆ nR}`):
* `annOf_mul_eq_of_inv`: if `I' I'' = (M)`, `M ≠ 0` and `n ∈ I'`, then `I · I' = (n)`.
* `mem_of_annOf_dvd`: if `I · I' = (n)` and `t I ⊆ nR` then `t ∈ I'`.
* `QA.exists_inv_of_proper` (`R = QuadraticAlgebra ℤ a b`, `D < 0`): `n ∈ I'` and properness
  (`y I' ⊆ n I'` ⇒ `n ∣ y`) make the Hermite form of `I'` primitive, so `I' Ī' = (M)`.
* `QA.annOf_mul_eq`: proper ⇒ `I · I' = (n)`.

Curves:
* **`exists_good_kerI_eq`** (b7c): an `R`-linear prime-to-`p` Vélu quotient `E → E₁` with kernel `G` has
  `G = E[I]` for a good ideal `I`.
* **`exists_quotClass_of_isQuot`**, **`exists_quotClass_of_isog`** (b7): a prime-to-`p` Frobenius-equivariant
  isogeny `u : E → E₁` (with `w u = [N]`, `u w = [N]`) between Frobenius-normalised `R`-structures gives
  `QuotClass E₁ hD s c` for some class `c`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse QuadraticAlgebra RamanujanPetersson.Hurwitz

section LGen

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If `I' I'' = (M)` with `M ≠ 0` and `n ∈ I'`, then `annOf I' n · I' = (n)`. -/
theorem annOf_mul_eq_of_inv {I' I'' : Ideal R} {n : ℕ} {M : R} (hM0 : M ≠ 0)
    (hM : I' * I'' = Ideal.span {M}) (hnI : (n : R) ∈ I') :
    annOf I' n * I' = Ideal.span {(n : R)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx t ht
    exact Ideal.mem_span_singleton.mpr ((mem_annOf.mp hx) t ht)
  · have le2 : Ideal.span {(n : R)} * I'' ≤ Ideal.span {M} * annOf I' n := by
      rw [Ideal.span_singleton_mul_le_span_singleton_mul]
      intro z hz
      have h1 : (n : R) * z ∈ Ideal.span {M} := by rw [← hM]; exact Ideal.mul_mem_mul hnI hz
      obtain ⟨x0, hx0⟩ := Ideal.mem_span_singleton'.mp h1
      refine ⟨x0, mem_annOf.mpr fun t ht => ?_, hx0.symm.trans (mul_comm _ _)⟩
      have h2 : t * z ∈ Ideal.span {M} := by rw [← hM]; exact Ideal.mul_mem_mul ht hz
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h2
      refine ⟨e, mul_right_cancel₀ hM0 ?_⟩
      linear_combination t * hx0 - (n : R) * he
    rw [← Ideal.span_singleton_mul_right_mono hM0]
    calc Ideal.span {M} * Ideal.span {(n : R)} = Ideal.span {(n : R)} * (I' * I'') := by
          rw [hM]; ring
      _ = I' * (Ideal.span {(n : R)} * I'') := by ring
      _ ≤ I' * (Ideal.span {M} * annOf I' n) := Ideal.mul_mono_right le2
      _ = Ideal.span {M} * (annOf I' n * I') := by ring

/-- If `annOf I' n · I' = (n)` and `t · annOf I' n ⊆ (n)`, then `t ∈ I'`. -/
theorem mem_of_annOf_dvd {I' : Ideal R} {n : ℕ} (hn : (n : R) ≠ 0)
    (hII : annOf I' n * I' = Ideal.span {(n : R)}) {t : R}
    (ht : ∀ x ∈ annOf I' n, (n : R) ∣ x * t) : t ∈ I' := by
  rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_mul_right_mono hn]
  calc Ideal.span {(n : R)} * Ideal.span {t} = Ideal.span {t} * (annOf I' n * I') := by
        rw [hII]; ring
    _ = (Ideal.span {t} * annOf I' n) * I' := by ring
    _ ≤ Ideal.span {(n : R)} * I' :=
        Ideal.mul_mono_left (Ideal.span_singleton_mul_le_iff.mpr fun x hx =>
          Ideal.mem_span_singleton.mpr (by rw [mul_comm]; exact ht x hx))

end LGen

section LQA

variable {a b : ℤ}

/-- `(ω - (b - k)) · lat A k ⊆ (c₀) · lat A k` when `c₀` divides `A`, `2k - b` and `c`. -/
theorem QA.span_gen_mul_lat_le {A k c c0 A1 B1 C1 : ℤ} {hk : A ∣ a + k * b - k ^ 2}
    (hc : a + k * b - k ^ 2 = A * c) (hA1' : A = c0 * A1) (hB1' : 2 * k - b = c0 * B1)
    (hC1' : -c = c0 * C1) :
    Ideal.span {(⟨-(b - k), 1⟩ : QuadraticAlgebra ℤ a b)} * QA.lat A k hk ≤
      Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * QA.lat A k hk := by
  set z : QuadraticAlgebra ℤ a b := ⟨-(b - k), 1⟩ with hz
  rw [QA.lat_eq_span, QA.span_pair_mul, QA.span_pair_mul, Ideal.span_le]
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

/-- **Proper ⇒ invertible.** If `n ∈ I'` (`n ≠ 0`) and `y I' ⊆ n I'` forces `n ∣ y`, then the Hermite form
`I' = (g) · lat A k` has a primitive form, so `I' · Ī' = (g² A)`. -/
theorem QA.exists_inv_of_proper (hD : b ^ 2 + 4 * a < 0) {I' : Ideal (QuadraticAlgebra ℤ a b)} {n : ℕ}
    (hn : n ≠ 0) (hnI : (n : QuadraticAlgebra ℤ a b) ∈ I')
    (hprop : ∀ y : QuadraticAlgebra ℤ a b, (∀ t ∈ I', ∃ t' ∈ I', y * t = n * t') →
      (n : QuadraticAlgebra ℤ a b) ∣ y) :
    ∃ I'' : Ideal (QuadraticAlgebra ℤ a b), ∃ M : QuadraticAlgebra ℤ a b,
      M ≠ 0 ∧ I' * I'' = Ideal.span {M} := by
  haveI := QA.isDomain hD
  have hnZ : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hnI' : ((n : ℤ) : QuadraticAlgebra ℤ a b) ∈ I' := by rw [Int.cast_natCast]; exact hnI
  have hI'ne : I' ≠ ⊥ := by
    rintro rfl
    exact QA.intCast_ne_zero' hnZ ((Submodule.mem_bot _).mp hnI')
  obtain ⟨g, A, k, hk, hg, hA, hI'eq⟩ := QA.exists_hermite hD hI'ne
  obtain ⟨c, hc⟩ := id hk
  set f : BQF := ⟨A, 2 * k - b, -c⟩ with hf
  obtain ⟨A1, hA1⟩ := f.content_dvd_a
  obtain ⟨B1, hB1⟩ := f.content_dvd_b
  obtain ⟨C1, hC1⟩ := f.content_dvd_c
  set c0 : ℤ := (f.content : ℤ) with hc0
  have hA1' : A = c0 * A1 := hA1
  have hB1' : 2 * k - b = c0 * B1 := hB1
  have hC1' : -c = c0 * C1 := hC1
  set z : QuadraticAlgebra ℤ a b := ⟨-(b - k), 1⟩ with hz
  have hzI : Ideal.span {z} * I' ≤ Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * I' := by
    rw [hI'eq]
    calc Ideal.span {z} * (Ideal.span {(g : QuadraticAlgebra ℤ a b)} * QA.lat A k hk)
        = Ideal.span {(g : QuadraticAlgebra ℤ a b)} * (Ideal.span {z} * QA.lat A k hk) := by ring
      _ ≤ Ideal.span {(g : QuadraticAlgebra ℤ a b)} *
          (Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} * QA.lat A k hk) :=
          Ideal.mul_mono_right (QA.span_gen_mul_lat_le hc hA1' hB1' hC1')
      _ = Ideal.span {(c0 : QuadraticAlgebra ℤ a b)} *
          (Ideal.span {(g : QuadraticAlgebra ℤ a b)} * QA.lat A k hk) := by ring
  -- `A ∣ n`, hence `c₀ ∣ n`
  have hAn : A ∣ (n : ℤ) := by
    rw [hI'eq] at hnI'
    obtain ⟨w, hw, hwn⟩ := Ideal.mem_span_singleton_mul.mp hnI'
    have him := congrArg QuadraticAlgebra.im hwn
    have hre := congrArg QuadraticAlgebra.re hwn
    rw [QA.im_intCast_mul, im_intCast] at him
    rw [QA.re_intCast_mul, re_intCast, Int.cast_id] at hre
    have hw0 : w.im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact absurd h hg.ne'
      · exact h
    have hAw : A ∣ w.re := by
      have := QA.mem_lat.mp hw
      rwa [hw0, mul_zero, add_zero] at this
    rw [← hre]
    exact dvd_mul_of_dvd_right hAw g
  obtain ⟨m, hm⟩ : c0 ∣ (n : ℤ) := (show c0 ∣ A from ⟨A1, hA1'⟩).trans hAn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hnZ hm
  have hnc : (n : QuadraticAlgebra ℤ a b) = (c0 : QuadraticAlgebra ℤ a b) * (m : QuadraticAlgebra ℤ a b) := by
    rw [← Int.cast_mul, ← hm, Int.cast_natCast]
  -- properness applied to `y = m (ω - (b - k))` gives `c₀ = 1`
  obtain ⟨e, he⟩ := hprop ((m : QuadraticAlgebra ℤ a b) * z) (fun t ht => by
    have h1 : z * t ∈ Ideal.span {z} * I' := Ideal.mem_span_singleton_mul.mpr ⟨t, ht, rfl⟩
    obtain ⟨t', ht', he⟩ := Ideal.mem_span_singleton_mul.mp (hzI h1)
    refine ⟨t', ht', ?_⟩
    linear_combination (-(m : QuadraticAlgebra ℤ a b)) * he - t' * hnc)
  have he' : (m : QuadraticAlgebra ℤ a b) * z = ((n : ℤ) : QuadraticAlgebra ℤ a b) * e := by
    rw [Int.cast_natCast]; exact he
  have him := congrArg QuadraticAlgebra.im he'
  rw [QA.im_intCast_mul, QA.im_intCast_mul] at him
  have hzim : z.im = 1 := rfl
  have h1 : c0 * e.im = 1 := by
    apply mul_left_cancel₀ hm0
    linear_combination -him + m * hzim - e.im * hm
  have hc01 : c0 = 1 := Int.eq_one_of_dvd_one (by rw [hc0]; positivity) ⟨e.im, h1.symm⟩
  have hprim : f.IsPrimitive := by
    show f.content = 1
    have h1' : ((f.content : ℕ) : ℤ) = 1 := hc01
    exact_mod_cast h1'
  -- `I' · Ī' = (g² A)`
  obtain ⟨u, v, w, huvw⟩ := QA.bezout_of_isPrimitive hprim
  have hstar := QA.lat_mul_lat_star (hk := hk) (C := -c) (by rw [hc]; ring) ⟨u, v, w, huvw⟩
  have hg0 : (g : QuadraticAlgebra ℤ a b) ≠ 0 := QA.intCast_ne_zero' hg.ne'
  have hA0 : (A : QuadraticAlgebra ℤ a b) ≠ 0 := QA.intCast_ne_zero' hA.ne'
  refine ⟨Ideal.span {(g : QuadraticAlgebra ℤ a b)} * QA.lat A (b - k) (QA.conj_dvd hk),
    (g : QuadraticAlgebra ℤ a b) * g * A, mul_ne_zero (mul_ne_zero hg0 hg0) hA0, ?_⟩
  rw [hI'eq]
  calc Ideal.span {(g : QuadraticAlgebra ℤ a b)} * QA.lat A k hk *
        (Ideal.span {(g : QuadraticAlgebra ℤ a b)} * QA.lat A (b - k) (QA.conj_dvd hk))
      = Ideal.span {(g : QuadraticAlgebra ℤ a b)} * Ideal.span {(g : QuadraticAlgebra ℤ a b)} *
        (QA.lat A k hk * QA.lat A (b - k) (QA.conj_dvd hk)) := by ring
    _ = Ideal.span {(g : QuadraticAlgebra ℤ a b) * g * A} := by
        rw [hstar, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]

/-- **Proper ⇒ `I · I' = (n)`** for `I = annOf I' n`. -/
theorem QA.annOf_mul_eq (hD : b ^ 2 + 4 * a < 0) {I' : Ideal (QuadraticAlgebra ℤ a b)} {n : ℕ}
    (hn : n ≠ 0) (hnI : (n : QuadraticAlgebra ℤ a b) ∈ I')
    (hprop : ∀ y : QuadraticAlgebra ℤ a b, (∀ t ∈ I', ∃ t' ∈ I', y * t = n * t') →
      (n : QuadraticAlgebra ℤ a b) ∣ y) :
    annOf I' n * I' = Ideal.span {(n : QuadraticAlgebra ℤ a b)} := by
  haveI := QA.isDomain hD
  obtain ⟨I'', M, hM0, hM⟩ := QA.exists_inv_of_proper hD hn hnI hprop
  exact annOf_mul_eq_of_inv hM0 hM hnI

end LQA

section LCurve

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic] {a b : ℤ}
  {s : OAct (QuadraticAlgebra ℤ a b) W L} {s₁ : OAct (QuadraticAlgebra ℤ a b) W₁ L}

/-- **(b7c)** An `R`-linear prime-to-`p` Vélu quotient `E → E₁` with kernel `G` is `E → E/E[I]` for a
good ideal `I` (`I = annOf I' n`, `I' = {r | ι r P₀ ∈ G}`, `I · I' = (n)`). -/
theorem exists_good_kerI_eq (hD : b ^ 2 + 4 * a < 0) {G : AddSubgroup (Pt W L)}
    {φ : Pt W L →+ Pt W₁ L} {ψ : Pt W₁ L →+ Pt W L} {n : ℕ} (hq : IsQuot G φ ψ n)
    (hφ : ∀ r, r ∈ commSub s s₁ φ) :
    ∃ I : Ideal (QuadraticAlgebra ℤ a b), GoodIdeal F I ∧ kerI s I = G := by
  haveI := QA.isDomain hD
  have hnR : (n : QuadraticAlgebra ℤ a b) ≠ 0 := natCast_ne_zero_QA hq.hn
  have hn0 : n ≠ 0 := fun h => hq.hn (by rw [h, Nat.cast_zero])
  have hnnF : ((n * n : ℕ) : F) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hq.hn hq.hn
  obtain ⟨P₁, h₁⟩ := exists_isGen s (n * n) hnnF
  have h₀ : IsGen s n (n • P₁) := h₁.nsmul_self hnR
  have hnI : (n : QuadraticAlgebra ℤ a b) ∈ idealOf s hq hφ (n • P₁) :=
    natCast_mem_idealOf hq hφ h₀.1
  have hII := QA.annOf_mul_eq hD hn0 hnI (fun y hy => proper_idealOf hq hφ h₁ hy)
  refine ⟨annOf (idealOf s hq hφ (n • P₁)) n, ⟨_, n, hII, hq.hn⟩, ?_⟩
  ext P
  rw [mem_kerI]
  constructor
  · intro hP
    have hnP : n • P = 0 := by rw [← s.natCast_apply]; exact hP _ (natCast_mem_annOf _ n)
    obtain ⟨t, rfl⟩ := h₀.exists_eq hq.hn hnP
    refine mem_idealOf.mp (mem_of_annOf_dvd hnR hII fun x hx => h₀.2 _ ?_)
    rw [s.ι_mul_apply]
    exact hP x hx
  · intro hP x hx
    obtain ⟨t, ht, rfl⟩ := (mem_iff_idealOf hq hφ h₀).mp hP
    obtain ⟨e, he⟩ := (mem_annOf.mp hx) t ht
    rw [← s.ι_mul_apply, he, s.ι_mul_apply, s.natCast_apply, ← map_nsmul, h₀.1, map_zero]

/-- **(b7c)** An `R`-linear prime-to-`p` Vélu quotient realises an ideal class. -/
theorem exists_quotClass_of_isQuot (hD : b ^ 2 + 4 * a < 0) {G : AddSubgroup (Pt W L)}
    {φ : Pt W L →+ Pt W₁ L} {ψ : Pt W₁ L →+ Pt W L} {n : ℕ} (hq : IsQuot G φ ψ n)
    (hφ : ∀ r, r ∈ commSub s s₁ φ) : ∃ c : QA.PicQ hD, QuotClass W₁ hD s c := by
  obtain ⟨I, hI, hker⟩ := exists_good_kerI_eq hD hq hφ
  refine ⟨picMk hD hI, I, hI, rfl, φ, ψ, n, ?_⟩
  rw [hker]
  exact hq

/-- **(b7)** A prime-to-`p` Frobenius-equivariant isogeny `u : E → E₁` (`w u = [N]`, `u w = [N]`, `p ∤ N`)
between Frobenius-normalised `R`-structures (`ι π = π_E`, `ι₁ π = π_{E₁}`, `p ∤ im π`) puts `E₁` in the
`Pic(R)`-orbit of `E`: `QuotClass E₁ hD s c` for some class `c`. -/
theorem exists_quotClass_of_isog (hD : b ^ 2 + 4 * a < 0) {π : QuadraticAlgebra ℤ a b}
    (hπ : s.ι π = piE W L) (hπ₁ : s₁.ι π = piE W₁ L) (hπF : (π.im.natAbs : F) ≠ 0) {N : ℕ}
    (hNF : (N : F) ≠ 0) {u : Pt W L →+ Pt W₁ L} {w : Pt W₁ L →+ Pt W L} (hu : IsIsog u)
    (hw : IsIsog w) (hwu : ∀ P, w (u P) = N • P) (huw : ∀ Q, u (w Q) = N • Q)
    (hfu : ∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (u P)) :
    ∃ c : QA.PicQ hD, QuotClass W₁ hD s c := by
  obtain ⟨ψ, n, hq⟩ := exists_isQuot_ker hNF hu hw hwu huw hfu
  exact exists_quotClass_of_isQuot hD hq (mem_commSub_of_frob hπ hπ₁ hπF hfu)

end LCurve

end RPLib.DWS


