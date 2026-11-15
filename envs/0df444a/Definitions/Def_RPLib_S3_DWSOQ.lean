-- Prove2me | Definitions.Def_RPLib_S3_DWSOQ
-- name    : RPLib_S3_DWSOQ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:41:01.549196+00:00
-- url     : https://prove2.me/theorems/a2ff2efd-dd4b-4cc5-8109-a875e86f2b8f
-- title:
--   Weight-two Ramanujan-Petersson library: `levelCount` of `γ_Q` through conjugation (O5, matrix half)
-- statement:
--   `levelCount` of `γ_Q` through conjugation (O5, matrix half).
--
--   * `levelCount_conj`: `A P = P B` with `det P` a unit mod `M` ⟹ `levelCount M δ A = levelCount M δ B`.
--   * `mulMat_shift`, **`levelCount_mulMat_eq`**: `levelCount M δ (mulMat (x + f ω))` depends only on `f`, the trace
--     and the discriminant of the order (`b² + 4a`).
--   * `gammaQ_mul`, **`levelCount_gammaQ`**: for `Q = f·[a',b',c']` and `(x,y)` with `Q'(x,y)` a unit mod `M`,
--     `levelCount M δ (γ_Q) = levelCount M δ (mulMat ((t - f b')/2 + f ω))` in `ℤ[ω]`, `ω² = -a'c' + b' ω`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOP

/-!
# S3-DWS-Ordinary, part Q: `levelCount` of `γ_Q` through conjugation (O5, matrix half)

* `levelCount_conj`: `A P = P B` with `det P` a unit mod `M` ⟹ `levelCount M δ A = levelCount M δ B`.
* `mulMat_shift`, **`levelCount_mulMat_eq`**: `levelCount M δ (mulMat (x + f ω))` depends only on `f`, the trace
  and the discriminant of the order (`b² + 4a`).
* `gammaQ_mul`, **`levelCount_gammaQ`**: for `Q = f·[a',b',c']` and `(x,y)` with `Q'(x,y)` a unit mod `M`,
  `levelCount M δ (γ_Q) = levelCount M δ (mulMat ((t - f b')/2 + f ω))` in `ℤ[ω]`, `ω² = -a'c' + b' ω`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

namespace RamanujanPetersson.S3.DWSO

theorem levelCount_conj (M : ℕ) [NeZero M] (δ' : ZMod M) {A B P : Matrix (Fin 2) (Fin 2) ℤ}
    (hP : IsUnit (P.map (Int.castRingHom (ZMod M))).det) (h : A * P = P * B) :
    levelCount M δ' A = levelCount M δ' B := by
  rw [levelCount_eq_natCard, levelCount_eq_natCard]
  set P' := P.map (Int.castRingHom (ZMod M)) with hP'def
  have hAB : A.map (Int.castRingHom (ZMod M)) * P' = P' * B.map (Int.castRingHom (ZMod M)) := by
    rw [hP'def, ← Matrix.map_mul, h, Matrix.map_mul]
  have hinv : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul P' hP
  have hinv' : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv P' hP
  have hinj : ∀ v w : Fin 2 → ZMod M, P' *ᵥ v = P' *ᵥ w → v = w := fun v w hvw => by
    have := congrArg (fun u => P'⁻¹ *ᵥ u) hvw
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this
    exact this
  have hB : B.map (Int.castRingHom (ZMod M)) = P'⁻¹ * A.map (Int.castRingHom (ZMod M)) * P' := by
    rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨P' *ᵥ v.1, ?_, ?_⟩) ⟨?_, ?_⟩)
  · intro d hd hd0 h0
    apply v.2.1 d hd hd0
    apply hinj
    rw [Matrix.mulVec_smul, h0, Matrix.mulVec_zero]
  · rw [Matrix.mulVec_mulVec, hAB, ← Matrix.mulVec_mulVec, v.2.2, Matrix.mulVec_smul]
  · intro v w hvw
    exact Subtype.ext (hinj _ _ (congrArg Subtype.val hvw))
  · rintro ⟨w, hw1, hw2⟩
    refine ⟨⟨P'⁻¹ *ᵥ w, ?_, ?_⟩, ?_⟩
    · intro d hd hd0 h0
      apply hw1 d hd hd0
      have := congrArg (fun u => P' *ᵥ u) h0
      simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    · rw [hB, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv', Matrix.mul_one, ← Matrix.mulVec_mulVec, hw2,
        Matrix.mulVec_smul]
    · apply Subtype.ext
      show P' *ᵥ (P'⁻¹ *ᵥ w) = w
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

/-- Change of basis `(1, ω) ↦ (1, ω + k)`. -/
lemma mulMat_shift (a b x f k : ℤ) :
    mulMat (⟨x, f⟩ : QuadraticAlgebra ℤ a b) * !![1, k; 0, 1] =
      !![1, k; 0, 1] * mulMat (⟨x - f * k, f⟩ : QuadraticAlgebra ℤ (a - k * b - k ^ 2) (b + 2 * k)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mulMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma two_dvd_sub_of_disc {a₁ b₁ a₂ b₂ : ℤ} (hD : b₁ ^ 2 + 4 * a₁ = b₂ ^ 2 + 4 * a₂) : 2 ∣ b₂ - b₁ := by
  by_contra h
  have ho : Odd (b₂ - b₁) := Int.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
  have ho2 : Odd (b₂ + b₁) := by
    have e : b₂ + b₁ = (b₂ - b₁) + 2 * b₁ := by ring
    rw [e]; exact ho.add_even (even_two_mul b₁)
  have hm := Int.odd_mul.mpr ⟨ho, ho2⟩
  have e : (b₂ - b₁) * (b₂ + b₁) = 2 * (2 * (a₁ - a₂)) := by linear_combination -hD
  rw [e] at hm
  exact Int.not_even_iff_odd.mpr hm (even_two_mul _)

/-- **`levelCount` of multiplication by `x + f ω` depends only on `f`, the trace and the discriminant.** -/
theorem levelCount_mulMat_eq (M : ℕ) [NeZero M] (δ' : ZMod M) {a₁ b₁ a₂ b₂ x₁ x₂ f : ℤ}
    (hD : b₁ ^ 2 + 4 * a₁ = b₂ ^ 2 + 4 * a₂) (ht : 2 * x₁ + f * b₁ = 2 * x₂ + f * b₂) :
    levelCount M δ' (mulMat (⟨x₁, f⟩ : QuadraticAlgebra ℤ a₁ b₁)) =
      levelCount M δ' (mulMat (⟨x₂, f⟩ : QuadraticAlgebra ℤ a₂ b₂)) := by
  obtain ⟨k, hk⟩ := two_dvd_sub_of_disc hD
  have hb : b₂ = b₁ + 2 * k := by linarith
  subst hb
  have ha : a₂ = a₁ - k * b₁ - k ^ 2 := by
    have e : 4 * a₂ = 4 * (a₁ - k * b₁ - k ^ 2) := by linear_combination -hD
    exact Int.eq_of_mul_eq_mul_left (by norm_num) e
  have hx : x₂ = x₁ - f * k := by
    have e : 2 * x₂ = 2 * (x₁ - f * k) := by linear_combination -ht
    exact Int.eq_of_mul_eq_mul_left (by norm_num) e
  subst ha hx
  exact levelCount_conj M δ' (P := !![1, k; 0, 1]) (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_fin_two_of]; simp)
    (mulMat_shift a₁ b₁ x₁ f k)

/-- `γ_{f Q'} P = P · (multiplication by (t - f b')/2 + f ω)` with `P = [v | K v]`, `v = (x, y)`. -/
lemma gammaQ_mul (a' b' c' f k x y : ℤ) :
    gammaQ (f * a', f * b', f * c') (2 * k + f * b') * !![x, -c' * y; y, a' * x + b' * y] =
      !![x, -c' * y; y, a' * x + b' * y] * mulMat (⟨k, f⟩ : QuadraticAlgebra ℤ (-(a' * c')) b') := by
  have e1 : (2 * k + f * b' - f * b') / 2 = k := by
    rw [show 2 * k + f * b' - f * b' = 2 * k by ring]; exact Int.mul_ediv_cancel_left k two_ne_zero
  have e2 : (2 * k + f * b' + f * b') / 2 = k + f * b' := by
    rw [show 2 * k + f * b' + f * b' = 2 * (k + f * b') by ring]
    exact Int.mul_ediv_cancel_left _ two_ne_zero
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gammaQ, mulMat, Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;> ring

/-- **(O5, matrix half)** `levelCount` of `γ_Q` for `Q = f·Q'`, given a value `Q'(x,y)` prime to `M`. -/
theorem levelCount_gammaQ (M : ℕ) [NeZero M] (δ' : ZMod M) (a' b' c' f t x y : ℤ) (ht : 2 ∣ t - f * b')
    (hunit : IsUnit ((a' * x ^ 2 + b' * x * y + c' * y ^ 2 : ℤ) : ZMod M)) :
    levelCount M δ' (gammaQ (f * a', f * b', f * c') t) =
      levelCount M δ' (mulMat (⟨(t - f * b') / 2, f⟩ : QuadraticAlgebra ℤ (-(a' * c')) b')) := by
  obtain ⟨k, hk⟩ := ht
  have htk : t = 2 * k + f * b' := by linarith
  have hk2 : (t - f * b') / 2 = k := by rw [hk]; exact Int.mul_ediv_cancel_left k two_ne_zero
  rw [hk2, htk]
  refine levelCount_conj M δ' ?_ (gammaQ_mul a' b' c' f k x y)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_fin_two_of]
  convert hunit using 1
  simp only [eq_intCast]; push_cast; ring

end RamanujanPetersson.S3.DWSO


