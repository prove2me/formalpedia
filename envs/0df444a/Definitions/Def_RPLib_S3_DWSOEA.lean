-- Prove2me | Definitions.Def_RPLib_S3_DWSOEA
-- name    : RPLib_S3_DWSOEA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:20:12.080145+00:00
-- url     : https://prove2.me/theorems/2a31f170-019f-48e7-a71a-5cb47f46f9d8
-- title:
--   Weight-two Ramanujan-Petersson library: summing the level-`ℓ` counts over `δ` (towards the level-one p-chain)
-- statement:
--   Summing the level-`ℓ` counts over `δ` (towards the level-one p-chain).
--
--   For a prime `ℓ` and an integer matrix `γ` whose discriminant `tr² - 4 det` is prime to `ℓ`:
--   * `exact_iff_ne_zero` : a vector of `(ZMod ℓ)²` has exact order `ℓ` iff it is nonzero.
--   * `card_ker_two` : a nonzero singular `2 × 2` matrix over a finite field has `#K - 1` nonzero kernel vectors.
--   * **`sum_levelCount`** : `Σ_δ levelCount ℓ δ γ = (ℓ - 1) · #{x : x² - tr γ · x + det γ = 0}`.
--   * **`sum_ellCount`** : `Σ_δ ellCount ℓ δ t n = (ℓ - 1) · r(t, n) · ellCount 1 1 t n` when `ℓ ∤ t² - 4n`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesD

/-!
# S3-DWS-Ordinary, part EA: summing the level-`ℓ` counts over `δ` (towards the level-one p-chain)

For a prime `ℓ` and an integer matrix `γ` whose discriminant `tr² - 4 det` is prime to `ℓ`:
* `exact_iff_ne_zero` : a vector of `(ZMod ℓ)²` has exact order `ℓ` iff it is nonzero.
* `card_ker_two` : a nonzero singular `2 × 2` matrix over a finite field has `#K - 1` nonzero kernel vectors.
* **`sum_levelCount`** : `Σ_δ levelCount ℓ δ γ = (ℓ - 1) · #{x : x² - tr γ · x + det γ = 0}`.
* **`sum_ellCount`** : `Σ_δ ellCount ℓ δ t n = (ℓ - 1) · r(t, n) · ellCount 1 1 t n` when `ℓ ∤ t² - 4n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix

namespace RamanujanPetersson.S3.DWSO

open RamanujanPetersson.S3.Conj

section Kernel

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem card_ker_two {B : Matrix (Fin 2) (Fin 2) K} (h0 : B ≠ 0) (hdet : B.det = 0) :
    (Finset.univ.filter fun v : Fin 2 → K => v ≠ 0 ∧ B *ᵥ v = 0).card = Fintype.card K - 1 := by
  set f := Matrix.toLin' B with hf
  have hker : Module.finrank K (LinearMap.ker f) = 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at hsum
    have h1 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero] at h
      obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      apply hv
      have : v ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply]; exact hBv
      rw [h] at this
      exact (Submodule.mem_bot K).mp this
    have h2 : Module.finrank K (LinearMap.range f) ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
      apply h0
      exact Matrix.toLin'.injective (by rw [← hf, h, map_zero])
    omega
  have hcard : Nat.card (LinearMap.ker f) = Fintype.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K), hker, pow_one, Nat.card_eq_fintype_card]
  have hall : (Finset.univ.filter fun v : Fin 2 → K => B *ᵥ v = 0).card = Fintype.card K := by
    rw [← hcard, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply])
  have e : (Finset.univ.filter fun v : Fin 2 → K => v ≠ 0 ∧ B *ᵥ v = 0) =
      (Finset.univ.filter fun v : Fin 2 → K => B *ᵥ v = 0).erase 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [e, Finset.card_erase_of_mem (by simp), hall]

end Kernel

section Level

variable {ℓ : ℕ} [NeZero ℓ] [Fact ℓ.Prime]

/-- The number of roots of `x² - t x + n` in `ZMod ℓ`. -/
noncomputable def rootCount (ℓ : ℕ) [NeZero ℓ] (t n : ℤ) : ℕ :=
  (Finset.univ.filter fun x : ZMod ℓ => x ^ 2 - (t : ZMod ℓ) * x + (n : ZMod ℓ) = 0).card

theorem exact_iff_ne_zero (v : Fin 2 → ZMod ℓ) :
    (∀ d ∈ Finset.range ℓ, 0 < d → d • v ≠ 0) ↔ v ≠ 0 := by
  constructor
  · intro h
    simpa using h 1 (Finset.mem_range.2 (Fact.out : ℓ.Prime).one_lt) one_pos
  · intro hv d hd hd0
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ)]
    refine smul_ne_zero ?_ hv
    rw [Ne, CharP.cast_eq_zero_iff (ZMod ℓ) ℓ]
    intro h
    rw [Finset.mem_range] at hd
    exact absurd (Nat.le_of_dvd hd0 h) (by omega)

theorem levelCount_prime (δ : ZMod ℓ) (γ : Mat) :
    levelCount ℓ δ γ = (Finset.univ.filter fun v : Fin 2 → ZMod ℓ =>
      v ≠ 0 ∧ (γ.map (Int.castRingHom (ZMod ℓ)) - δ • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))) *ᵥ v = 0).card := by
  rw [levelCount]
  refine congrArg Finset.card (Finset.filter_congr fun v _ => ?_)
  rw [exact_iff_ne_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem det_sub (γ : Mat) (δ : ZMod ℓ) :
    (γ.map (Int.castRingHom (ZMod ℓ)) - δ • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))).det =
      δ ^ 2 - (γ.trace : ZMod ℓ) * δ + (γ.det : ZMod ℓ) := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp
  ring

theorem sub_ne_zero_of (γ : Mat) (hD : ¬ (ℓ : ℤ) ∣ γ.trace ^ 2 - 4 * γ.det) (δ : ZMod ℓ) :
    γ.map (Int.castRingHom (ZMod ℓ)) - δ • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ≠ 0 := by
  intro h
  have h00 : ((γ 0 0 : ℤ) : ZMod ℓ) - δ = 0 := by simpa [Matrix.one_apply] using congrFun (congrFun h 0) 0
  have h11 : ((γ 1 1 : ℤ) : ZMod ℓ) - δ = 0 := by simpa [Matrix.one_apply] using congrFun (congrFun h 1) 1
  have h01 : ((γ 0 1 : ℤ) : ZMod ℓ) = 0 := by simpa [Matrix.one_apply] using congrFun (congrFun h 0) 1
  apply hD
  rw [← CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ, Matrix.trace_fin_two, Matrix.det_fin_two]
  push_cast
  linear_combination (((γ 0 0 : ℤ) : ZMod ℓ) - ((γ 1 1 : ℤ) : ZMod ℓ)) * (h00 - h11) +
    4 * ((γ 1 0 : ℤ) : ZMod ℓ) * h01

/-- **`Σ_δ levelCount ℓ δ γ = (ℓ - 1) · r`** when `ℓ ∤ disc γ`. -/
theorem sum_levelCount (γ : Mat) (hD : ¬ (ℓ : ℤ) ∣ γ.trace ^ 2 - 4 * γ.det) :
    ∑ δ : ZMod ℓ, levelCount ℓ δ γ = (ℓ - 1) * rootCount ℓ γ.trace γ.det := by
  have h : ∀ δ : ZMod ℓ, levelCount ℓ δ γ =
      if δ ^ 2 - (γ.trace : ZMod ℓ) * δ + (γ.det : ZMod ℓ) = 0 then ℓ - 1 else 0 := by
    intro δ
    rw [levelCount_prime]
    split_ifs with hr
    · rw [card_ker_two (sub_ne_zero_of γ hD δ) (by rw [det_sub]; exact hr), ZMod.card]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro v - ⟨hv, hBv⟩
      exact hr (by rw [← det_sub]; exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hBv⟩)
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, rootCount, mul_comm]

/-- **`Σ_δ ellCount ℓ δ t n = (ℓ - 1) · r(t, n) · ellCount 1 1 t n`** when `ℓ ∤ t² - 4n`. -/
theorem sum_ellCount (t : ℤ) (n : ℕ) (hD : ¬ (ℓ : ℤ) ∣ t ^ 2 - 4 * n) :
    ∑ δ : ZMod ℓ, ellCount ℓ δ t n = (((ℓ - 1) * rootCount ℓ t n : ℕ) : ℚ) * ellCount 1 1 t n := by
  unfold ellCount
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  obtain ⟨hdet, htr, -⟩ := gammaQ_facts hQ
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_levelCount _ (by rw [hdet, htr]; exact hD), levelCount_one, hdet, htr]
  push_cast
  ring

end Level

end RamanujanPetersson.S3.DWSO


