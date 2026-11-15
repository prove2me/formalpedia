-- Prove2me | Definitions.Def_RPLib_S3_HasseWeilA
-- name    : RPLib_S3_HasseWeilA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:44:41.482505+00:00
-- url     : https://prove2.me/theorems/6f07600f-f06c-4134-b5f6-ec0898991c67
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, O6b part A: the two-sided bound along a progression
-- statement:
--   S3-ZetaSB, O6b part A: the two-sided bound along a progression.
--
--   For a function field `F / Fq` with full constant field, `N_m(F) = q ^ m + O(q ^ (m/2))` along `m ∈ D·ℕ`, `D > 0`:
--   take the Galois closure `E = GalE Fq F n` with a place of degree `ℓ = ℓ_E(0)` (`exists_galE_place`), `D = 2ℓ`,
--   `Q0 = q ^ (ℓ j)` (so `q ^ m = Q0 ^ 2`), a finite field `L` of large degree, and combine `lower_bound_core` (SB_GalC)
--   with `upper_bound_core` (SB_Upper).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBUpper
import Definitions.Def_RPLib_S3_SBClosB

/-!
# S3-ZetaSB, O6b part A: the two-sided bound along a progression

For a function field `F / Fq` with full constant field, `N_m(F) = q ^ m + O(q ^ (m/2))` along `m ∈ D·ℕ`, `D > 0`:
take the Galois closure `E = GalE Fq F n` with a place of degree `ℓ = ℓ_E(0)` (`exists_galE_place`), `D = 2ℓ`,
`Q0 = q ^ (ℓ j)` (so `q ^ m = Q0 ^ 2`), a finite field `L` of large degree, and combine `lower_bound_core` (SB_GalC)
with `upper_bound_core` (SB_Upper).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Module IsDedekindDomain

namespace RamanujanPetersson.ZetaSB

open RR

section HWA

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **O6b (A)**: `|N_{Dj}(F) - q ^ (Dj)| ≤ C √q ^ (Dj)` for all `j ≥ j0`, some `D > 0`. -/
theorem two_sided (hk : Places.constField Fq F = ⊥) :
    ∃ D : ℕ, 0 < D ∧ ∃ C : ℝ, ∃ j0 : ℕ, ∀ j : ℕ, j0 ≤ j →
      |(Places.numPoints Fq F (D * j) : ℝ) - (Fintype.card Fq : ℝ) ^ (D * j)| ≤
        C * Real.sqrt (Fintype.card Fq) ^ (D * j) := by
  classical
  obtain ⟨n, P0, hP0⟩ := exists_galE_place Fq F
  obtain ⟨p, hchar, r, hp, hcard⟩ := FiniteField.card' Fq
  haveI := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (GalE Fq F n) p := (Algebra.charP_iff Fq (GalE Fq F n) p).mp hchar
  set ℓ := ellF Fq (GalE Fq F n) 0 with hℓdef
  set gE := genusF Fq (GalE Fq F n) with hgE
  set G := Nat.card (GalE Fq F n ≃ₐ[RatFunc Fq] GalE Fq F n) with hG
  set Ci := Cinf Fq F with hCi
  have hℓ1 : 1 ≤ ℓ := by rw [← hP0]; exact P0.deg_pos
  have hr1 : 1 ≤ (r : ℕ) := r.pos
  refine ⟨2 * ℓ, by omega, (G * (2 * gE + 1) + (2 * gE + 1) + Ci : ℕ), (gE + ℓ) ^ 2 + 1, fun j hj => ?_⟩
  set m := 2 * ℓ * j with hm
  set Q0 := p ^ ((r : ℕ) * (ℓ * j)) with hQ0
  have hj1 : 1 ≤ j := by omega
  have hm0 : m ≠ 0 := by positivity
  have hq : Fintype.card Fq ^ m = Q0 ^ 2 := by
    rw [hcard, ← pow_mul, ← pow_mul]; congr 1; rw [hm]; ring
  have h2j : 2 ^ j ≤ Q0 := by
    calc 2 ^ j ≤ 2 ^ ((r : ℕ) * (ℓ * j)) :=
          Nat.pow_le_pow_right two_pos (by nlinarith)
      _ ≤ Q0 := Nat.pow_le_pow_left hp.two_le _
  have hQ1 : 1 ≤ Q0 := le_trans Nat.one_le_two_pow h2j
  have hQ0lt : (gE + ℓ) ^ 2 < ℓ ^ 2 * Q0 := by
    have h1 : (gE + ℓ) ^ 2 < 2 ^ j := lt_of_lt_of_le (by omega) (j.lt_two_pow_self).le
    have h2 : Q0 ≤ ℓ ^ 2 * Q0 := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hℓm : finrank Fq (Places.constField Fq (GalE Fq F n)) ∣ m := by
    rw [← RR.ellF_zero]; exact Dvd.intro (2 * j) (by rw [hm]; ring)
  set M := m * (finrank Fq[X] (Places.Rfin Fq (GalE Fq F n))).factorial with hM
  haveI : NeZero M := ⟨mul_ne_zero hm0 (Nat.factorial_ne_zero _)⟩
  have hL : M ∣ finrank Fq (FiniteField.Extension Fq p M) := by rw [FiniteField.finrank_extension]
  have hlo := lower_bound_core (FiniteField.Extension Fq p M) (closureEmb Fq F n) p ((r : ℕ) * (ℓ * j)) Q0 m
    hm0 rfl hq hℓm hL P0 hP0 hQ0lt
  have hup := upper_bound_core (FiniteField.Extension Fq p M) hk (closureEmb Fq F n) p ((r : ℕ) * (ℓ * j)) Q0 m
    hm0 rfl hq hℓm hL P0 hP0 hQ0lt
  have hsq : Real.sqrt (Fintype.card Fq) ^ m = (Q0 : ℝ) := by
    rw [show m = 2 * (ℓ * j) by rw [hm]; ring, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _), hcard, hQ0]
    push_cast
    rw [← pow_mul]
  have hqm : (Fintype.card Fq : ℝ) ^ m = (Q0 : ℝ) ^ 2 := by exact_mod_cast hq
  rw [hsq, hqm]
  have hlo' : (Q0 : ℝ) ^ 2 ≤ Places.numPoints Fq F m + G * ((2 * gE + 1) * Q0) := by exact_mod_cast hlo
  have hup' : (Places.numPoints Fq F m : ℝ) ≤ Q0 ^ 2 + (2 * gE + 1) * Q0 + Ci := by exact_mod_cast hup
  have hQ1' : (1 : ℝ) ≤ Q0 := by exact_mod_cast hQ1
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have hg0 : (0 : ℝ) ≤ gE := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ Ci := Nat.cast_nonneg _
  push_cast
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hQ1'), mul_nonneg (mul_nonneg hG0 (by positivity : (0 : ℝ) ≤ 2 * gE + 1))
      (by positivity : (0 : ℝ) ≤ Q0)]
  · nlinarith [mul_nonneg hC0 (by positivity : (0 : ℝ) ≤ Q0), mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * gE + 1)
      (by positivity : (0 : ℝ) ≤ Q0)]

end HWA

end RamanujanPetersson.ZetaSB


