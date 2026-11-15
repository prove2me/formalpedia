-- Prove2me | Definitions.Def_RPLib_S3_SSHasseB
-- name    : RPLib_S3_SSHasseB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:01.300756+00:00
-- url     : https://prove2.me/theorems/09ac92e2-39e8-4c31-9d17-356f6adaeb1b
-- title:
--   Weight-two Ramanujan-Petersson library: the Hasse invariant
-- statement:
--   The Hasse invariant.
--
--   In characteristic `p` odd, `hasseA p W = [X^{p-1}] g_E^{(p-1)/2}` and `hasseM p m W = [X^{p^m-1}] g_E^{(p^m-1)/2}`.
--   * `hasseM_succ` (Manin) : `hasseM p (m+1) W = hasseA p W · (hasseM p m W)^p`;
--     `hasseA_eq_zero_of_hasseM` : `hasseM p m W = 0 → hasseA p W = 0`.
--   * `hasseA_variableChange` : `hasseA (C • W) · u⁻²⁽ᵖ⁻¹⁾ = u⁻⁶ⁿ · hasseA W`, so `hasseA` vanishes on whole
--     isomorphism classes (`hasseA_variableChange_eq_zero`); `hasseA_map` : compatible with field maps.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_SSHasseA

/-!
# S3-DWS-Supersingular, part B2/B3: the Hasse invariant

In characteristic `p` odd, `hasseA p W = [X^{p-1}] g_E^{(p-1)/2}` and `hasseM p m W = [X^{p^m-1}] g_E^{(p^m-1)/2}`.
* `hasseM_succ` (Manin) : `hasseM p (m+1) W = hasseA p W · (hasseM p m W)^p`;
  `hasseA_eq_zero_of_hasseM` : `hasseM p m W = 0 → hasseA p W = 0`.
* `hasseA_variableChange` : `hasseA (C • W) · u⁻²⁽ᵖ⁻¹⁾ = u⁻⁶ⁿ · hasseA W`, so `hasseA` vanishes on whole
  isomorphism classes (`hasseA_variableChange_eq_zero`); `hasseA_map` : compatible with field maps.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve RPLib RPLib.TateNF

namespace RamanujanPetersson.S3.DWSS

section HasseB

variable {F : Type*} [Field F] (p : ℕ)

/-- The Hasse invariant `[X^{p-1}] g_E^{(p-1)/2}`. -/
noncomputable def hasseA (W : WeierstrassCurve F) : F := (gE W ^ ((p - 1) / 2)).coeff (p - 1)

/-- `[X^{p^m-1}] g_E^{(p^m-1)/2}`. -/
noncomputable def hasseM (m : ℕ) (W : WeierstrassCurve F) : F :=
  (gE W ^ ((p ^ m - 1) / 2)).coeff (p ^ m - 1)

lemma hasseA_map {L : Type*} [Field L] (f : F →+* L) (W : WeierstrassCurve F) :
    hasseA p (W.map f) = f (hasseA p W) := by
  have : gE (W.map f) = (gE W).map f := by
    simp only [gE, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, map_b₂,
      map_b₄, map_b₆, map_mul, map_ofNat, Polynomial.map_ofNat]
  rw [hasseA, hasseA, this, ← Polynomial.map_pow, coeff_map]

variable [Fact p.Prime] [CharP F p]

lemma coeff_pow_char (f : F[X]) (j : ℕ) :
    (f ^ p).coeff j = if p ∣ j then f.coeff (j / p) ^ p else 0 := by
  rw [← map_frobenius_expand p f, coeff_map, coeff_expand (Fact.out : p.Prime).pos]
  split_ifs <;> simp [frobenius_def, (Fact.out : p.Prime).ne_zero]

lemma exp_succ (hp2 : p ≠ 2) (m : ℕ) :
    (p ^ (m + 1) - 1) / 2 = (p - 1) / 2 + p * ((p ^ m - 1) / 2) := by
  have hp : p.Prime := Fact.out
  have hpo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hao : p ^ m % 2 = 1 := Nat.odd_iff.mp (Odd.pow (Nat.odd_iff.mpr hpo))
  have h1 : 2 * ((p - 1) / 2) + 1 = p := by omega
  have h2 : 2 * ((p ^ m - 1) / 2) + 1 = p ^ m := by omega
  rw [pow_succ']
  generalize (p - 1) / 2 = S at h1 ⊢
  generalize (p ^ m - 1) / 2 = T at h2 ⊢
  rw [← h2, ← h1]
  have : (2 * S + 1) * (2 * T + 1) - 1 = 2 * (S + (2 * S + 1) * T) := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [this, Nat.mul_div_cancel_left _ two_pos]

/-- **B2 (Manin).** `hasseM p (m+1) W = hasseA p W · (hasseM p m W)^p`. -/
theorem hasseM_succ (hp2 : p ≠ 2) (W : WeierstrassCurve F) (m : ℕ) :
    hasseM p (m + 1) W = hasseA p W * hasseM p m W ^ p := by
  have hp : p.Prime := Fact.out
  have hpo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hp1 := hp.one_lt
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
  have hpm1 : p ^ (m + 1) = p * p ^ m := pow_succ' p m
  set n := (p - 1) / 2 with hn
  have hdeg : (gE W ^ n).natDegree ≤ n * 3 := natDegree_pow_le_of_le _ (natDegree_gE_le W)
  rw [hasseM, exp_succ p hp2, pow_add, mul_comm p, pow_mul, coeff_mul]
  rw [Finset.sum_eq_single (p - 1, p ^ (m + 1) - 1 - (p - 1))]
  · rw [coeff_pow_char p, if_pos, hasseA, hasseM]
    · congr 2; rw [hpm1]
      have : p * p ^ m - 1 - (p - 1) = p * (p ^ m - 1) := by rw [Nat.mul_sub_one]; omega
      rw [this, Nat.mul_div_cancel_left _ hp.pos]
    · rw [hpm1]; exact ⟨p ^ m - 1, by rw [Nat.mul_sub_one]; omega⟩
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    simp only at hab
    by_cases ha : n * 3 < a
    · rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt ha), zero_mul]
    rw [coeff_pow_char p]
    split_ifs with hb
    · exfalso
      have hsum : a + 1 + b = p ^ (m + 1) := by have := Nat.one_le_pow (m + 1) p hp.pos; omega
      have hd : p ∣ a + 1 := (Nat.dvd_add_left hb).mp (hsum ▸ dvd_pow_self p (Nat.succ_ne_zero m))
      obtain ⟨c, hc⟩ := hd
      rcases c with _ | _ | c
      · omega
      · apply hne; simp only [Prod.mk.injEq]; omega
      · have h2n : 2 * n + 1 = p := by omega
        have : 2 * p ≤ p * (c + 1 + 1) := by nlinarith
        omega
    · rw [mul_zero]
  · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp only
    have : p ≤ p ^ (m + 1) := by rw [hpm1]; exact Nat.le_mul_of_pos_right p hpm
    omega

omit [Fact p.Prime] [CharP F p] in
lemma hasseM_zero (W : WeierstrassCurve F) : hasseM p 0 W = 1 := by simp [hasseM]

/-- A vanishing `hasseM` forces a vanishing Hasse invariant. -/
theorem hasseA_eq_zero_of_hasseM (hp2 : p ≠ 2) (W : WeierstrassCurve F) {m : ℕ}
    (h : hasseM p m W = 0) : hasseA p W = 0 := by
  by_contra hA
  have : ∀ k, hasseM p k W ≠ 0 := by
    intro k
    induction k with
    | zero => rw [hasseM_zero]; exact one_ne_zero
    | succ k ih => rw [hasseM_succ p hp2]; exact mul_ne_zero hA (pow_ne_zero _ ih)
  exact this m h

/-- Taylor shift does not change the `X^{p-1}` coefficient of a polynomial of degree `≤ 2p-2`. -/
lemma coeff_comp_X_add_C (P : F[X]) (hP : P.natDegree ≤ 2 * p - 2) (r : F) :
    (P.comp (X + C r)).coeff (p - 1) = P.coeff (p - 1) := by
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  rw [← taylor_apply, taylor_coeff]
  have hd : (hasseDeriv (p - 1) P).natDegree < p :=
    (natDegree_hasseDeriv_le P (p - 1)).trans_lt (by omega)
  rw [eval_eq_sum_range' hd, Finset.sum_eq_single 0]
  · simp [hasseDeriv_coeff]
  · intro i hi hi0
    rw [Finset.mem_range] at hi
    rw [hasseDeriv_coeff]
    have : ((i + (p - 1)).choose (p - 1) : F) = 0 := by
      rw [CharP.cast_eq_zero_iff F p, add_comm]
      exact hp.dvd_choose_add (by omega) hi (by omega)
    rw [this, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hp.pos) h

lemma gE_variableChange_comp (W : WeierstrassCurve F) (V : VariableChange F) :
    (gE (V • W)).comp (C (ui V ^ 2) * X) = C (ui V ^ 6) * (gE W).comp (X + C V.r) := by
  simp only [gE, variableChange_b₂, variableChange_b₄, variableChange_b₆, add_comp, mul_comp, C_comp,
    pow_comp, X_comp]
  simp only [ui, map_mul, map_add, map_pow, map_ofNat]
  ring

/-- **B3.** `hasseA (V • W) · ui^{2(p-1)} = ui^{6n} · hasseA W`. -/
theorem hasseA_variableChange (W : WeierstrassCurve F) (V : VariableChange F) :
    hasseA p (V • W) * (ui V ^ 2) ^ (p - 1) = (ui V ^ 6) ^ ((p - 1) / 2) * hasseA p W := by
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  have e : (((gE (V • W)).comp (C (ui V ^ 2) * X)) ^ ((p - 1) / 2)).coeff (p - 1) =
      ((C (ui V ^ 6) * (gE W).comp (X + C V.r)) ^ ((p - 1) / 2)).coeff (p - 1) := by
    rw [gE_variableChange_comp]
  rw [← pow_comp, comp_C_mul_X_coeff, mul_pow, ← C_pow, coeff_C_mul, ← pow_comp,
    coeff_comp_X_add_C p _ ((natDegree_pow_le_of_le _ (natDegree_gE_le W)).trans (by omega))] at e
  exact e

theorem hasseA_variableChange_eq_zero (W : WeierstrassCurve F) (V : VariableChange F) :
    hasseA p (V • W) = 0 ↔ hasseA p W = 0 := by
  have h := hasseA_variableChange p W V
  have hu : ui V ≠ 0 := ui_ne_zero V
  constructor
  · intro h0; rw [h0, zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (pow_ne_zero _ hu))
  · intro h0; rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (pow_ne_zero _ hu))

end HasseB

end RamanujanPetersson.S3.DWSS


