-- Prove2me | Definitions.Def_RPLib_S3_EllW2AS4
-- name    : RPLib_S3_EllW2AS4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:05:56.17144+00:00
-- url     : https://prove2.me/theorems/8b12a9a6-2a16-47c4-a991-0be28625b089
-- title:
--   The Eichler-Selberg trace formula in weight two: the squeeze `y0 → 0` and the residue statement P6
-- statement:
--   The squeeze `y0 → 0` and the residue statement P6.
--
--   * `A_le_B`, `ne_top_of_mul_le`, **`ev_fin`**: eventually (`s → 0+`) the lower integrals `A`, `B` are finite
--     and `s · B ≤ CB`; `E_ne_top`.
--   * `real_sandwich`, `scaled_sandwich`: `|π s a - y0 s e| ≤ 6 √y0 · CB` (real form of `fd_eCnt_le`).
--   * `tendsto_y0E`: `y0 · s · e(s, y0) → π · (π ρ / 3)`; `exists_y0`, `squeeze_step`.
--   * **`tendsto_sA`**: `s · A(s) → π ρ(n) / 3`; **`tendsto_sLS`**: `s · LS(s) → π ρ(n) / 3` in `ℂ`.
--   * `sum_inv_divisors`: `Σ_{h ∣ n} 1/h = σ₁(n)/n`; **`p6`** : `P6Stmt`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2AS3
import Definitions.Def_RPLib_S3_EllW2O7c

/-!
# S3-ES-Wt2 (O6, file AS4): the squeeze `y0 → 0` and the residue statement P6

* `A_le_B`, `ne_top_of_mul_le`, **`ev_fin`**: eventually (`s → 0+`) the lower integrals `A`, `B` are finite
  and `s · B ≤ CB`; `E_ne_top`.
* `real_sandwich`, `scaled_sandwich`: `|π s a - y0 s e| ≤ 6 √y0 · CB` (real form of `fd_eCnt_le`).
* `tendsto_y0E`: `y0 · s · e(s, y0) → π · (π ρ / 3)`; `exists_y0`, `squeeze_step`.
* **`tendsto_sA`**: `s · A(s) → π ρ(n) / 3`; **`tendsto_sLS`**: `s · LS(s) → π ρ(n) / 3` in `ℂ`.
* `sum_inv_divisors`: `Σ_{h ∣ n} 1/h = σ₁(n)/n`; **`p6`** : `P6Stmt`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ENNReal Modular Real

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma A_le_B (n : ℤ) (δ' : ZMod M) (s : ℝ) :
    (∫⁻ z in 𝒟, SNE M n δ' s z) ≤ ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) := by
  refine lintegral_mono fun z => ?_
  calc SNE M n δ' s z = SNE M n δ' s z * 1 := (mul_one _).symm
    _ ≤ SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) := by
      gcongr
      exact ENNReal.one_le_ofReal.2 (by linarith [Real.sqrt_nonneg z.im])

lemma ne_top_of_mul_le {s : ℝ} (hs : 0 < s) {X C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ENNReal.ofReal s * X ≤ C) : X ≠ ∞ := by
  intro hX
  rw [hX, ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne'] at h
  exact hC (top_le_iff.1 h)

theorem ev_fin {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧
      (∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) ≠ ∞ ∧
      (∫⁻ z in 𝒟, SNE M n δ' s z) ≠ ∞ ∧
      s * (∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)).toReal ≤ CB.toReal := by
  obtain ⟨CB, hCB, hev⟩ := B_bound hn hnM hδ
  refine ⟨CB, hCB, ?_⟩
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin
  filter_upwards [hpos, hev] with s hs hsB
  have hB := ne_top_of_mul_le hs hCB hsB
  refine ⟨hs, hB, ne_top_of_le_ne_top hB (A_le_B n δ' s), ?_⟩
  have h := ENNReal.toReal_mono hCB hsB
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le] at h

lemma E_ne_top {n : ℤ} (δ' : ZMod M) {s y0 : ℝ} (hy0 : 0 < y0) (hy01 : y0 ≤ 1)
    (hA : (∫⁻ z in 𝒟, SNE M n δ' s z) ≠ ∞)
    (hB : (∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) ≠ ∞) :
    (∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z) ≠ ∞ :=
  ne_top_of_mul_le hy0 (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB⟩) (fd_eCnt_le n δ' s hy0 hy01).2

theorem real_sandwich {n : ℤ} (δ' : ZMod M) {s y0 : ℝ} (hy0 : 0 < y0) (hy01 : y0 ≤ 1)
    (hA : (∫⁻ z in 𝒟, SNE M n δ' s z) ≠ ∞)
    (hE : (∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z) ≠ ∞)
    (hB : (∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) ≠ ∞) :
    |π * (∫⁻ z in 𝒟, SNE M n δ' s z).toReal - y0 * (∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z).toReal|
      ≤ 6 * √y0 * (∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)).toReal := by
  obtain ⟨h1, h2⟩ := fd_eCnt_le n δ' s hy0 hy01
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have h6 : (0 : ℝ) ≤ 6 * √y0 := by positivity
  have hAt := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := π)) hA
  have hEt := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := y0)) hE
  have hBt := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 6 * √y0)) hB
  have t1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hEt, hBt⟩) h1
  have t2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAt, hBt⟩) h2
  rw [ENNReal.toReal_add hEt hBt] at t1
  rw [ENNReal.toReal_add hAt hBt] at t2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hπ, ENNReal.toReal_ofReal hy0.le,
    ENNReal.toReal_ofReal h6] at t1 t2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma scaled_sandwich {s y0 a e b Cb : ℝ} (hs : 0 < s) (h : |π * a - y0 * e| ≤ 6 * √y0 * b)
    (hb : s * b ≤ Cb) : |π * (s * a) - y0 * (s * e)| ≤ 6 * √y0 * Cb := by
  have heq : π * (s * a) - y0 * (s * e) = s * (π * a - y0 * e) := by ring
  rw [heq, abs_mul, abs_of_pos hs]
  calc s * |π * a - y0 * e| ≤ s * (6 * √y0 * b) := mul_le_mul_of_nonneg_left h hs.le
    _ = 6 * √y0 * (s * b) := by ring
    _ ≤ 6 * √y0 * Cb := mul_le_mul_of_nonneg_left hb (by positivity)

theorem tendsto_y0E {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') {y0 : ℝ} (hy0 : 0 < y0) :
    Tendsto (fun s : ℝ => y0 * (s * (∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z).toReal)) (𝓝[>] 0)
      (𝓝 (π * (π * rhoE n / 3))) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp (tendsto_eCnt hn hnM hδ hy0)
  rw [ENNReal.toReal_ofReal (mul_nonneg (div_nonneg (mul_nonneg zero_le_two (rhoE_nonneg n))
    hy0.le) (by positivity))] at h1
  have h2 := h1.const_mul y0
  have hy0ne : y0 ≠ 0 := hy0.ne'
  have heq : y0 * (2 * rhoE n / y0 * (π ^ 2 / 6)) = π * (π * rhoE n / 3) := by
    field_simp
    ring
  rw [heq] at h2
  refine h2.congr' ?_
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin
  filter_upwards [hpos] with s hs
  simp only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le]

lemma exists_y0 {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ y0 : ℝ, 0 < y0 ∧ y0 ≤ 1 ∧ 6 * √y0 * C < ε * π / 2 := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε * π / (12 * (C + 1)) := ⟨_, rfl⟩
  have hC1 : C + 1 ≠ 0 := by positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have hupos : 0 < min 1 t := lt_min one_pos htpos
  have hu1 : min 1 t ≤ 1 := min_le_left _ _
  have hut : min 1 t ≤ t := min_le_right _ _
  refine ⟨(min 1 t) ^ 2, by positivity, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hupos.le]
  have h1 : 6 * min 1 t * C ≤ 6 * t * C := by gcongr
  have h2 : 6 * t * (C + 1) = ε * π / 2 := by
    rw [ht]
    field_simp
    ring
  nlinarith

lemma squeeze_step {F G c ε y0 Cb : ℝ} (h1 : |π * F - G| ≤ 6 * √y0 * Cb)
    (h2 : |G - π * c| < ε * π / 2) (h3 : 6 * √y0 * Cb < ε * π / 2) : |F - c| < ε := by
  have key : |π * F - π * c| < π * ε := by
    calc |π * F - π * c| ≤ |π * F - G| + |G - π * c| := abs_sub_le _ _ _
      _ < π * ε := by linarith
  rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos] at key
  exact lt_of_mul_lt_mul_left key Real.pi_pos.le

/-- `s · A(s) → π ρ(n) / 3` as `s → 0+`. -/
theorem tendsto_sA {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    Tendsto (fun s : ℝ => s * (∫⁻ z in 𝒟, SNE M n δ' s z).toReal) (𝓝[>] 0)
      (𝓝 (π * rhoE n / 3)) := by
  obtain ⟨CB, _, hfin⟩ := ev_fin hn hnM hδ
  have hCb : 0 ≤ CB.toReal := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y0, hy0, hy01, hsmall⟩ := exists_y0 hε hCb
  have hev2 := Metric.tendsto_nhds.1 (tendsto_y0E hn hnM hδ hy0) (ε * π / 2) (by positivity)
  filter_upwards [hfin, hev2] with s hsf hd
  obtain ⟨hs, hB, hA, hsB⟩ := hsf
  rw [Real.dist_eq] at hd ⊢
  have hEf := E_ne_top δ' hy0 hy01 hA hB
  exact squeeze_step (scaled_sandwich hs (real_sandwich δ' hy0 hy01 hA hEf hB) hsB) hd hsmall

/-- `s · LS(s) → π ρ(n) / 3` in `ℂ` as `s → 0+`. -/
theorem tendsto_sLS {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    Tendsto (fun s : ℝ => (s : ℂ) * LS M n δ' s) (𝓝[>] 0) (𝓝 (((π * rhoE n / 3 : ℝ)) : ℂ)) := by
  obtain ⟨CB, _, hfin⟩ := ev_fin hn hnM hδ
  refine ((Complex.continuous_ofReal.tendsto _).comp (tendsto_sA hn hnM hδ)).congr' ?_
  filter_upwards [hfin] with s hsf
  obtain ⟨hs, _, hA, _⟩ := hsf
  rw [Function.comp_apply, LS_eq_toReal hn δ' hs hA, Complex.ofReal_mul]

lemma sum_inv_divisors (n : ℕ) (hn : 0 < n) :
    ∑ h ∈ n.divisors, (1 : ℝ) / h = (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
    ← Nat.sum_div_divisors n (fun d => (d : ℝ)), Finset.sum_div]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hd : h ∣ n := Nat.dvd_of_mem_divisors hh
  have h0 : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hh).ne'
  show (1 : ℝ) / h = ((n / h : ℕ) : ℝ) / n
  rw [Nat.cast_div hd h0]
  field_simp

/-- **P6**: `s · LS(s) → π σ₁(n)/n` as `s → 0+`. -/
theorem p6 : P6Stmt := by
  intro M _ _ n hn hnM δ
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hnM' : Nat.Coprime (n : ℤ).natAbs M := by rwa [Int.natAbs_natCast]
  have hval : π * rhoE (n : ℤ) / 3 = π * (ArithmeticFunction.sigma 1 n : ℝ) / n := by
    rw [rhoE, Int.natAbs_natCast, sum_inv_divisors n hn]
    ring
  rw [← hval]
  exact tendsto_sLS hn' hnM' (Units.isUnit _)

end RamanujanPetersson.EllW2


