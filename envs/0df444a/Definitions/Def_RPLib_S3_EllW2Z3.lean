-- Prove2me | Definitions.Def_RPLib_S3_EllW2Z3
-- name    : RPLib_S3_EllW2Z3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:45:41.423682+00:00
-- url     : https://prove2.me/theorems/c3f950c9-5a74-4dbc-849c-60875967e416
-- title:
--   The Eichler-Selberg trace formula in weight two: consequences of the trivial zero-mode bound
-- statement:
--   Consequences of the trivial zero-mode bound.
--
--   * `sum_range_rpow_le`, **`tsum_abs_int_rpow_le`**: `Σ'_{c ∈ ℤ} |c|^(-(1+2s)) ≤ 2 + 1/s`.
--   * `norm_topIs_le_int`, `norm_wtN_topIs_le`, `norm_TsY_le`: `‖T_s(Y)‖ ≤ (1+4n)/Y · Σ'_g zA(s, Y)`.
--   * **`tendsto_TsY`**: for fixed `s > 0`, `T_s(Y) = Σ'_g wtN g · topIs g s Y → 0` as `Y → ∞`.
--   * `wtN_eq_norm`; **`zeroMode_SNH`**: `∫_{-1/2}^{1/2} Σ'_g wtN g R_g(x,y)^(-s-1) dx = Σ'_g zA g` (`y ≥ 1/2`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2Z2

/-!
# S3-ES-Wt2 (O6, file Z3): consequences of the trivial zero-mode bound

* `sum_range_rpow_le`, **`tsum_abs_int_rpow_le`**: `Σ'_{c ∈ ℤ} |c|^(-(1+2s)) ≤ 2 + 1/s`.
* `norm_topIs_le_int`, `norm_wtN_topIs_le`, `norm_TsY_le`: `‖T_s(Y)‖ ≤ (1+4n)/Y · Σ'_g zA(s, Y)`.
* **`tendsto_TsY`**: for fixed `s > 0`, `T_s(Y) = Σ'_g wtN g · topIs g s Y → 0` as `Y → ∞`.
* `wtN_eq_norm`; **`zeroMode_SNH`**: `∫_{-1/2}^{1/2} Σ'_g wtN g R_g(x,y)^(-s-1) dx = Σ'_g zA g` (`y ≥ 1/2`).
-/

open MeasureTheory Set Filter Real Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## The zeta bound -/

lemma sum_range_rpow_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-p) ≤ 1 + 1 / (p - 1) := by
  have hp0 : 0 < p - 1 := by linarith
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have := div_pos one_pos hp0; linarith
  | succ N =>
    rw [Finset.sum_range_succ']
    have hA : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc 1 (1 + (N : ℝ))) := by
      intro x hx z hz hxz
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxz (by linarith)
    have h1 := hA.sum_le_integral
    have h2 : ∫ x in (1 : ℝ)..1 + N, x ^ (-p) = ((1 + (N : ℝ)) ^ (-p + 1) - 1 ^ (-p + 1)) / (-p + 1) :=
      integral_rpow (Or.inr ⟨by linarith, Set.notMem_uIcc_of_lt one_pos (by positivity)⟩)
    have hb : 0 ≤ (1 + (N : ℝ)) ^ (-p + 1) := Real.rpow_nonneg (by positivity) _
    have h3 : ((1 + (N : ℝ)) ^ (-p + 1) - 1 ^ (-p + 1)) / (-p + 1) ≤ 1 / (p - 1) := by
      rw [Real.one_rpow, show -p + 1 = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
      exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hp0.le
    have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-p) =
        ∑ i ∈ Finset.range N, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-p) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    have h0 : (((0 : ℕ) : ℝ) + 1) ^ (-p) = 1 := by simp
    have h4 : ∑ i ∈ Finset.range N, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-p) ≤ 1 / (p - 1) :=
      (h1.trans_eq h2).trans h3
    rw [e, h0]
    linarith [h4]

/-- **`Σ'_{c ∈ ℤ} |c|^(-(1+2s)) ≤ 2 + 1/s`.** -/
lemma tsum_abs_int_rpow_le {s : ℝ} (hs : 0 < s) :
    ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) ≤ 2 + 1 / s := by
  set p := 1 + 2 * s with hpdef
  have hp : 1 < p := by rw [hpdef]; linarith
  have hp1 : p - 1 = 2 * s := by rw [hpdef]; ring
  have hsZ := Real.summable_abs_int_rpow hp
  have hN : Summable fun n : ℕ => |(((n : ℤ)) : ℝ)| ^ (-p) :=
    hsZ.comp_injective Nat.cast_injective
  have hM : Summable fun n : ℕ => |(((-((n : ℤ) + 1)) : ℤ) : ℝ)| ^ (-p) :=
    hsZ.comp_injective fun a b h => by simpa using h
  rw [tsum_of_nat_of_neg_add_one (f := fun c : ℤ => |(c : ℝ)| ^ (-p)) hN hM]
  have e1 : ∀ n : ℕ, |(((-((n : ℤ) + 1)) : ℤ) : ℝ)| ^ (-p) = ((n : ℝ) + 1) ^ (-p) := fun n => by
    congr 1; push_cast; rw [abs_neg, abs_of_pos (by positivity)]
  have hT : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) ≤ 1 + 1 / (p - 1) :=
    Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_range_rpow_le hp)
  have hN' : ∑' n : ℕ, |(((n : ℤ)) : ℝ)| ^ (-p) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) := by
    rw [hN.tsum_eq_zero_add]
    have h0 : |((((0 : ℕ) : ℤ)) : ℝ)| ^ (-p) = 0 := by
      simp only [Nat.cast_zero, Int.cast_zero, abs_zero]
      exact Real.zero_rpow (by linarith)
    rw [h0, zero_add]
    refine tsum_congr fun n => ?_
    congr 1; push_cast; rw [abs_of_pos (by positivity)]
  rw [hN', tsum_congr e1]
  rw [hp1] at hT
  have h2 : (1 : ℝ) / (2 * s) * 2 = 1 / s := by field_simp
  linarith

/-! ## The top edge `T_s(Y) → 0` -/

lemma norm_topIs_le_int {g : S3.Conj.Mat} (hdet : 0 < g.det)
    (hD : (1 : ℤ) ≤ (g 0 0 + g 1 1) ^ 2 - 4 * g.det) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 0 < Y) :
    ‖topIs g s Y‖ ≤ (1 + 4 * (g.det : ℝ)) / Y * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Rc g x Y ^ (-s - 1) := by
  have hcont : Continuous fun x : ℝ => Rc g x Y ^ (-s - 1) := by
    refine Continuous.rpow_const ?_ fun x => Or.inl ?_
    · unfold Rc Pc trR; fun_prop
    · have := Rc_pos hdet (z := (x : ℂ) + Y * Complex.I) (by simpa using hY)
      simpa using this.ne'
  unfold topIs
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun x _ => ?_) ((continuous_const.mul hcont).intervalIntegrable _ _)
  have hz : (0 : ℝ) < ((x : ℂ) + Y * Complex.I).im := by simpa using hY
  have h := norm_VsF_le_N hdet hD hs hz
  simpa using h

lemma norm_wtN_topIs_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 0 < Y)
    (g : S3.Conj.Mat) :
    ‖wtN M n δ' g * topIs g s Y‖ ≤ (1 + 4 * (n : ℝ)) / Y * zA M n δ' s Y g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · obtain ⟨hd, hr, hsp⟩ := h
    have hdet : 0 < g.det := hd ▸ hn
    have hT := norm_topIs_le_int hdet (disc_ge_one hr hsp) hs hY
    rw [hd] at hT
    rw [norm_mul]
    unfold zA
    calc ‖wtN M n δ' g‖ * ‖topIs g s Y‖
        ≤ ‖wtN M n δ' g‖ * ((1 + 4 * (n : ℝ)) / Y *
            ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Rc g x Y ^ (-s - 1)) :=
          mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = _ := by ring
  · rw [wtN_of_not h, zero_mul, norm_zero]
    exact mul_nonneg (div_nonneg (by linarith) hY.le) (zA_nonneg n δ' s Y g)

lemma norm_TsY_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ‖∑' g : S3.Conj.Mat, wtN M n δ' g * topIs g s Y‖ ≤
      (1 + 4 * (n : ℝ)) / Y * ∑' g, zA M n δ' s Y g := by
  have hY0 : 0 < Y := by linarith
  have hb := norm_wtN_topIs_le hn δ' hs.le hY0
  have hS := (summable_zA hn δ' hs hY).mul_left ((1 + 4 * (n : ℝ)) / Y)
  have hN : Summable fun g => ‖wtN M n δ' g * topIs g s Y‖ :=
    Summable.of_nonneg_of_le (fun g => norm_nonneg _) hb hS
  calc _ ≤ ∑' g, ‖wtN M n δ' g * topIs g s Y‖ := norm_tsum_le_tsum_norm hN
    _ ≤ ∑' g, (1 + 4 * (n : ℝ)) / Y * zA M n δ' s Y g := hN.tsum_le_tsum hb hS
    _ = _ := tsum_mul_left

/-- **For fixed `s > 0` the top-edge term `T_s(Y)` tends to `0`.** -/
theorem tendsto_TsY {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun Y : ℝ => ∑' g : S3.Conj.Mat, wtN M n δ' g * topIs g s Y) atTop (𝓝 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Z := ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun c => by positivity
  set C := (1 + 4 * (n : ℝ)) * (KZ M n s 1 * (2 * π ^ 2)) * Z with hCdef
  have hb : ∀ Y : ℝ, Y ≥ 1 → ‖∑' g : S3.Conj.Mat, wtN M n δ' g * topIs g s Y‖ ≤ C / Y := by
    intro Y hY
    have hY2 : 1 / 2 ≤ Y := by linarith
    have h1 := norm_TsY_le hn δ' hs hY2
    have h2 := tsum_zA_le hn δ' hs hY2
    have hK : KZ M n s Y ≤ KZ M n s 1 := by
      unfold KZ
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
      exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by positivity)) one_pos hY
    have hP : (Y ^ 2) ^ (-s) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hY) (by linarith)
    have h3 : KZ M n s Y * (2 * π ^ 2 * (Y ^ 2) ^ (-s)) * Z ≤ KZ M n s 1 * (2 * π ^ 2) * Z := by
      refine mul_le_mul_of_nonneg_right ?_ hZ0
      refine mul_le_mul hK ?_ (by positivity) (KZ_nonneg n hs.le one_pos)
      exact mul_le_of_le_one_right (by positivity) hP
    have hc : 0 ≤ (1 + 4 * (n : ℝ)) / Y := div_nonneg (by linarith) (by linarith)
    calc _ ≤ _ := h1
      _ ≤ (1 + 4 * (n : ℝ)) / Y * (KZ M n s 1 * (2 * π ^ 2) * Z) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hc
      _ = C / Y := by rw [hCdef]; ring
  exact squeeze_zero_norm' (eventually_atTop.2 ⟨1, hb⟩) (tendsto_const_nhds.div_atTop tendsto_id)

/-! ## The zero mode of `SNH` -/

lemma wtN_eq_norm (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) :
    wtN M n δ' g = ((‖wtN M n δ' g‖ : ℝ) : ℂ) := by
  have h : ∃ r : ℝ, 0 ≤ r ∧ wtN M n δ' g = (r : ℂ) := by
    unfold wtN HypPar.wt
    by_cases h1 : IsSP g
    · exact ⟨0, le_rfl, by rw [if_pos h1]; simp⟩
    · rw [if_neg h1]
      by_cases h2 : g.det = n ∧ HypPar.IsRest g
      · exact ⟨(S3.levelCount M δ' g : ℝ) / 2, by positivity, by rw [if_pos h2]; simp⟩
      · exact ⟨0, le_rfl, by rw [if_neg h2]; simp⟩
  obtain ⟨r, hr, e⟩ := h
  rw [e, Complex.norm_real, Real.norm_of_nonneg hr]

/-- **The zero mode of the `R^(-s-1)` series is `Σ'_g zA g`** (`y ≥ 1/2`). -/
theorem zeroMode_SNH {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∑' g : S3.Conj.Mat, wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ) =
      ((∑' g, zA M n δ' s y g : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have hI : ∀ g : S3.Conj.Mat, IntegrableOn (fun x => wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ))
      (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro g
    by_cases hw : wtN M n δ' g = 0
    · simp only [hw, zero_mul]; exact integrableOn_zero
    · have hd : g.det = n := by
        by_contra hd; exact hw (wtN_det n δ' g hd)
      have hdet : 0 < g.det := hd ▸ hn
      have hcont : Continuous fun x : ℝ => wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ) := by
        refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
        refine Continuous.rpow_const ?_ fun x => Or.inl ?_
        · unfold Rc Pc trR; fun_prop
        · have := Rc_pos hdet (z := (x : ℂ) + y * Complex.I) (by simpa using hy0)
          simpa using this.ne'
      exact (hcont.intervalIntegrable _ _).1
  have hnorm : ∀ g : S3.Conj.Mat, ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ‖wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ)‖ = zA M n δ' s y g := by
    intro g
    have e : ∀ x, ‖wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ)‖ =
        ‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1) := fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Rc_nonneg' g x y) _)]
    simp_rw [e]
    rw [integral_const_mul, zA, intervalIntegral.integral_of_le hab]
  have hsum : Summable fun g : S3.Conj.Mat => ∫ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ‖wtN M n δ' g * ((Rc g x y ^ (-s - 1) : ℝ) : ℂ)‖ := by
    simp_rw [hnorm]; exact summable_zA hn δ' hs hy
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  rw [intervalIntegral.integral_of_le hab, ← integral_tsum_of_summable_integral_norm hI hsum,
    Complex.ofReal_tsum]
  refine tsum_congr fun g => ?_
  rw [integral_const_mul, integral_complex_ofReal, zA, intervalIntegral.integral_of_le hab,
    Complex.ofReal_mul, ← wtN_eq_norm]

end RamanujanPetersson.EllW2


