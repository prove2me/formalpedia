-- Prove2me | solution 1 for Apery.energy_ineq
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T00:17:42.793962+00:00
-- url     : https://prove2.me/submissions/5842b3f2-1e3d-44fb-9579-9933b8a38ccf

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# Equation (6.9) — the logarithmic-energy inequality for configurations

This file proves the platform theorem `Apery.energy_ineq`: for every configuration of
$h = 37n$ positive pairwise distinct points $t_1,\dots,t_h$,

  `2∑_{i<j} log|tᵢ - tⱼ| - K∑V(tᵢ) + ∑√tᵢ ≤ (λM₀ - I(ρ))K² + 5h + 6h log K`

with $K = K_n = 40n$. The development is a faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, modules
`Apery/EnergyFinal.lean` (the assembly, the regularisation-error bounds, the pair-sum
rearrangement), `Apery/Table/Tail.lean` (the tail bounds (6.8)) and the Table 1 facts of
`Apery/Potential.lean`, `Apery/EnergyAtoms.lean` and `Apery/Measure.lean`. Two inputs are
the imported platform children `Apery.energy_raw` (the raw configuration inequality) and
`Apery.potential_ineq` (Lemma 6.1), with their source-exact statements.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy
import Theorems.Thm_Apery_energy_raw
import Theorems.Thm_Apery_potential_ineq

set_option autoImplicit false

section Port0
/-!
# The configuration inequality (6.9)

From the raw inequality `energy_raw` with `ε = K⁻⁶` (imported child), the potential
inequality `potential_ineq` (Lemma 6.1, imported child), the tail bound (6.8) and the bound
for the regularisation error we obtain `energy_ineq`: for every configuration of `h = 37 n`
positive, pairwise distinct points,

`2∑_{i<j} log|tᵢ - tⱼ| - K∑V(tᵢ) + ∑√tᵢ ≤ (λM₀ - I(ρ))K² + 5h + 6h log K`.

Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/EnergyFinal.lean`,
`Apery/Table/Tail.lean` (the two tail bounds) and the Table 1 facts of
`Apery/Potential.lean` / `Apery/EnergyAtoms.lean` / `Apery/Measure.lean`.
-/

open MeasureTheory Set Real Filter Topology Finset

namespace Apery

/-! ### Facts about Table 1 -/

lemma aρ_lt_bρ : ∀ j ∈ Finset.Icc 1 16, aρ j < bρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma cρ_pos : ∀ j ∈ Finset.Icc 1 16, 0 < cρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [cρ, table1]

lemma rρ_pos (j : Fin 16) : 0 < rρ (j + 1) := by
  have := aρ_lt_bρ (j + 1) (by simp only [Finset.mem_Icc]; omega)
  unfold rρ; linarith

lemma rρ_ge (j : Fin 16) : 1 / 450 ≤ rρ (j + 1) := by
  unfold rρ; fin_cases j <;> norm_num [aρ, bρ, table1]

lemma mρ_bounds (j : Fin 16) : 0 < mρ (j + 1) ∧ mρ (j + 1) < 2 := by
  unfold mρ; fin_cases j <;> norm_num [aρ, bρ, table1]

lemma Sρ_sixteen : Sρ 16 = lam := by
  simp [Sρ, cρ, table1, Finset.sum_Icc_succ_top]
  norm_num

/-! ### The tail bounds (6.8) -/

lemma Uω_of_mem {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) : Uω a b t = Real.log ((b - a) / 4) := by
  simp [Uω, h1, h2]

lemma Uω_of_ge {a b t : ℝ} (hab : a < b) (h : b ≤ t) :
    Uω a b t = Real.log ((t - (a + b) / 2 + Real.sqrt ((t - a) * (t - b))) / 2) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [Uω_of_mem hab.le le_rfl]
    simp only [sub_self, mul_zero, Real.sqrt_zero, add_zero]
    congr 1; ring
  · have : ¬ (a ≤ t ∧ t ≤ b) := fun hh => absurd hh.2 (not_le.mpr h')
    simp only [Uω, this, if_false]
    rw [abs_of_nonneg (by linarith)]

/-- For `t ≥ b`, `Uω a b t ≤ log t`. -/
lemma Uω_le_log {a b t : ℝ} (ha : 0 < a) (hab : a < b) (h : b ≤ t) : Uω a b t ≤ Real.log t := by
  rw [Uω_of_ge hab h]
  have hm : 0 < t - (a + b) / 2 := by linarith
  have hsq : Real.sqrt ((t - a) * (t - b)) ≤ t - (a + b) / 2 :=
    (Real.sqrt_le_left hm.le).mpr (by nlinarith)
  have hs0 := Real.sqrt_nonneg ((t - a) * (t - b))
  exact Real.log_le_log (by linarith) (by linarith)

/-- For `t ≥ 2`, `Uρ t ≤ (37/40) log t` (total mass of `ρ` is `37/40`). -/
lemma Uρ_le_log {t : ℝ} (ht : 2 ≤ t) : Uρ t ≤ 37 / 40 * Real.log t := by
  rw [Uρ]
  have hmem : ∀ j ∈ Finset.Icc 1 16, cρ j * Uω (aρ j) (bρ j) t ≤ cρ j * Real.log t := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ 16 := (Finset.mem_Icc.mp hj).2
    refine mul_le_mul_of_nonneg_left ?_ (by interval_cases j <;> norm_num [cρ, table1])
    exact Uω_le_log (by interval_cases j <;> norm_num [aρ, table1])
      (by interval_cases j <;> norm_num [aρ, bρ, table1])
      ((by interval_cases j <;> norm_num [bρ, table1] : bρ j ≤ 2).trans ht)
  calc ∑ j ∈ Finset.Icc 1 16, cρ j * Uω (aρ j) (bρ j) t
      ≤ ∑ j ∈ Finset.Icc 1 16, cρ j * Real.log t := Finset.sum_le_sum hmem
    _ = (∑ j ∈ Finset.Icc 1 16, cρ j) * Real.log t := by rw [Finset.sum_mul]
    _ = lam * Real.log t := by congr 1; exact Sρ_sixteen
    _ = 37 / 40 * Real.log t := rfl

/-- The lower bound for `V` used in (6.8): `V(t) ≥ 2π√t + log t - 6α (log t + α²/t)`. -/
lemma Vfield_ge_tail {t : ℝ} (ht : 2 ≤ t) :
    2 * Real.pi * Real.sqrt t + Real.log t - 6 * (3 / 40) * (Real.log t + (3 / 40) ^ 2 / t) ≤
      Vfield t := by
  unfold Vfield
  have ht0 : 0 < t := by linarith
  have hcont : Continuous fun u : ℝ => Real.log (t + u ^ 2) :=
    (continuous_const.add (continuous_pow 2)).log (fun u => by simp only [Pi.add_apply]; nlinarith [sq_nonneg u])
  have h1 : Real.log t ≤ ∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2) := by
    have e : ∫ u in (0 : ℝ)..1, Real.log t = Real.log t := by simp
    rw [← e]
    refine intervalIntegral.integral_mono_on zero_le_one (by simp) (hcont.intervalIntegrable _ _) ?_
    intro u _
    exact Real.log_le_log ht0 (by nlinarith)
  have h2 : ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) ≤
      3 / 40 * (Real.log t + (3 / 40) ^ 2 / t) := by
    have e : ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + (3 / 40) ^ 2) =
        3 / 40 * Real.log (t + (3 / 40) ^ 2) := by simp
    have hle : ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2) ≤
        ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + (3 / 40) ^ 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
        (by simp) ?_
      intro u hu
      exact Real.log_le_log (by positivity) (by nlinarith [hu.1, hu.2])
    have hlog : Real.log (t + (3 / 40) ^ 2) ≤ Real.log t + (3 / 40) ^ 2 / t := by
      have e2 : Real.log (t + (3 / 40) ^ 2) = Real.log t + Real.log (1 + (3 / 40) ^ 2 / t) := by
        rw [← Real.log_mul ht0.ne' (by positivity)]
        congr 1; field_simp
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (3 / 40) ^ 2 / t by positivity)
      linarith
    linarith
  linarith

/-! ### The regularisation error -/

lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- The regularisation error at one interval. -/
lemma errj_le {ε t m r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hm : 0 < m ∧ m < 2)
    (hr : 1 / 450 ≤ r) :
    errj ε t m r ≤ Real.sqrt ε * (637 * Real.sqrt t + 1457) := by
  unfold errj
  have hr0 : 0 < r := by linarith
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hεs : ε ≤ Real.sqrt ε := by
    rw [Real.le_sqrt hε.le hε.le]; nlinarith
  have h1 : ε / r ≤ 450 * ε := by rw [div_le_iff₀ hr0]; nlinarith
  have habs : |t - m| ≤ t + 2 := by rw [abs_le]; constructor <;> linarith
  have h2 : ε / r * ((ε + 2 * |t - m|) / r) ≤ 450 ^ 2 * ε * (2 * t + 5) := by
    have : (ε + 2 * |t - m|) / r ≤ 450 * (2 * t + 5) := by
      rw [div_le_iff₀ hr0]; nlinarith
    calc ε / r * ((ε + 2 * |t - m|) / r) ≤ (450 * ε) * (450 * (2 * t + 5)) :=
          mul_le_mul h1 this (by positivity) (by positivity)
      _ = 450 ^ 2 * ε * (2 * t + 5) := by ring
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hs5 : Real.sqrt 5 ≤ 22361 / 10000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have h3 : Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r)) ≤
      450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
    calc Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r))
        ≤ Real.sqrt (450 ^ 2 * ε * (2 * t + 5)) := Real.sqrt_le_sqrt h2
      _ = 450 * Real.sqrt ε * Real.sqrt (2 * t + 5) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
      _ ≤ 450 * Real.sqrt ε * (Real.sqrt (2 * t) + Real.sqrt 5) := by
          apply mul_le_mul_of_nonneg_left (sqrt_add_le' (by positivity) (by norm_num))
          positivity
      _ ≤ 450 * Real.sqrt ε * (14143 / 10000 * Real.sqrt t + 22361 / 10000) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Real.sqrt_mul (by norm_num)]
          have := mul_le_mul_of_nonneg_right hs2 hst
          linarith
  nlinarith

/-- Reindexing `∑_{j ∈ Icc 1 m} f j = ∑_{j < m} f (j + 1)`. -/
lemma sum_Icc_eq_sum_range' (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ j ∈ Finset.range m, f (j + 1) := by
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

/-- The total mass of the sixteen weights. -/
lemma sum_cρ_fin : ∑ j : Fin 16, cρ (j + 1) = lam := by
  rw [← Sρ_sixteen, Sρ, sum_Icc_eq_sum_range', Fin.sum_univ_eq_sum_range (fun j => cρ (j + 1))]

/-- The total regularisation error. -/
lemma Err_le {ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) :
    Err ε t ≤ Real.sqrt ε * (590 * Real.sqrt t + 1348) := by
  unfold Err
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc ∑ j : Fin 16, cρ (j + 1) * errj ε t (mρ (j + 1)) (rρ (j + 1))
      ≤ ∑ j : Fin 16, cρ (j + 1) * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (errj_le hε hε1 ht (mρ_bounds j) (rρ_ge j))
          (cρ_pos _ (by simp only [Finset.mem_Icc]; omega)).le
    _ = lam * (Real.sqrt ε * (637 * Real.sqrt t + 1457)) := by
        rw [← Finset.sum_mul, sum_cρ_fin]
    _ ≤ _ := by
        simp only [lam]
        nlinarith

/-- The tail bound with an extra `c √t`, `0 ≤ c ≤ 1/20`. -/
lemma potential_ineq_tail' {t c : ℝ} (ht : 2 ≤ t) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 20) :
    2 * Uρ t - Vfield t + c * Real.sqrt t ≤ M0 := by
  have ht0 : 0 < t := by linarith
  have h1 := Uρ_le_log ht
  have h2 := Vfield_ge_tail ht
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs2 : (141 / 100 : ℝ) ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hlog : Real.log t ≤ 2 * (Real.sqrt t - 1) := by
    have e : Real.log (Real.sqrt t ^ 2) = 2 * Real.log (Real.sqrt t) := by
      rw [Real.log_pow]; norm_num
    rw [hs] at e
    rw [e]
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hq : (3 / 40 : ℝ) ^ 2 / t ≤ (3 / 40) ^ 2 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hpi := Real.pi_gt_d2
  have hprod : 314 / 100 * Real.sqrt t ≤ Real.pi * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (by norm_num at hpi; linarith) hs0.le
  have hcs : c * Real.sqrt t ≤ 1 / 20 * Real.sqrt t := mul_le_mul_of_nonneg_right hc hs0.le
  unfold M0
  linarith

/-- The pointwise inequality (6.7): `2Uρ(t) - V(t) + (2/K)√t ≤ M₀ + 3/K` for `K ≥ 40`. -/
lemma pointwise_bound {K t : ℝ} (hK : 40 ≤ K) (ht : 0 < t) :
    2 * Uρ t - Vfield t + 2 / K * Real.sqrt t ≤ M0 + 3 / K := by
  have hK0 : 0 < K := by linarith
  rcases le_or_gt t 2 with h | h
  · have h1 := potential_ineq t ht
    have hs : Real.sqrt t ≤ 3 / 2 := by
      rw [Real.sqrt_le_iff]; constructor <;> [norm_num; nlinarith]
    have : 2 / K * Real.sqrt t ≤ 3 / K := by
      rw [show 3 / K = 2 / K * (3 / 2) by ring]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    exact add_le_add h1 this
  · have h1 := potential_ineq_tail' (c := 2 / K) h.le (by positivity)
      (by rw [div_le_iff₀ hK0]; linarith)
    have : (0 : ℝ) ≤ 3 / K := by positivity
    linarith

/-- The double sum over all ordered pairs equals twice the sum over `i < j`. -/
lemma sum_pairs_eq {h : ℕ} (t : Fin h → ℝ) :
    ∑ i, ∑ i', Real.log |t i - t i'| = ∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i| := by
  have hsplit : ∀ i : Fin h, ∑ i', Real.log |t i - t i'| =
      ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| + ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    intro i
    have e1 : (Finset.univ : Finset (Fin h)).filter (fun x => x < i) = Finset.Iio i := by
      ext x; simp
    have e2 : (Finset.univ : Finset (Fin h)).filter (fun x => ¬ x < i) = Finset.Ici i := by
      ext x; simp [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x < i), e1, e2,
      ← Finset.add_sum_Ioi_eq_sum_Ici, sub_self, abs_zero, Real.log_zero, zero_add]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hcomm : ∑ i, ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| =
      ∑ i, ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i' => Finset.Ioi i')]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [abs_sub_comm]
    · intro x y
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [hcomm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_sub_comm]; ring

/-- **(6.9)**, with the constants obtained here. -/
theorem energy_ineq (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Kr n * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (lam * M0 - Irho) * Kr n ^ 2 + 5 * (37 * n) + 6 * (37 * n) * Real.log (Kr n) := by
  have hK : 40 ≤ Kr n := by
    simp only [Kr]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : 0 < Kr n := by linarith
  set K := Kr n with hKdef
  set ε : ℝ := K ^ (-6 : ℤ) with hε_def
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε_def, zpow_neg, inv_le_one_iff₀]
    right; exact one_le_zpow₀ (by linarith) (by norm_num)
  have hsqrtε : Real.sqrt ε = K ^ (-3 : ℤ) := by
    have e : (K ^ (-3 : ℤ)) ^ 2 = ε := by
      rw [hε_def, ← zpow_natCast, ← zpow_mul]; norm_num
    rw [← e, Real.sqrt_sq (by positivity)]
  have hlogε : Real.log ε = -6 * Real.log K := by
    rw [hε_def, Real.log_zpow]; push_cast; ring
  have hraw := energy_raw n hn t hinj hε
  rw [← hKdef, sum_pairs_eq, hlogε] at hraw
  -- bound the error terms
  have hErr : ∀ i, Err ε (t i) ≤ 1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348) := fun i => by
    have := Err_le hε hε1 (ht i)
    rw [hsqrtε, zpow_neg, zpow_ofNat] at this
    rw [one_div]; exact this
  have hK2 : 1 / K ^ 2 ≤ 1 / 1600 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  -- pointwise
  have hpt : ∀ i, 2 * K * (Uρ (t i) + Err ε (t i)) - K * Vfield (t i) + Real.sqrt (t i) ≤
      K * M0 + 5 := by
    intro i
    have h1 := pointwise_bound hK (ht i)
    have h2 := hErr i
    have hs := Real.sqrt_nonneg (t i)
    have e1 : 2 * K * (1 / K ^ 3 * (590 * Real.sqrt (t i) + 1348)) =
        1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) := by field_simp; ring
    have e2 : 1 / K ^ 2 * (1180 * Real.sqrt (t i) + 2696) ≤
        1 / 1600 * (1180 * Real.sqrt (t i) + 2696) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have e3 : K * (2 / K * Real.sqrt (t i)) = 2 * Real.sqrt (t i) := by field_simp
    have e4 : K * (3 / K) = 3 := by field_simp
    have h1' := mul_le_mul_of_nonneg_left h1 hK0.le
    rw [mul_add, mul_add, mul_sub, e3, e4] at h1'
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * K)
    rw [e1] at h2'
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hraw
  have hlam : ((37 * n : ℕ) : ℝ) * (K * M0) = lam * M0 * K ^ 2 := by
    rw [hKdef]; simp only [Kr, lam]; push_cast; ring
  rw [hlam] at hsum
  push_cast at hraw hsum ⊢
  linarith [hraw, hsum]

end Apery
end Port0


open MeasureTheory Polynomial Finset in
/-- The platform target `Apery.energy_ineq`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Apery.Kr n * ∑ i, Apery.Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (Apery.lam * Apery.M0 - Apery.Irho) * Apery.Kr n ^ 2 + 5 * (37 * n) +
        6 * (37 * n) * Real.log (Apery.Kr n) :=
  Apery.energy_ineq n hn t ht hinj
