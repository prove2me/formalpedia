-- Prove2me | Definitions.Def_QMCLeafB_hhalveFalse
-- name    : QMCLeafB_hhalveFalse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:20:45.71442+00:00
-- url     : https://prove2.me/theorems/c779e540-8c7c-4121-9647-09c14406654d
-- title:
--   QMCLeafB hhalveFalse
-- statement:
--   # leaf B phase 16 — machine-checked refutation of the global-`m` `hhalve` slot (member m1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_initdq_m1
/-
# leaf B phase 16 — machine-checked refutation of the global-`m` `hhalve` slot (member m1)

Brick 1 (`Check_initdq_m1.lean`) closed the `init`/fuel content at the campaign tolerance, and while
routing it through `FinalReunion.endgame_RSt` it became clear that the **halving slot** of the whole
`RunParams`-splitting stroke family is unsatisfiable as stated.  Every one of

* `QMCLeafB.FinalStroke.endgame_of_parts`, `endgame_of_concrete(_params)`,
  `endgame_of_dominated_rounds`, `endgame_of_dominated_rounds_interior`,
* `QMCLeafB.FinalReunion.endgame_orbit`, `endgame_orbit_sq`, `endgame_RSt`, `endgame_RSt_step`,
* `QMCLeafB.InitDq.endgame_RSt_dq` (my brick-1 copy),

takes `(rmax : ℚ)` and `(m : ℕ)` **global** and asks for

    hhalve : ∀ G : Input, (Real.sqrt (rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2.

`rho0R N ρ = (N²-1)^N (N+1) / ((N-1)(N+ρ)^{2N})` decreases in `N` to `exp(-2ρ)`.  So
`(√(rho0R (G.n²) ρ))⁻¹` increases to `exp(ρ) > 1` (ρ > 0) or to `1` (ρ = 0), while `hhalve` is
equivalent to `rho0R (G.n²) ρ ≥ 2^{2/m} > 1`.  No fixed `(rmax, m)` works; `m` must grow like
`2·G.n²·ln 2`.

This file proves that:

* §1 `rho0R 4 (1/4) = 16588800000/20927272323 < 1` (a step of the `N = 4` check);
* §2 `rho0R N ρ` is antitone in `ρ` and `rho0R N 0 ≤ 1 + 4/N` (`N ≥ 2`);
* §3 `((√R)⁻¹)^m ≤ 1/2` forces `R^m ≥ 4`, while `R ≤ 1 + 1/(4(m+1)²)` forces `R^m < 4`;
* §4 **the general statement** (`hhalve_false`): for **every** `rmax ≥ 0` and every `m ≥ 1` there is
  an input `G` — of order `4(m+1)` — whose inequality fails (`rho0R` does not read the weights, so the
  witness is `⟨4(m+1), 0⟩`);
* §5 the packaged form (`hhalve_unsatisfiable`): no `(rmax, m)` makes the slot hold.

The fix (already in `Check_initdq_m1.lean`): keep `m`, `rmax` per `G`, as
`QMCLeafB.RundataParams.runParamsShallow` does (`m = mOf (G.n²) = 16·G.n⁴`,
`rmax = rmaxOf (G.n²) = 1/(4·G.n²)`), and use `InitDq.endgame_RSt_dq_shallow`.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`; axiom audit
at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.HhalveFalse

open QuantumMaxCutEnergy

local instance instRequestCodingHhalve :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  Elementary bounds -/

theorem exp_quarter_lt_four : Real.exp (1 / 4) < 4 := by
  have h1 : Real.exp (1 : ℝ) = (Real.exp (1 / 4)) ^ 4 := by
    have h := Real.exp_nat_mul (1 / 4 : ℝ) 4
    have harg : ((4 : ℕ) : ℝ) * (1 / 4) = 1 := by norm_num
    rw [harg] at h
    exact h
  have hpos : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  by_contra hcon
  push_neg at hcon
  have hle : (4 : ℝ) ^ 4 ≤ (Real.exp (1 / 4)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hcon 4
  rw [← h1] at hle
  linarith [Real.exp_one_lt_three]

/-- `((√r)⁻¹)^m ≤ 1/2` with `0 < r` forces `(√r)^m ≥ 2`. -/
theorem two_le_pow_of_inv_pow {r : ℝ} (hr : 0 < r) {m : ℕ}
    (h : ((Real.sqrt r)⁻¹) ^ m ≤ 1 / 2) : (2 : ℝ) ≤ (Real.sqrt r) ^ m := by
  have hs0 : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos_of_pos hr
  have hprod : (Real.sqrt r) ^ m * ((Real.sqrt r)⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hs0), one_pow]
  have hp : (0 : ℝ) < (Real.sqrt r) ^ m := pow_pos hs0 m
  nlinarith

/-- **The reciprocal form**: `((√r)⁻¹)^m ≤ 1/2` forces `r^m ≥ 4` when `0 < r`. -/
theorem four_le_pow_of_hhalve {r : ℝ} (hr : 0 < r) {m : ℕ}
    (h : ((Real.sqrt r)⁻¹) ^ m ≤ 1 / 2) : 4 ≤ r ^ m := by
  have h2 := two_le_pow_of_inv_pow hr h
  have hsq : r ^ m = ((Real.sqrt r) ^ m) ^ 2 := by
    have h1 : r ^ m = ((Real.sqrt r) ^ 2) ^ m := by rw [Real.sq_sqrt hr.le]
    rw [h1, ← pow_mul, ← pow_mul, show 2 * m = m * 2 by ring]
  rw [hsq]
  nlinarith

/-- `(1 + x)^m < 4` for `x = 1/(4(m+1)²)`. -/
theorem one_add_pow_lt_four (m : ℕ) (hm : 1 ≤ m) :
    (1 + 1 / (4 * ((m : ℝ) + 1) ^ 2)) ^ m < 4 := by
  set x : ℝ := 1 / (4 * ((m : ℝ) + 1) ^ 2) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hexp : (m : ℝ) * x ≤ 1 / 8 := by
    rw [hx, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1) ^ 2)]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [sq_nonneg ((m : ℝ) + 1)]
  have hstep1 : (1 + x) ^ m ≤ (Real.exp x) ^ m := by
    have h1 : (1 + x) ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    exact pow_le_pow_left₀ (by linarith) h1 m
  have hstep2 : (Real.exp x) ^ m = Real.exp ((m : ℝ) * x) := by
    rw [← Real.exp_nat_mul]
  have hstep3 : Real.exp ((m : ℝ) * x) ≤ Real.exp (1 / 8) := (Real.exp_le_exp).mpr hexp
  have hstep4 : Real.exp (1 / 8) < Real.exp (1 / 4) :=
    (Real.exp_lt_exp).mpr (by norm_num)
  calc (1 + x) ^ m ≤ (Real.exp x) ^ m := hstep1
    _ = Real.exp ((m : ℝ) * x) := hstep2
    _ ≤ Real.exp (1 / 8) := hstep3
    _ < Real.exp (1 / 4) := hstep4
    _ < 4 := exp_quarter_lt_four

/-- **`r^m < 4` from `r ≤ 1 + 1/(4(m+1)²)`.** -/
theorem pow_lt_four_of_le {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m)
    (h : r ≤ 1 + 1 / (4 * ((m : ℝ) + 1) ^ 2)) : r ^ m < 4 := by
  calc r ^ m ≤ (1 + 1 / (4 * ((m : ℝ) + 1) ^ 2)) ^ m :=
        pow_le_pow_left₀ (le_of_lt hr) h m
    _ < 4 := one_add_pow_lt_four m hm

/-! ## 1.  `rho0R` at `(N, ρ) = (4, 1/4)` is below `1` -/

theorem rho0R_four_quarter :
    QMCLeafB.EngineIterates.rho0R 4 ((1 / 4 : ℚ) : ℝ) = 16588800000 / 20927272323 := by
  unfold QMCLeafB.EngineIterates.rho0R
  norm_num

theorem rho0R_four_quarter_lt_one :
    QMCLeafB.EngineIterates.rho0R 4 ((1 / 4 : ℚ) : ℝ) < 1 := by
  rw [rho0R_four_quarter]
  norm_num

/-! ## 2.  `rho0R` is antitone in the ceiling -/

theorem rho0R_antitone_rho {N : ℕ} (hN : 2 ≤ N) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') :
    QMCLeafB.EngineIterates.rho0R N ρ' ≤ QMCLeafB.EngineIterates.rho0R N ρ := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hnum : 0 ≤ ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hC : 0 < ((N : ℝ) - 1) * ((N : ℝ) + ρ) ^ (2 * N) := by
    have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + ρ := by linarith
    positivity
  have hCB : ((N : ℝ) - 1) * ((N : ℝ) + ρ) ^ (2 * N)
      ≤ ((N : ℝ) - 1) * ((N : ℝ) + ρ') ^ (2 * N) := by
    have hp : ((N : ℝ) + ρ) ^ (2 * N) ≤ ((N : ℝ) + ρ') ^ (2 * N) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    exact mul_le_mul_of_nonneg_left hp (by linarith)
  unfold QMCLeafB.EngineIterates.rho0R
  exact div_le_div_of_nonneg_left hnum hC hCB

/-! ## 3.  The general `rho0R N 0 ≤ 1 + 4/N` -/

theorem rho0R_zero_eq (N : ℕ) (hN : 2 ≤ N) :
    QMCLeafB.EngineIterates.rho0R N 0
      = (((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1)) := by
  have hN1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (((N : ℝ)) ^ 2) ^ N = (N : ℝ) ^ (2 * N) := by
    rw [← pow_mul]
  unfold QMCLeafB.EngineIterates.rho0R
  rw [show ((N : ℝ) + 0) = (N : ℝ) by ring, div_pow, hsq, div_mul_div_comm]
  congr 1
  ring

theorem rho0R_zero_le (N : ℕ) (hN : 2 ≤ N) :
    QMCLeafB.EngineIterates.rho0R N 0 ≤ 1 + 4 / (N : ℝ) := by
  rw [rho0R_zero_eq N hN]
  have hN1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNm : (0 : ℝ) < (N : ℝ) - 1 := by
    have h : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    linarith
  have hbase_pos : (0 : ℝ) < ((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2 := by
    have h : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hbase_le : ((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hpow : (((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2) ^ N ≤ 1 := by
    calc (((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2) ^ N ≤ 1 ^ N :=
          pow_le_pow_left₀ hbase_pos.le hbase_le N
      _ = 1 := one_pow N
  have hfac_pos : (0 : ℝ) ≤ ((N : ℝ) + 1) / ((N : ℝ) - 1) := by positivity
  have hfac : ((N : ℝ) + 1) / ((N : ℝ) - 1) ≤ 1 + 4 / (N : ℝ) := by
    rw [div_le_iff₀ hNm]
    have h2 : (1 + 4 / (N : ℝ)) * ((N : ℝ) - 1)
        = ((N : ℝ) - 1) + (4 : ℝ) * ((N : ℝ) - 1) / (N : ℝ) := by
      field_simp
    rw [h2]
    have h1 : (2 : ℝ) ≤ (4 : ℝ) * ((N : ℝ) - 1) / (N : ℝ) := by
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rw [le_div_iff₀ hN1]
      nlinarith
    linarith
  calc (((N : ℝ) ^ 2 - 1) / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
      ≤ 1 * (1 + 4 / (N : ℝ)) := mul_le_mul hpow hfac hfac_pos (by norm_num)
    _ = 1 + 4 / (N : ℝ) := by ring

/-! ## 4.  The refutation -/

/-- The pure algebra: if `0 < R < 1` then `((√R)⁻¹)^m > 1/2`. -/
theorem hhalve_false_abstract {R : ℝ} (h0 : 0 < R) (h1 : R < 1) {m : ℕ} (hm : 1 ≤ m) :
    ¬ ((Real.sqrt R)⁻¹ ^ m ≤ 1 / 2) := by
  have hs0 : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos_of_pos h0
  have hs1 : Real.sqrt R < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    simpa using h1
  have hinv : 1 < (Real.sqrt R)⁻¹ := by
    have h := one_lt_one_div hs0 hs1
    simpa [one_div] using h
  have hgt : 1 < (Real.sqrt R)⁻¹ ^ m := by
    calc (1 : ℝ) < (Real.sqrt R)⁻¹ := hinv
      _ = (Real.sqrt R)⁻¹ ^ 1 := (pow_one _).symm
      _ ≤ (Real.sqrt R)⁻¹ ^ m := pow_le_pow_right₀ hinv.le hm
  exact not_le.mpr (by linarith)

/-- **The `hhalve` slot is unsatisfiable.**  For **every** `rmax ≥ 0` and every `m ≥ 1` there is an
input `G` — one of order `4(m+1)` — at which the inequality fails (`rho0R` does not read the weights,
so the witness is `⟨4(m+1), 0⟩`). -/
theorem hhalve_false (rmax : ℚ) (hrmax : 0 ≤ rmax) {m : ℕ} (hm : 1 ≤ m) :
    ∃ G : QuantumMaxCutEnergy.Input,
      ¬ ((Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax : ℚ) : ℝ)))⁻¹ ^ m
          ≤ 1 / 2) := by
  have hm1 : 1 ≤ m := hm
  refine ⟨⟨4 * (m + 1), fun _ => 0⟩, ?_⟩
  show ¬ ((Real.sqrt (QMCLeafB.EngineIterates.rho0R ((4 * (m + 1)) * (4 * (m + 1)))
    ((rmax : ℚ) : ℝ)))⁻¹ ^ m ≤ 1 / 2)
  have hr0 : (0 : ℝ) ≤ ((rmax : ℚ) : ℝ) := by exact_mod_cast hrmax
  have hN2 : 2 ≤ (4 * (m + 1)) * (4 * (m + 1)) := by nlinarith
  have hNcast : (((4 * (m + 1)) * (4 * (m + 1)) : ℕ) : ℝ) = 16 * ((m : ℝ) + 1) ^ 2 := by
    push_cast
    ring
  set R : ℝ := QMCLeafB.EngineIterates.rho0R ((4 * (m + 1)) * (4 * (m + 1)))
    ((rmax : ℚ) : ℝ) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact QMCLeafB.EngineIterates.rho0R_pos hN2 hr0
  have hle : R ≤ 1 + 1 / (4 * ((m : ℝ) + 1) ^ 2) := by
    have h1 : R ≤ QMCLeafB.EngineIterates.rho0R ((4 * (m + 1)) * (4 * (m + 1))) 0 := by
      rw [hR]
      exact rho0R_antitone_rho (N := (4 * (m + 1)) * (4 * (m + 1))) (ρ := (0 : ℝ))
        (ρ' := ((rmax : ℚ) : ℝ)) hN2 le_rfl hr0
    have h2 := rho0R_zero_le ((4 * (m + 1)) * (4 * (m + 1))) hN2
    have h3 : (1 : ℝ) + 4 / (((4 * (m + 1)) * (4 * (m + 1)) : ℕ) : ℝ)
        = 1 + 1 / (4 * ((m : ℝ) + 1) ^ 2) := by
      rw [hNcast]
      field_simp
      try ring
    linarith
  intro hcon
  have h4 : 4 ≤ R ^ m := four_le_pow_of_hhalve hRpos hcon
  have h5 : R ^ m < 4 := pow_lt_four_of_le hRpos hm1 hle
  exact (not_le.mpr h5) h4

/-- **The packaged statement**: no `(rmax, m)` makes the `hhalve` slot hold. -/
theorem hhalve_unsatisfiable (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm : 1 ≤ m) :
    ¬ (∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax : ℚ) : ℝ)))⁻¹ ^ m ≤ 1 / 2) := by
  intro hall
  obtain ⟨G, hG⟩ := hhalve_false rmax hrmax hm
  exact hG (hall G)

end QMCLeafB.HhalveFalse

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.HhalveFalse.exp_quarter_lt_four
#print axioms QMCLeafB.HhalveFalse.two_le_pow_of_inv_pow
#print axioms QMCLeafB.HhalveFalse.four_le_pow_of_hhalve
#print axioms QMCLeafB.HhalveFalse.one_add_pow_lt_four
#print axioms QMCLeafB.HhalveFalse.rho0R_four_quarter
#print axioms QMCLeafB.HhalveFalse.rho0R_four_quarter_lt_one
#print axioms QMCLeafB.HhalveFalse.rho0R_antitone_rho
#print axioms QMCLeafB.HhalveFalse.rho0R_zero_eq
#print axioms QMCLeafB.HhalveFalse.rho0R_zero_le
#print axioms QMCLeafB.HhalveFalse.pow_lt_four_of_le
#print axioms QMCLeafB.HhalveFalse.hhalve_false_abstract
#print axioms QMCLeafB.HhalveFalse.hhalve_false
#print axioms QMCLeafB.HhalveFalse.hhalve_unsatisfiable


