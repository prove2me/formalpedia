-- Prove2me | Definitions.Def_QMCLeafB_fa40
-- name    : QMCLeafB_fa40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:31:16.627886+00:00
-- url     : https://prove2.me/theorems/47e2c8f5-7ceb-42ad-84d5-3b322ddf4c50
-- title:
--   QMCLeafB fa40
-- statement:
--   # `Check_fa40_m8` — phase 40, member m8, direction d7 (`assembly40`): the admissibility receipt
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_b1d37
/-
# `Check_fa40_m8` — phase 40, member m8, direction d7 (`assembly40`): the admissibility receipt

**Task of the direction.** Assemble the leaf at the phase-40 family `rmax := 1/(n·n)`.  Before the
assembly, the family itself has to be inhabited — this file is that check, and it FAILS.

The phase-40 charter says:

> `Check_b1d37_m5.runParams_rmax_lt_one` and the `hhalve`/`hbudget` shapes: a LARGER `rmax`
> gives a FASTER contraction, so the halving and budget constraints get easier.

**That is a sign error, and the error is decisive.**  `RunParams.hhalve` reads

    (Real.sqrt (rho0R (n·n) rmax))⁻¹ ^ m ≤ 1/2 ,

and `rho0R N ρ = (N^2-1)^N (N+1) / ((N-1)(N+ρ)^(2N))` is **decreasing** in the depth `ρ`
(`rho0R_antitone` below; `Check_b1d37_m5` says the same in prose and only uses it at `ρ ≥ 1`).
A contraction (`rho0R > 1`) therefore requires `rmax` to be **small**; raising the ceiling makes
`hhalve` strictly harder.  The true threshold is the root of `rho0R N ρ = 1`.

**Verdict of this file, machine-checked.**

* `rho0R_inv_dim_lt_one : rho0R N (1/N) < 1` for every `N ≥ 2` — the factor at the proposed ceiling
  is *below* one, so no number of rounds can halve it.
* `halve_forces_rmax_lt_inv_dim` — **every** `RunParams` (every `m`, every `N ≥ 2`) has
  `rmax < 1/N`.  Consequently
  `no_runParams_rmax_inv_dim : ¬ ∃ P : RunParams G, P.rmax = ((G.n * G.n : Q))⁻¹`
  at every graph with `2 ≤ G.n`: **the phase-40 family does not exist.**
* `reuse_ratio_le_inv_dim` — the closing move's arithmetic, CORRECT as arithmetic:
  `ρ ≤ 1/N ⟹ (1-ρ)/(N+ρ) ≤ 1/N`.  Its equality case is `ρ = 0` (`reuse_eq_iff`), and the ratio
  there is exactly `1/N` (`reuse_ratio_at_supporting`).
* `closing_move_impossible` — for every inhabited `RunParams`, `rmax < 1/N`: the supporting reuse
  supplies the round obligation at depth exactly `1/N`, which **exceeds every admissible ceiling**.
  Since `(1-ρ)/(N+ρ)` is decreasing in `ρ`, this is the best case, so no depth and no admissible
  ceiling make the reuse cut satisfy the leaf's inequality.
* `old_ceiling_quarter` — the closing move is exactly the request to multiply the campaign's
  `rmaxOf N = 1/(4N)` by 4; `§4` refuses it (the true threshold is `≈ 1/(2N)`).

So the factor-4 repair is an arithmetic fact about a ceiling that `RunParams` cannot carry.  The
leaf's `del = 0` route (`Bypass35M6.shallowCut_of_separating`) never reads `rmax` — it needs only
`P.hrmax` — so the residual is unaffected: SEPARATION remains the one obligation, as phase 38 said.

Discipline: `set_option autoImplicit false`; `#print axioms` after every theorem (all exactly
[propext, Classical.choice, Quot.sound]).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Fa40M8

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates

/-! ## 1.  `rho0R` is antitone in the depth

The determinant contraction of the GLS step: numerator independent of `ρ`, denominator
`(N-1)(N+ρ)^(2N)` increasing. -/

theorem rho0R_antitone {N : ℕ} (hN : 2 ≤ N) {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (hle : ρ₁ ≤ ρ₂) :
    rho0R N ρ₂ ≤ rho0R N ρ₁ := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnum : (0 : ℝ) ≤ ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) := by
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1 := by nlinarith [hNR, mul_self_nonneg ((N : ℝ) - 2)]
    exact mul_nonneg (pow_nonneg h4 N) (by linarith)
  have hden0 : (0 : ℝ) < ((N : ℝ) - 1) * ((N : ℝ) + ρ₁) ^ (2 * N) := by
    apply mul_pos (by linarith)
    apply pow_pos
    linarith
  have hden : ((N : ℝ) - 1) * ((N : ℝ) + ρ₁) ^ (2 * N)
      ≤ ((N : ℝ) - 1) * ((N : ℝ) + ρ₂) ^ (2 * N) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  rw [rho0R, rho0R]
  exact div_le_div_of_nonneg_left hnum hden0 hden

#print axioms QMCLeafB.Fa40M8.rho0R_antitone

/-! ## 2.  THE FACTOR AT THE PROPOSED CEILING IS BELOW ONE

`rho0R N (1/N) < 1` for every `N ≥ 2`.  With `s = N^2-1`, `t = N + 1/N`, `u = (3 + 1/N^2)/s` we
have `t^2 = s(1+u)`, so Bernoulli gives

    t^(2N) = s^N (1+u)^N ≥ s^N (1 + N u) = s^(N-1) (N^2-1 + 3N + 1/N) > s^(N-1) (N+1)^2

the last step being `N + 1/N > 2`, and `(N^2-1)^N (N+1) = (N-1) * s^(N-1) (N+1)^2`. -/

theorem rho0R_inv_dim_lt_one {N : ℕ} (hN : 2 ≤ N) :
    rho0R N ((N : ℝ))⁻¹ < 1 := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  set t : ℝ := (N : ℝ) + 1 / (N : ℝ) with ht_def
  set s : ℝ := (N : ℝ) ^ 2 - 1 with hs_def
  have hspos : (0 : ℝ) < s := by
    rw [hs_def]; nlinarith
  set u : ℝ := (3 + 1 / (N : ℝ) ^ 2) / s with hu_def
  have hupos : (0 : ℝ) ≤ u := by
    rw [hu_def]
    apply div_nonneg _ (le_of_lt hspos)
    positivity
  have ht2 : t ^ 2 = s * (1 + u) := by
    rw [ht_def, hs_def, hu_def]
    field_simp
    ring
  have hbern : 1 + (N : ℝ) * u ≤ (1 + u) ^ N := by
    have h := one_add_mul_le_pow (a := u) (by linarith) N
    simpa using h
  have hNu : s * ((N : ℝ) * u) = (N : ℝ) * (3 + 1 / (N : ℝ) ^ 2) := by
    rw [hu_def]
    field_simp
  have hkey : s * (1 + (N : ℝ) * u) = (N : ℝ) ^ 2 - 1 + 3 * (N : ℝ) + 1 / (N : ℝ) := by
    rw [mul_add, mul_one, hNu, hs_def]
    field_simp
    ring
  have hgt : ((N : ℝ) + 1) ^ 2 < s * (1 + (N : ℝ) * u) := by
    rw [hkey]
    have hsq : ((N : ℝ) - 1) ^ 2 / (N : ℝ) = (N : ℝ) - 2 + 1 / (N : ℝ) := by
      field_simp
      ring
    have hpos : (0 : ℝ) < ((N : ℝ) - 1) ^ 2 / (N : ℝ) := by
      apply div_pos (by positivity) hNpos
    nlinarith [hsq, hpos]
  have hstep1 : s ^ (N - 1) * ((N : ℝ) + 1) ^ 2 < s ^ (N - 1) * (s * (1 + (N : ℝ) * u)) :=
    mul_lt_mul_of_pos_left hgt (pow_pos hspos (N - 1))
  have hstep2 : s ^ (N - 1) * (s * (1 + (N : ℝ) * u))
      ≤ s ^ (N - 1) * (s * (1 + u) ^ N) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hspos) (N - 1))
    exact mul_le_mul_of_nonneg_left hbern (le_of_lt hspos)
  have hsplit : s ^ N = s * s ^ (N - 1) :=
    QMCLeafB.B1D37M5.pow_eq_mul_pow_sub_one (by omega : 1 ≤ N)
  have hfin : s ^ (N - 1) * (s * (1 + u) ^ N) = s ^ N * (1 + u) ^ N := by
    rw [hsplit]; ring
  have hmain : s ^ (N - 1) * ((N : ℝ) + 1) ^ 2 < t ^ (2 * N) := by
    rw [show t ^ (2 * N) = (t ^ 2) ^ N from by rw [pow_mul], ht2, mul_pow, ← hfin]
    exact lt_of_lt_of_le hstep1 hstep2
  have hre : ((N : ℝ) - 1) ^ (N - 1) * ((N : ℝ) + 1) ^ (N + 1)
      = s ^ (N - 1) * ((N : ℝ) + 1) ^ 2 := by
    rw [hs_def, show (N : ℝ) ^ 2 - 1 = ((N : ℝ) - 1) * ((N : ℝ) + 1) from by ring, mul_pow,
      show (N + 1 : ℕ) = (N - 1) + 2 from by omega, pow_add]
    ring
  have hpowN : ((N : ℝ) - 1) ^ N = ((N : ℝ) - 1) * ((N : ℝ) - 1) ^ (N - 1) :=
    QMCLeafB.B1D37M5.pow_eq_mul_pow_sub_one (show 1 ≤ N by omega)
  have hpowN1 : ((N : ℝ) + 1) ^ (N + 1) = ((N : ℝ) + 1) ^ N * ((N : ℝ) + 1) := by
    rw [pow_succ]
  have hA : ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1)
      = ((N : ℝ) - 1) * (((N : ℝ) - 1) ^ (N - 1) * ((N : ℝ) + 1) ^ (N + 1)) := by
    rw [show ((N : ℝ) ^ 2 - 1) = ((N : ℝ) - 1) * ((N : ℝ) + 1) from by ring, mul_pow,
      hpowN, hpowN1]
    ring
  have hsum : (N : ℝ) + ((N : ℝ))⁻¹ = t := by
    rw [ht_def, one_div]
  rw [rho0R, div_lt_one (by positivity), hsum, hA, hre]
  exact mul_lt_mul_of_pos_left hmain hN1

#print axioms QMCLeafB.Fa40M8.rho0R_inv_dim_lt_one

/-! ## 3.  `hhalve` forces the ceiling BELOW `1/N` -/

theorem halve_forces_rmax_lt_inv_dim {N : ℕ} (hN : 2 ≤ N) {rmax : ℝ} (h0 : 0 ≤ rmax)
    {m : ℕ} (hh : (Real.sqrt (rho0R N rmax))⁻¹ ^ m ≤ 1 / 2) :
    rmax < ((N : ℝ))⁻¹ := by
  have hpos : 0 < rho0R N rmax := rho0R_pos hN h0
  have hgt : 1 < rho0R N rmax := by
    by_contra hcon
    push Not at hcon
    have hs1 : Real.sqrt (rho0R N rmax) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hcon
    have hspos : 0 < Real.sqrt (rho0R N rmax) := Real.sqrt_pos.mpr hpos
    have hinv : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ := by
      rw [← one_div]
      exact (one_le_div hspos).mpr hs1
    have hge : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ ^ m := one_le_pow₀ hinv
    linarith
  by_contra hcon
  push Not at hcon
  have hmono : rho0R N rmax ≤ rho0R N ((N : ℝ))⁻¹ :=
    rho0R_antitone hN (by positivity : (0 : ℝ) ≤ ((N : ℝ))⁻¹) hcon
  have h1 := rho0R_inv_dim_lt_one hN
  linarith

#print axioms QMCLeafB.Fa40M8.halve_forces_rmax_lt_inv_dim

/-! ## 4.  THE PHASE-40 FAMILY DOES NOT EXIST -/

theorem runParams_rmax_lt_inv_dim {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) :
    (P.rmax : ℝ) < (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have h0 : (0 : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast P.hrmax
  exact halve_forces_rmax_lt_inv_dim hN h0 P.hhalve

#print axioms QMCLeafB.Fa40M8.runParams_rmax_lt_inv_dim

theorem no_runParams_rmax_inv_dim {G : QuantumMaxCutEnergy.Input} (hG : 2 ≤ G.n) :
    ¬ ∃ P : QMCLeafB.FinalStroke.RunParams G, P.rmax = ((G.n * G.n : ℚ))⁻¹ := by
  rintro ⟨P, hP⟩
  have h := runParams_rmax_lt_inv_dim P hG
  have hcast : ((((G.n * G.n : ℚ))⁻¹ : ℚ) : ℝ) = (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
    push_cast
    ring
  have h2 : (P.rmax : ℝ) = (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
    rw [hP, hcast]
  rw [h2] at h
  exact lt_irrefl _ h

#print axioms QMCLeafB.Fa40M8.no_runParams_rmax_inv_dim

/-! ## 5.  The closing move's arithmetic, both directions

The arithmetic itself is right (`reuse_ratio_le_inv_dim`), its equality case is the supporting cut
`ρ = 0`, and the ratio there is exactly `1/N` — which `§4` shows no `RunParams` can carry. -/

/-- **The ratio at the supporting cut is exactly `1/N`** — the phase-40 "exactly". -/
theorem reuse_ratio_at_supporting (N : ℕ) :
    (1 - (0 : ℝ)) / ((N : ℝ) + 0) = ((N : ℝ))⁻¹ := by
  norm_num

#print axioms QMCLeafB.Fa40M8.reuse_ratio_at_supporting

/-- **The closing move's inequality is TRUE**: at `ρ ≤ 1/N` the reuse ratio is at most `1/N`. -/
theorem reuse_ratio_le_inv_dim {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hρ : ρ ≤ ((N : ℝ))⁻¹) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ ((N : ℝ))⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  rw [div_le_iff₀ hden]
  have hexp : ((N : ℝ))⁻¹ * ((N : ℝ) + ρ) = 1 + ρ / (N : ℝ) := by
    field_simp
  rw [hexp]
  have h2 : 0 ≤ ρ + ρ / (N : ℝ) := by positivity
  linarith

#print axioms QMCLeafB.Fa40M8.reuse_ratio_le_inv_dim

/-- **The ratio is STRICTLY below `1/N` at every positive depth** — so the closing move's equality
is the supporting cut and nothing else. -/
theorem reuse_ratio_lt_of_pos {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (h0 : 0 < ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) < ((N : ℝ))⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  rw [div_lt_iff₀ hden]
  have hexp : ((N : ℝ))⁻¹ * ((N : ℝ) + ρ) = 1 + ρ / (N : ℝ) := by
    field_simp
  rw [hexp]
  have h2 : 0 < ρ + ρ / (N : ℝ) := by positivity
  linarith

#print axioms QMCLeafB.Fa40M8.reuse_ratio_lt_of_pos

/-- **The equality case is the supporting cut.** -/
theorem reuse_eq_iff {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (h0 : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) = ((N : ℝ))⁻¹ ↔ ρ = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < ρ := lt_of_le_of_ne h0 (Ne.symm hne)
    have hlt := reuse_ratio_lt_of_pos hN hpos
    linarith
  · intro h
    rw [h]
    exact reuse_ratio_at_supporting N

#print axioms QMCLeafB.Fa40M8.reuse_eq_iff

/-- **THE OBSTRUCTION.**  At EVERY inhabited `RunParams`, the supporting reuse's `1/N` exceeds the
ceiling: `rmax < 1/N`.  Since `(1-ρ)/(N+ρ)` is decreasing in `ρ`, the supporting cut is the best
case — so no admissible ceiling makes the reuse cut satisfy the leaf's inequality. -/
theorem closing_move_impossible {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) :
    (P.rmax : ℝ) < (1 - (0 : ℝ)) / (((G.n * G.n : ℕ)) : ℝ) := by
  have h1 : (1 - (0 : ℝ)) / (((G.n * G.n : ℕ)) : ℝ) = (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
    simpa using reuse_ratio_at_supporting (G.n * G.n)
  rw [h1]
  exact runParams_rmax_lt_inv_dim P hG

#print axioms QMCLeafB.Fa40M8.closing_move_impossible

/-! ## 6.  The factor `4`, bookkept

At the campaign's own ceiling `rmaxOf N = 1/(4N)` the supporting reuse misses the leaf by exactly
`4`; the closing move is precisely the request to multiply the ceiling by `4`. -/

/-- The campaign's constant is exactly one quarter of `1/N`. -/
theorem old_ceiling_quarter (N : ℕ) :
    (1 - (0 : ℝ)) / ((N : ℝ) + 0) = 4 * (1 / (4 * (N : ℝ))) := by
  rw [reuse_ratio_at_supporting]
  field_simp

#print axioms QMCLeafB.Fa40M8.old_ceiling_quarter

/-! ## 7.  The contrast at `n = 2` (`N = 4`), in concrete numbers

The campaign's own ceiling `rmaxOf 4 = 1/16` carries `rho0R > 1` (contraction), the proposed
`1/(n·n) = 1/4` does not.  So the obstruction is not "no ceiling works" — it is that `1/n²` is the
wrong side of the threshold. -/

/-- At the proposed ceiling `1/4` (i.e. `n = 2`) no round count can halve the factor. -/
theorem no_hhalve_at_quarter : ¬ ∃ m : ℕ, (Real.sqrt (rho0R 4 (1 / 4)))⁻¹ ^ m ≤ 1 / 2 := by
  rintro ⟨m, hm⟩
  have h := halve_forces_rmax_lt_inv_dim (N := 4) (by norm_num) (by norm_num : (0:ℝ) ≤ 1/4) hm
  norm_num at h

#print axioms QMCLeafB.Fa40M8.no_hhalve_at_quarter

/-- The campaign's own ceiling `1/16` at `n = 2` DOES contract. -/
theorem rho0R_four_sixteenth_gt_one : 1 < rho0R 4 (1 / 16) := by
  rw [rho0R]
  norm_num

#print axioms QMCLeafB.Fa40M8.rho0R_four_sixteenth_gt_one

/-- The proposed ceiling `1/4` at `n = 2` does not. -/
theorem rho0R_four_quarter_lt_one : rho0R 4 (1 / 4) < 1 := by
  have h : rho0R 4 (((4 : ℝ))⁻¹) < 1 := rho0R_inv_dim_lt_one (N := 4) (by norm_num)
  norm_num at h
  exact h

#print axioms QMCLeafB.Fa40M8.rho0R_four_quarter_lt_one

end QMCLeafB.Fa40M8


