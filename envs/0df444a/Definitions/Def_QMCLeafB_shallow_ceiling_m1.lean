-- Prove2me | Definitions.Def_QMCLeafB_shallow_ceiling_m1
-- name    : QMCLeafB_shallow_ceiling_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:09:59.5442+00:00
-- url     : https://prove2.me/theorems/b1911fcc-46db-4b71-9776-5ca9ed970463
-- title:
--   QMCLeafB shallow_ceiling_m1
-- statement:
--   # leaf B phase 13 — `shallow-ceiling` (swarm `smw17fqzz`, member m1, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_ClosingBracket
import Definitions.Def_QMCLeafB_brick_verdict_sound
/-
# leaf B phase 13 — `shallow-ceiling` (swarm `smw17fqzz`, member m1, direction d6)

`QMCLeafB.VerdictSound.RunData` carries a *contraction ceiling* `rmax : ℚ` with

    hle    : ∀ k < K*m, ok k = false → (cd k).rho ≤ rmax
    hhalve : (√(rho0R (n·n) rmax))⁻¹ ^ m ≤ 1/2

and the shelf's only explicit halving lemma, `SimLoop.halving_time_explicit`, is stated at depth
**zero** (`rmax = 0`, `m = 4N`).  That ceiling is unusable for a genuine run: see
`del_eq_zero_of_rmax_zero` below — `hle` with `rmax = 0`, `hrho` and `hcheck`
(`del² ≤ rho²·sigmaQ`) force `del k = 0` on every cut round, while the relax-oracle
(`Check_relax_oracle_m4`, `RelaxCut`) reports a *positive* margin over the widened body
`Boundary.relaxBall`.  So the endgame needs the halving lemma at a positive, shallow ceiling.

That is what this file supplies, from shelf pieces only:

* `one_add_pow_mul_one_sub_le` — `(1+u)^m (1 - m·u) ≤ 1` for `0 ≤ u ≤ 1` (Bernoulli, `m` a
  variable exponent);
* `add_pow_mul_one_sub_le` — `(N+ρ)^{2N} (1 - 2ρ) ≤ N^{2N}`: the shrink of the shape matrix at
  normalized depth `ρ ≤ 1/2`;
* `rho0R_ge_of_shallow` — **the shallow-regime lower bound**
  `(1 + 1/N)(1 - 2ρ) ≤ rho0R N ρ`, linear in `ρ` (the shelf has only `rho0R_anti` and the
  depth-zero bound `rho0R_zero_ge_one_add`);
* `ceiling_arith`, `halving_time_shallow` — `8N` rounds halve the contraction factor at the
  shallow ceiling `ρmax = 1/(8N)`;
* `halving_time_of_ceiling` — the same at *every* ceiling `0 ≤ ρmax ≤ 1/(8N)`, in exactly the shape
  of `RunData.hhalve`;
* `one_lt_rho0R_of_ceiling` — the non-degeneracy `1 < rho0R N ρmax` that
  `Boundary.exists_halving_time` and the volume decreasing arguments ask for;
* `shallow_run_budget` — `hhalve` and `hbudget` together at `rmax = 1/(8(n·n))`, `m = 8(n·n)`,
  i.e. the two arithmetic fields of `RunData` at a ceiling that admits positive cut margins;
* `del_eq_zero_of_rmax_zero` — the audit: ceiling zero forces `del = 0`.

No `sorry`, no `axiom`, no `native_decide`; audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.ShallowCeiling

open QMCLeafB.EngineIterates

/-! ## 1.  Bernoulli with a variable exponent -/

/-- **`(1+u)^m (1 - m u) ≤ 1`** for `0 ≤ u ≤ 1`: the upper bound on a power that is the exact
mirror of Bernoulli's lower bound `1 + m u ≤ (1+u)^m`.  Equivalently `(1+u)^m ≤ 1/(1-mu)`, which
is the form the shallow ellipsoid step needs. -/
theorem one_add_pow_mul_one_sub_le (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ 1 := by
  -- Bernoulli in the form `1 - m u ≤ (1-u)^m`
  have hbern : 1 - (m : ℝ) * u ≤ (1 - u) ^ m := by
    have h := one_add_mul_sub_le_pow (a := 1 - u) (by linarith : (-1 : ℝ) ≤ 1 - u) m
    have h' : 1 + (m : ℝ) * ((1 - u) - 1) = 1 - (m : ℝ) * u := by ring
    rwa [h'] at h
  -- `(1+u)(1-u) ≤ 1`, hence `((1+u)(1-u))^m ≤ 1`
  have hprod : ((1 + u) * (1 - u)) ^ m ≤ 1 :=
    pow_le_one₀ (by nlinarith : (0 : ℝ) ≤ (1 + u) * (1 - u))
      (by nlinarith : (1 + u) * (1 - u) ≤ 1)
  have hsplit : (1 + u) ^ m * (1 - u) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact hprod
  have hstep : (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ (1 + u) ^ m * (1 - u) ^ m :=
    mul_le_mul_of_nonneg_left hbern (by positivity)
  linarith

/-- **Shrink at normalized depth `ρ`**: `(N+ρ)^{2N} (1-2ρ) ≤ N^{2N}` for `0 ≤ ρ ≤ 1/2`. -/
theorem add_pow_mul_one_sub_le {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : 2 * ρ ≤ 1) :
    ((N : ℝ) + ρ) ^ (2 * N) * (1 - 2 * ρ) ≤ (N : ℝ) ^ (2 * N) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set u : ℝ := ρ / (N : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hNpos]
    linarith
  have hbase : (N : ℝ) + ρ = (N : ℝ) * (1 + u) := by
    rw [hu]
    field_simp
  have hNu : (N : ℝ) * u = ρ := by
    rw [hu]
    field_simp
  have hm : (((2 * N : ℕ)) : ℝ) * u = 2 * ρ := by
    push_cast
    linarith
  have hkey : (1 + u) ^ (2 * N) * (1 - 2 * ρ) ≤ 1 := by
    have h := one_add_pow_mul_one_sub_le (2 * N) hu0 hu1
    rw [hm] at h
    exact h
  have hpow : ((N : ℝ) + ρ) ^ (2 * N) = (N : ℝ) ^ (2 * N) * (1 + u) ^ (2 * N) := by
    rw [hbase, mul_pow]
  rw [hpow]
  have hNpow : (0 : ℝ) < (N : ℝ) ^ (2 * N) := pow_pos hNpos _
  nlinarith [hkey, hNpow, mul_le_mul_of_nonneg_left hkey hNpow.le]

/-! ## 2.  The one-step contraction factor in the shallow regime -/

/-- **The shallow-regime lower bound on `rho0R`.**  At normalized depth `ρ ∈ [0, 1/2]` the one-step
determinant factor is at least `(1 + 1/N)(1 - 2ρ)`: linear in `ρ`, and matching the shelf's
depth-zero bound `rho0R_zero_ge_one_add` at `ρ = 0`. -/
theorem rho0R_ge_of_shallow {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ2 : 2 * ρ ≤ 1) :
    (1 + ((N : ℝ))⁻¹) * (1 - 2 * ρ) ≤ rho0R N ρ := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set C : ℝ := ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) / ((N : ℝ) - 1) with hCdef
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 - 1 := by nlinarith
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact div_nonneg (mul_nonneg (pow_nonneg (by linarith) N) (by linarith)) hNr.le
  have hNrpos : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have e0 : rho0R N 0 = C / (N : ℝ) ^ (2 * N) := by
    rw [rho0R, hCdef]
    simp only [add_zero]
    rw [div_div]
  have e1 : rho0R N ρ = C / ((N : ℝ) + ρ) ^ (2 * N) := by
    rw [rho0R, hCdef, div_div]
  have h1m : (0 : ℝ) ≤ 1 - 2 * ρ := by linarith
  have hcross : C / (N : ℝ) ^ (2 * N) * (1 - 2 * ρ) ≤ C / ((N : ℝ) + ρ) ^ (2 * N) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hb := add_pow_mul_one_sub_le (N := N) (by omega) hρ hρ2
    nlinarith [hb, hC0, mul_le_mul_of_nonneg_left hb hC0]
  have hbase := QMCLeafB.SimLoop.rho0R_zero_ge_one_add hN
  have hstep : (1 + ((N : ℝ))⁻¹) * (1 - 2 * ρ) ≤ rho0R N 0 * (1 - 2 * ρ) :=
    mul_le_mul_of_nonneg_right hbase h1m
  calc (1 + ((N : ℝ))⁻¹) * (1 - 2 * ρ) ≤ rho0R N 0 * (1 - 2 * ρ) := hstep
    _ = C / (N : ℝ) ^ (2 * N) * (1 - 2 * ρ) := by rw [e0]
    _ ≤ C / ((N : ℝ) + ρ) ^ (2 * N) := hcross
    _ = rho0R N ρ := by rw [e1]

/-! ## 3.  The shallow ceiling `1/(8N)` -/

/-- The ceiling `1/(8N)` is inside the linear bound: `(1+1/N)(1-1/(4N)) ≥ (1+1/(8N))²`. -/
theorem ceiling_arith {N : ℕ} (hN : 2 ≤ N) :
    (1 + ((N : ℝ))⁻¹) * (1 - 2 * ((8 * (N : ℝ))⁻¹)) ≥ (1 + (8 * (N : ℝ))⁻¹) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h8 : (0 : ℝ) < 8 * (N : ℝ) := by linarith
  rw [ge_iff_le]
  field_simp
  nlinarith [hN2, sq_nonneg ((N : ℝ) - 1)]

/-- **`8N` rounds halve the contraction factor at the shallow ceiling `1/(8N)`.** -/
theorem halving_time_shallow {N : ℕ} (hN : 2 ≤ N) :
    (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)))⁻¹ ^ (8 * N) ≤ 1 / 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hρ0 : (0 : ℝ) ≤ (8 * (N : ℝ))⁻¹ := by positivity
  have hρ2 : 2 * ((8 * (N : ℝ))⁻¹) ≤ 1 := by
    rw [show (2 : ℝ) * (8 * (N : ℝ))⁻¹ = (4 * (N : ℝ))⁻¹ by field_simp; ring]
    rw [inv_le_one₀ (by linarith : (0:ℝ) < 4 * (N:ℝ))]
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hlow := rho0R_ge_of_shallow hN hρ0 hρ2
  have hce := ceiling_arith hN
  have hR : (1 + (8 * (N : ℝ))⁻¹) ^ 2 ≤ rho0R N ((8 * (N : ℝ))⁻¹) := le_trans hce hlow
  have hpos : (0 : ℝ) < rho0R N ((8 * (N : ℝ))⁻¹) := rho0R_pos hN hρ0
  have hb0 : (0 : ℝ) ≤ 1 + (8 * (N : ℝ))⁻¹ := by positivity
  have hbase : 1 + (8 * (N : ℝ))⁻¹ ≤ Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)) := by
    rw [Real.le_sqrt hb0 hpos.le]
    exact hR
  have h8N : (8 * (N : ℝ))⁻¹ = (N : ℝ)⁻¹ * (1 / 8) := by
    rw [mul_comm, mul_inv]
    norm_num
  have hbern : 2 ≤ (1 + (8 * (N : ℝ))⁻¹) ^ (8 * N) := by
    have hNpos'' : (0 : ℝ) < 8 * (N : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      linarith
    have hge : (-2 : ℝ) ≤ (8 * (N : ℝ))⁻¹ := by
      have := inv_pos.mpr hNpos''
      linarith
    have h := one_add_mul_le_pow (a := (8 * (N : ℝ))⁻¹) hge (8 * N)
    have h1 : (((8 * N : ℕ)) : ℝ) * (8 * (N : ℝ))⁻¹ = 1 := by
      push_cast
      field_simp
    rw [h1] at h
    rw [h8N]
    norm_num at h
    exact h
  have hmono : (1 + (8 * (N : ℝ))⁻¹) ^ (8 * N)
      ≤ (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹))) ^ (8 * N) :=
    pow_le_pow_left₀ hb0 hbase (8 * N)
  have h2 : 2 ≤ (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹))) ^ (8 * N) := le_trans hbern hmono
  have hspos : (0 : ℝ) < Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)) := Real.sqrt_pos.2 hpos
  have hppos : (0 : ℝ) < (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹))) ^ (8 * N) := pow_pos hspos _
  calc (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)))⁻¹ ^ (8 * N)
      = ((Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹))) ^ (8 * N))⁻¹ := by rw [inv_pow]
    _ ≤ 2⁻¹ := (inv_le_inv₀ hppos (by norm_num : (0:ℝ) < 2)).mpr h2
    _ = 1 / 2 := by norm_num

/-- **The same at every ceiling `0 ≤ ρmax ≤ 1/(8N)`** — the shape of `RunData.hhalve`. -/
theorem halving_time_of_ceiling {N : ℕ} (hN : 2 ≤ N) {ρmax : ℝ} (h0 : 0 ≤ ρmax)
    (hle : ρmax ≤ (8 * (N : ℝ))⁻¹) :
    (Real.sqrt (rho0R N ρmax))⁻¹ ^ (8 * N) ≤ 1 / 2 := by
  have hceil0 : (0 : ℝ) ≤ (8 * (N : ℝ))⁻¹ := by positivity
  have hanti : rho0R N ((8 * (N : ℝ))⁻¹) ≤ rho0R N ρmax := rho0R_anti hN h0 hle
  have hpos0 : (0 : ℝ) < rho0R N ((8 * (N : ℝ))⁻¹) := rho0R_pos hN hceil0
  have hpos1 : (0 : ℝ) < rho0R N ρmax := rho0R_pos hN h0
  have hs : Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)) ≤ Real.sqrt (rho0R N ρmax) :=
    Real.sqrt_le_sqrt hanti
  have hspos : (0 : ℝ) < Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)) := Real.sqrt_pos.2 hpos0
  have hspos1 : (0 : ℝ) < Real.sqrt (rho0R N ρmax) := Real.sqrt_pos.2 hpos1
  have hinv : (Real.sqrt (rho0R N ρmax))⁻¹ ≤ (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)))⁻¹ :=
    (inv_le_inv₀ hspos1 hspos).mpr hs
  calc (Real.sqrt (rho0R N ρmax))⁻¹ ^ (8 * N)
      ≤ (Real.sqrt (rho0R N ((8 * (N : ℝ))⁻¹)))⁻¹ ^ (8 * N) :=
        pow_le_pow_left₀ (by positivity) hinv (8 * N)
    _ ≤ 1 / 2 := halving_time_shallow hN

/-- **Non-degeneracy of the shallow regime**: `1 < rho0R N ρmax` below the ceiling, which is the
hypothesis of `Boundary.exists_halving_time` and of the volume arguments. -/
theorem one_lt_rho0R_of_ceiling {N : ℕ} (hN : 2 ≤ N) {ρmax : ℝ} (h0 : 0 ≤ ρmax)
    (hle : ρmax ≤ (8 * (N : ℝ))⁻¹) : 1 < rho0R N ρmax := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hρ2 : 2 * ρmax ≤ 1 := by
    have h1 : 2 * ρmax ≤ 2 * ((8 * (N : ℝ))⁻¹) := by linarith
    have h2 : 2 * ((8 * (N : ℝ))⁻¹) ≤ 1 := by
      rw [show (2 : ℝ) * (8 * (N : ℝ))⁻¹ = (4 * (N : ℝ))⁻¹ by field_simp; ring]
      rw [inv_le_one₀ (by linarith)]
      linarith
    linarith
  have hlow := rho0R_ge_of_shallow hN h0 hρ2
  have hk : (1 : ℝ) + (2 * (N : ℝ))⁻¹ ≤ (1 + ((N : ℝ))⁻¹) * (1 - 2 * ρmax) := by
    have h4 : 2 * ρmax ≤ (4 * (N : ℝ))⁻¹ := by
      have : (8 * (N : ℝ))⁻¹ * 2 = (4 * (N : ℝ))⁻¹ := by field_simp; ring
      nlinarith [hle, hNpos]
    have hpos' : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    have hm1 : (0 : ℝ) ≤ 1 - 2 * ρmax := by linarith [lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) le_rfl]
    have hstep : (1 + ((N : ℝ))⁻¹) * (1 - (4 * (N : ℝ))⁻¹) ≤ (1 + ((N : ℝ))⁻¹) * (1 - 2 * ρmax) := by
      have : (1 - (4 * (N : ℝ))⁻¹) ≤ 1 - 2 * ρmax := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hkey : (1 : ℝ) + (2 * (N : ℝ))⁻¹ ≤ (1 + ((N : ℝ))⁻¹) * (1 - (4 * (N : ℝ))⁻¹) := by
      field_simp
      nlinarith [hN1]
    exact le_trans hkey hstep
  have : (1 : ℝ) < 1 + (2 * (N : ℝ))⁻¹ := by
    have : (0 : ℝ) < (2 * (N : ℝ))⁻¹ := by positivity
    linarith
  linarith

/-! ## 4.  The two arithmetic fields of `RunData` at the shallow ceiling -/

/-- **`RunData`'s `hhalve` and `hbudget` at the shallow ceiling.**  With
`rmax = 1/(8(n·n))` and `m = 8(n·n)` both arithmetic fields hold at the campaign's own radius
`r = dq/(8(c_A+1))` and starting shape `initShapeOf (n·n) (2n²+2dq²)`, so a run whose recorded
depths are bounded by that ceiling can be assembled with no search at all. -/
theorem shallow_run_budget {n : ℕ} (hn : 2 ≤ n) (M : ℚ) (hM : 0 < M) {δq cAq : ℚ}
    (hδq : 0 < δq) (hcAq : 0 ≤ cAq) :
    (Real.sqrt (rho0R (n * n) ((8 * ((n * n : ℕ) : ℝ))⁻¹)))⁻¹ ^ (8 * (n * n)) ≤ 1 / 2 ∧
      volPot (n * n) (QMCLeafB.Boundary.initShapeOf (n * n) M)
        * (1 / 2) ^ (QMCLeafB.SimLoop.simRounds n
            (volPot (n * n) (QMCLeafB.Boundary.initShapeOf (n * n) M))
            ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) (8 * (n * n)))
        < ((δq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n) := by
  have hn2 : 2 ≤ n * n := by
    have h4 : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
    omega
  have h8 : (0 : ℝ) < 8 * ((n * n : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      have : 1 ≤ n * n := by omega
      exact_mod_cast this
    linarith
  refine ⟨?_, ?_⟩
  · exact halving_time_of_ceiling (N := n * n) hn2 (inv_nonneg.mpr h8.le) (le_refl _)
  · exact QMCLeafB.SimLoop.simRounds_budget (n := n) M hM hδq hcAq (m := 8 * (n * n)) (by omega)

/-! ## 5.  Audit: the ceiling zero forces a zero cut margin -/

/-- **Ceiling zero is unusable.**  In `RunData`, `hle` together with `hrho` pins the recorded depth
to `0`, and then `hcheck` (`del² ≤ rho²·sigmaQ`) pins the recorded margin to `0`.  Since the
relax-oracle reports a *positive* margin over the widened body, the endgame's ceiling must be
positive — hence `runData_hhalve_close`'s depth-zero form is not the endgame's `hhalve`, and
`halving_time_of_ceiling` is what is needed instead. -/
theorem del_eq_zero_of_rmax_zero {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (d : QMCLeafB.VerdictSound.RunData o G t)
    (hrmax : d.rmax = 0) {k : ℕ} (hk : k < d.K * d.m) (hok : d.ok k = false) : d.del k = 0 := by
  have hρ0 : 0 ≤ (d.cd k).rho := d.hrho k hk hok
  have hρle : (d.cd k).rho ≤ 0 := by
    have h := d.hle k hk hok
    rw [hrmax] at h
    exact h
  have hρ : (d.cd k).rho = 0 := le_antisymm hρle hρ0
  have hck := d.hcheck k hk hok
  rw [hρ] at hck
  have hck0 : (d.del k) ^ 2 ≤ 0 := by simpa using hck
  have hsq : (d.del k) * (d.del k) = 0 := by
    rw [← pow_two]
    exact le_antisymm hck0 (sq_nonneg _)
  exact mul_self_eq_zero.mp hsq

end QMCLeafB.ShallowCeiling

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.ShallowCeiling.one_add_pow_mul_one_sub_le
#print axioms QMCLeafB.ShallowCeiling.add_pow_mul_one_sub_le
#print axioms QMCLeafB.ShallowCeiling.rho0R_ge_of_shallow
#print axioms QMCLeafB.ShallowCeiling.ceiling_arith
#print axioms QMCLeafB.ShallowCeiling.halving_time_shallow
#print axioms QMCLeafB.ShallowCeiling.halving_time_of_ceiling
#print axioms QMCLeafB.ShallowCeiling.one_lt_rho0R_of_ceiling
#print axioms QMCLeafB.ShallowCeiling.shallow_run_budget
#print axioms QMCLeafB.ShallowCeiling.del_eq_zero_of_rmax_zero


