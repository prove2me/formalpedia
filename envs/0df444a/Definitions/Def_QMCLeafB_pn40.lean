-- Prove2me | Definitions.Def_QMCLeafB_pn40
-- name    : QMCLeafB_pn40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:46:55.074586+00:00
-- url     : https://prove2.me/theorems/38f71ab5-0b33-4900-b80b-6af44201a904
-- title:
--   QMCLeafB pn40
-- statement:
--   # `Check_pn40_m5` — phase 40, member m5, direction `params-n2` (d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_unionShallow
/-
# `Check_pn40_m5` — phase 40, member m5, direction `params-n2` (d6)

## The task this file answers

Phase 40's closing move is the parameter change

    rmax := 1/(G.n * G.n)          (`= 1/n²` at the engine's order `N = n·n`),

whose purpose is the ratio inequality of `Check_eq38_m2`: at `ρ ≤ 1/N` the attained supporting
ratio `(1−ρ)/(N+ρ)·√σ'` is below the leaf's allowance `(1/N)·√σ'`.  The claim to be re-discharged
is that `RunParams.hhalve` and `RunParams.hbudget` survive the move.

## The verdict: the move is INADMISSIBLE, and the reason is the engine's own potential

`RunParams.hhalve` is `(√(rho0R N rmax))⁻¹ ^ m ≤ 1/2` with

    rho0R N ρ = ((N²−1)^N · (N+1)) / ((N−1) · (N+ρ)^{2N})        (`det A' = rho0R N ρ · det A`),

and `rho0R N ρ` is ANTI-monotone in `ρ` (`rho0R_anti`): a deeper cut (`ρ → 0`, through the centre)
is the good case, the ceiling `ρ = rmax` is the worst case.  So a LARGER `rmax` makes the halving
inequality HARDER at fixed `m`, not easier — the direction of the phase-40 note is reversed.

The wall is hard, not a matter of the halving time:

* §1 `rho0R_inv_lt_one` — at the closed ceiling `ρ = 1/N`, `rho0R N (1/N) < 1` for EVERY order
  `N ≥ 2` (one Bernoulli step; the identity behind it is `N + 1/N > 2`).  Since the inverse square
  root of a number in `(0,1)` exceeds `1`, `(√(rho0R N (1/N)))⁻¹ ^ m > 1 > 1/2` for every `m : ℕ`:
  **no halving time repairs the ceiling `1/N`.**
* §2 the same at every `ρ ≥ 1/N` (`rho0R_anti`), and the monotonicity in the ceiling displayed.
* §3 `params_rmax_lt_inv` — the field-level consequence: **every** `P : RunParams G` with `2 ≤ G.n`
  has `P.rmax < 1/(n·n)`.  So the phase-40 family is EMPTY: no run exists at the new ceiling.
* §4 the other half, verified rather than assumed: `(1−ρ)/(N+ρ) ≤ 1/N` for every `ρ ≥ 0` (so the
  ratio claim of the closing move is correct) — but §3 says the ceiling it needs is unreachable, and
  §5 sharpens this: at `N·rmax ≤ 1/4` the reuse ratio beats the ceiling at EVERY admissible depth
  `0 ≤ ρ ≤ rmax`.  So the step's own normal can never be the record's normal at the next round, at
  any admissible `RunParams` — the factor-4 miss of `Check_eq38_m2` is not a ceiling artefact.

`RunParams.hbudget` does not mention `rmax` at all (its fields are `K`, `dq`, `cAq`), so it is
neither easier nor harder at the new constant; the obstruction is entirely `hhalve`.  The surviving
leaf interface is therefore the ceiling-free separation route (`Check_rf38_m1.SepStream`,
`solution_of_separating`), at the banked ceiling `rmaxOf (n·n) = 1/(4N)` — where the leaf's demand
`Δ_{A_k}(Cat k, body) ≤ rmax` is *four times tighter*, not looser, so the witness must genuinely be a
supporting direction (`del ≡ 0`), never the step's own cut.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every load-bearing declaration, each exactly
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Pn40M5

open QuantumMaxCutEnergy

/-! ## 1.  The wall: the potential factor at the closed ceiling `1/N` is below `1` -/

/-- **The potential factor at `ρ = 1/n` is `< 1`** (the engine's order is `n` here).

`(n²−1)^N·(n+1)/((n−1)·(n+1/n)^{2N})`, and the comparison against `1` reduces, after writing
`(n+1/n)² = (n²−1)·(1 + (3 + 1/n²)/(n²−1))` and one Bernoulli step, to the identity `(N−1)² > 0`
(with `N` the order and `n` its real value).  Nothing here is numerical: the ceiling `ρ = 1/N` sits
past the wall at every order. -/
theorem rho0R_aux {n : ℝ} (hn : 1 < n) (N : ℕ) (hcast : n = (N : ℝ)) :
    (n ^ 2 - 1) ^ N * (n + 1) / ((n - 1) * (n + n⁻¹) ^ (2 * N)) < 1 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hu : (0 : ℝ) < n ^ 2 - 1 := by nlinarith
  have hy0 : (0 : ℝ) < (3 + (n ^ 2)⁻¹) / (n ^ 2 - 1) := by positivity
  set y : ℝ := (3 + (n ^ 2)⁻¹) / (n ^ 2 - 1) with hy
  have hypos : (0 : ℝ) < y := hy0
  have hfac : (n + n⁻¹) ^ (2 * N) = (n ^ 2 - 1) ^ N * (1 + y) ^ N := by
    rw [pow_mul]
    have hsq : (n + n⁻¹) ^ 2 = (n ^ 2 - 1) * (1 + y) := by
      rw [hy]; field_simp; ring
    rw [hsq, mul_pow]
  have hbern : 1 + (N : ℝ) * y ≤ (1 + y) ^ N := by
    have h := one_add_mul_le_pow (R := ℝ) (a := y) (by linarith) N
    simpa [mul_comm] using h
  -- the arithmetic core: `2·(n+1) < N·(3 + 1/n²)` is `(N−1)² > 0` after clearing `N`
  have hcore : 2 * (n + 1) < (N : ℝ) * (3 + (n ^ 2)⁻¹) := by
    have hsq : (2 : ℝ) * n < n ^ 2 + 1 := by
      nlinarith [mul_pos (sub_pos.mpr hn) (sub_pos.mpr hn)]
    have htwo : (2 : ℝ) < n + n⁻¹ := by
      have h := (div_lt_div_iff_of_pos_right hn0).mpr hsq
      have e1 : 2 * n / n = (2 : ℝ) := by field_simp
      have e2 : (n ^ 2 + 1) / n = n + n⁻¹ := by field_simp
      rw [e1, e2] at h
      exact h
    have hmul : (N : ℝ) * (3 + (n ^ 2)⁻¹) = 3 * n + n⁻¹ := by
      rw [← hcast]; field_simp
    rw [hmul]; linarith
  have harith : n + 1 < (n - 1) * (1 + (N : ℝ) * y) := by
    have hden : (0 : ℝ) < n + 1 := by linarith
    have hkey : (2 : ℝ) < ((N : ℝ) * (3 + (n ^ 2)⁻¹)) / (n + 1) := by
      rw [lt_div_iff₀ hden]; linarith
    have hshape : (n - 1) * (1 + (N : ℝ) * y)
        = (n - 1) + ((N : ℝ) * (3 + (n ^ 2)⁻¹)) / (n + 1) := by
      rw [hy]; field_simp; ring
    rw [hshape]; linarith
  have huN : (0 : ℝ) < (n ^ 2 - 1) ^ N := pow_pos hu N
  have hstep1 : (n ^ 2 - 1) ^ N * (n + 1)
      < (n ^ 2 - 1) ^ N * ((n - 1) * (1 + (N : ℝ) * y)) :=
    mul_lt_mul_of_pos_left harith huN
  have hstep2 : (n ^ 2 - 1) ^ N * ((n - 1) * (1 + (N : ℝ) * y))
      ≤ (n ^ 2 - 1) ^ N * ((n - 1) * (1 + y) ^ N) := by
    have hc : (0 : ℝ) ≤ (n ^ 2 - 1) ^ N * (n - 1) := by
      have : (0 : ℝ) < n - 1 := by linarith
      positivity
    have h := mul_le_mul_of_nonneg_left hbern hc
    nlinarith [h]
  have hfin : (n ^ 2 - 1) ^ N * (n + 1) < (n - 1) * (n + n⁻¹) ^ (2 * N) := by
    rw [hfac]; nlinarith [hstep1, hstep2]
  have hden : (0 : ℝ) < (n - 1) * (n + n⁻¹) ^ (2 * N) := by
    have : (0 : ℝ) < n - 1 := by linarith
    positivity
  rw [div_lt_one hden]
  exact hfin

#print axioms QMCLeafB.Pn40M5.rho0R_aux

/-- **`rho0R N (1/N) < 1` at every order `N ≥ 2`** — the engine's potential factor at the ceiling
`rmax = 1/N` is below one, so `(√·)⁻¹ > 1` and no halving time can make `(√·)⁻¹ ^ m ≤ 1/2`. -/
theorem rho0R_inv_lt_one (N : ℕ) (hN : 2 ≤ N) :
    QMCLeafB.EngineIterates.rho0R N ((N : ℝ)⁻¹) < 1 := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have h : (1 : ℕ) < N := by omega
    exact_mod_cast h
  rw [QMCLeafB.EngineIterates.rho0R]
  exact rho0R_aux hN1 N rfl

#print axioms QMCLeafB.Pn40M5.rho0R_inv_lt_one
/-! ## 2.  Every ceiling past the wall, and the monotonicity in the ceiling -/

/-- **`rho0R N ρ < 1` at every `ρ ≥ 1/N`** — `rho0R_anti` transports §1 up. -/
theorem rho0R_lt_one_of_inv_le {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : (N : ℝ)⁻¹ ≤ ρ) : QMCLeafB.EngineIterates.rho0R N ρ < 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hinv0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := (inv_pos.mpr hNpos).le
  exact lt_of_le_of_lt (QMCLeafB.EngineIterates.rho0R_anti hN hinv0 hρ)
    (rho0R_inv_lt_one N hN)

#print axioms QMCLeafB.Pn40M5.rho0R_lt_one_of_inv_le

/-- **NO halving time repairs a ceiling past `1/N`.**  With `rho0R N ρ ∈ (0,1)` the inverse square
root exceeds `1`, so every `m`-th power exceeds `1/2` — including `m = 0`, where the power is `1`. -/
theorem not_hhalve_of_inv_le {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : (N : ℝ)⁻¹ ≤ ρ) (m : ℕ) :
    ¬ ((Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ ^ m ≤ 1 / 2) := by
  have hlt : QMCLeafB.EngineIterates.rho0R N ρ < 1 := rho0R_lt_one_of_inv_le hN hρ0 hρ
  have hpos : 0 < QMCLeafB.EngineIterates.rho0R N ρ :=
    QMCLeafB.EngineIterates.rho0R_pos hN hρ0
  have hsqrt_lt : Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ) < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hpos.le hlt
  have hsqrt_pos : 0 < Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ) := Real.sqrt_pos.mpr hpos
  have hinv : 1 < (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ := by
    rw [← one_div]
    exact (one_lt_div hsqrt_pos).mpr hsqrt_lt
  intro hle
  have hge : (1 : ℝ) ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · exact (one_lt_pow₀ hinv hm.ne').le
  linarith

#print axioms QMCLeafB.Pn40M5.not_hhalve_of_inv_le

/-- **Enlarging the ceiling makes `hhalve` HARDER, not easier**: at a fixed halving time the
halving expression is monotone in the ceiling (through `rho0R_anti`).  This is the direction the
phase-40 note has reversed. -/
theorem hhalve_antitone_ceiling {N m : ℕ} {rmax rmax' : ℝ} (hN : 2 ≤ N) (h0 : 0 ≤ rmax)
    (h : rmax ≤ rmax') :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax))⁻¹ ^ m
      ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax'))⁻¹ ^ m := by
  have hmono : QMCLeafB.EngineIterates.rho0R N rmax' ≤ QMCLeafB.EngineIterates.rho0R N rmax :=
    QMCLeafB.EngineIterates.rho0R_anti hN h0 h
  have hpos : 0 < QMCLeafB.EngineIterates.rho0R N rmax :=
    QMCLeafB.EngineIterates.rho0R_pos hN h0
  have hpos' : 0 < QMCLeafB.EngineIterates.rho0R N rmax' :=
    QMCLeafB.EngineIterates.rho0R_pos hN (le_trans h0 h)
  have hs : Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax')
      ≤ Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax) :=
    Real.sqrt_le_sqrt hmono
  have hs' : 0 < Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax') := Real.sqrt_pos.mpr hpos'
  have hinv : (Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax))⁻¹
      ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N rmax'))⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr hpos) hs').mpr hs
  exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv m

#print axioms QMCLeafB.Pn40M5.hhalve_antitone_ceiling

/-! ## 3.  The field-level verdict: no `RunParams` at the new ceiling

`RunParams.hhalve` is the only *arithmetic* field that sees `rmax` (besides the sign condition
`hrmax : 0 ≤ rmax`); `RunParams.hbudget` mentions `K`, `dq`, `cAq` and the order, and nothing else.  §1–§2 say the `hhalve` slot is unsatisfiable at `rmax ≥ 1/(n·n)`,
so the phase-40 family is empty. -/

/-- **Every run parameter has its ceiling strictly below `1/(n·n)`.** -/
theorem params_rmax_lt_inv (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    (P.rmax : ℝ) < (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have hNpos : (0 : ℝ) < (((G.n * G.n : ℕ)) : ℝ) := by
    have h : (0 : ℕ) < G.n * G.n := by omega
    exact_mod_cast h
  by_contra hcon
  rw [not_lt] at hcon
  have hrmax0 : (0 : ℝ) ≤ (P.rmax : ℝ) := by
    have := P.hrmax
    exact_mod_cast this
  exact not_hhalve_of_inv_le hN (le_trans (inv_pos.mpr hNpos).le hcon) hcon P.m P.hhalve

#print axioms QMCLeafB.Pn40M5.params_rmax_lt_inv

/-- **The phase-40 family is EMPTY**: there is no `RunParams` whose ceiling is `(n·n)⁻¹`, the
`rmax := 1/n²` of the closing move.  Hence no `RunParts`, no `SelfRec`, no assembly at that
constant. -/
theorem no_params_at_new_ceiling (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n) :
    ¬ ∃ P : QMCLeafB.FinalStroke.RunParams G, ((G.n * G.n : ℚ)⁻¹) ≤ P.rmax := by
  rintro ⟨P, hP⟩
  have hreal : (((G.n * G.n : ℚ)⁻¹ : ℚ) : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast hP
  have hcast : (((G.n * G.n : ℚ)⁻¹ : ℚ) : ℝ) = (((G.n * G.n : ℕ)) : ℝ)⁻¹ := by
    push_cast
    rfl
  rw [hcast] at hreal
  exact absurd hreal (not_le.mpr (params_rmax_lt_inv G hG P))

#print axioms QMCLeafB.Pn40M5.no_params_at_new_ceiling

/-- The same, at the campaign's smallest order `n = 2` (`N = 4`): no `RunParams` has `rmax = 1/4`. -/
theorem no_params_at_inv_four (G : QuantumMaxCutEnergy.Input) (hG : G.n = 2)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    (P.rmax : ℝ) < 1 / 4 := by
  have h := params_rmax_lt_inv G (by omega) P
  have hN : (((G.n * G.n : ℕ)) : ℝ) = 4 := by
    rw [hG]; norm_num
  rw [hN] at h
  norm_num at h ⊢
  exact h

#print axioms QMCLeafB.Pn40M5.no_params_at_inv_four

/-! ## 4.  The closing move's own inequality, verified: `(1−ρ)/(N+ρ) ≤ 1/N`

This half of the phase-40 note is CORRECT — for every `ρ ≥ 0`, not only `ρ ≤ 1/N`.  It is recorded
here so that the refutation of §3 cannot be read as a dispute about the ratio. -/
theorem ratio_le_inv {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  rw [div_le_div_iff₀ hden hNpos]
  nlinarith

#print axioms QMCLeafB.Pn40M5.ratio_le_inv

/-! ## 5.  The reuse direction at the campaign's ceiling: the miss is real at EVERY depth

`Check_eq38_m2.reuse_short_of_leaf` computes the miss at `rmax = rmaxOf N = 1/(4N)`.  The statement
below is the trajectory-free form: whenever the ceiling is at most a quarter of `1/N` — in particular
at the campaign's own `1/(4N)` — the attained ratio `(1−ρ)/(N+ρ)` STRICTLY exceeds the ceiling at
every admissible depth `0 ≤ ρ ≤ rmax`.  So the step's own normal is never the record's normal, and
the factor-4 enlargement of §3 was the only way the reuse lane could have closed. -/
theorem reuse_never_works {N : ℕ} (hN : 2 ≤ N) {rmax ρ : ℝ} (hrmax0 : 0 ≤ rmax)
    (hquarter : (N : ℝ) * rmax ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ rmax) :
    rmax < (1 - ρ) / ((N : ℝ) + ρ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hrmax_le : rmax ≤ 1 / 8 := by
    have h1 : rmax ≤ 1 / (4 * (N : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h2 : 1 / (4 * (N : ℝ)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  rw [lt_div_iff₀ hden]
  have hprod : rmax * ((N : ℝ) + ρ) ≤ 1 / 4 + 1 / 64 := by
    have h1 : rmax * (N : ℝ) ≤ 1 / 4 := by rw [mul_comm]; exact hquarter
    have h2 : rmax * ρ ≤ (1 / 8) * (1 / 8) := by
      have hρ8 : ρ ≤ 1 / 8 := le_trans hρ hrmax_le
      nlinarith
    nlinarith
  have hgap : (1 : ℝ) - ρ ≥ 7 / 8 := by linarith
  linarith

#print axioms QMCLeafB.Pn40M5.reuse_never_works

/-- The same at the campaign's ceiling `rmaxOf N = 1/(4N)` (which `RunParams` uses at every order). -/
theorem reuse_never_works_banked {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / (4 * (N : ℝ))) :
    1 / (4 * (N : ℝ)) < (1 - ρ) / ((N : ℝ) + ρ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  refine reuse_never_works hN (by positivity) ?_ hρ0 hρ
  field_simp
  norm_num

#print axioms QMCLeafB.Pn40M5.reuse_never_works_banked

/-- **The leaf's inequality itself, in the ratio form**: at any ceiling with `N·rmax ≤ 1/4` and any
positive `√σ`, the reuse direction's support value exceeds the leaf's allowance `rmax·√σ`. -/
theorem reuse_short_of_ceiling {N : ℕ} (hN : 2 ≤ N) {rmax ρ s : ℝ} (hrmax0 : 0 ≤ rmax)
    (hquarter : (N : ℝ) * rmax ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ rmax) (hs : 0 < s) :
    rmax * s < ((1 - ρ) / ((N : ℝ) + ρ)) * s :=
  mul_lt_mul_of_pos_right (reuse_never_works hN hrmax0 hquarter hρ0 hρ) hs

#print axioms QMCLeafB.Pn40M5.reuse_short_of_ceiling

/-- **The miss at the central cut is exactly `4`**: `(1−0)/(N+0) = 1/N = 4·(1/(4N))`. -/
theorem central_cut_four (N : ℕ) :
    (1 - 0) / ((N : ℝ) + 0) = 4 * (1 / (4 * (N : ℝ))) := by
  rw [sub_zero, add_zero]
  field_simp

#print axioms QMCLeafB.Pn40M5.central_cut_four

/-! ## 6.  Exact receipts at the campaign's orders (`n = 2` is the smallest live one) -/

/-- At `n = 2` (`N = 4`) the ceiling `1/4 = 1/n²` gives the potential factor `0.7926… < 1`. -/
theorem rho0R_four_quarter :
    QMCLeafB.EngineIterates.rho0R 4 (1 / 4) = 5529600000 / 6975757441 := by
  rw [QMCLeafB.EngineIterates.rho0R]
  norm_num

#print axioms QMCLeafB.Pn40M5.rho0R_four_quarter

/-- … so at `n = 2` the new ceiling is already past the wall. -/
theorem rho0R_four_quarter_lt_one : QMCLeafB.EngineIterates.rho0R 4 (1 / 4) < 1 := by
  have hN : 2 ≤ 4 := by norm_num
  have := rho0R_inv_lt_one 4 hN
  norm_num at this ⊢
  exact this

#print axioms QMCLeafB.Pn40M5.rho0R_four_quarter_lt_one

/-- At the same order, the doubled campaign ceiling `1/(2N) = 1/8` is still past… no: it is still
ADMISSIBLE (`rho0R 4 (1/8) = 1.0065… > 1`).  So the wall at `n = 2` sits strictly between `1/8` and
`1/4`, and the closing move's `1/4` is beyond it while its predecessor's doubled value is not. -/
theorem rho0R_four_eighth_gt_one : 1 < QMCLeafB.EngineIterates.rho0R 4 (1 / 8) := by
  rw [QMCLeafB.EngineIterates.rho0R]
  norm_num

#print axioms QMCLeafB.Pn40M5.rho0R_four_eighth_gt_one

/-! ## 7.  The pointed consequence: the reuse direction fails at EVERY run parameter

`RunParams.hle` allows the recorded depth `ρ = 0` (a cut through the centre), and at `ρ = 0` the
attained ratio is exactly `1/N`, which §3 puts strictly above the ceiling of every run parameter.
So no choice of `RunParams` makes the step's own normal admissible — the closing move's enlargement
was the *only* window, and it is closed. -/

/-- **The reuse direction misses the leaf at the central cut, at every `RunParams`.** -/
theorem reuse_fails_at_every_params (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n)
    (P : QMCLeafB.FinalStroke.RunParams G) {s : ℝ} (hs : 0 < s) :
    (P.rmax : ℝ) * s < ((1 - 0) / ((((G.n * G.n : ℕ)) : ℝ) + 0)) * s := by
  have hlt := params_rmax_lt_inv G hG P
  have hN : (0 : ℝ) < (((G.n * G.n : ℕ)) : ℝ) := by
    have hG0 : (0 : ℕ) < G.n := by omega
    have h : (0 : ℕ) < G.n * G.n := Nat.mul_pos hG0 hG0
    exact_mod_cast h
  have hratio : (P.rmax : ℝ) < (1 - 0) / ((((G.n * G.n : ℕ)) : ℝ) + 0) := by
    rw [sub_zero, add_zero, one_div]
    exact hlt
  exact mul_lt_mul_of_pos_right hratio hs

#print axioms QMCLeafB.Pn40M5.reuse_fails_at_every_params

/-- **No parameter family exists at the new ceiling** — in particular no `RunParts` family, hence no
`SelfRec`, hence no assembly at `rmax := 1/n²`.  The phase-40 closing move cannot be run. -/
theorem no_family_at_new_ceiling (G₀ : QuantumMaxCutEnergy.Input) (hG₀ : 2 ≤ G₀.n) :
    ¬ ∃ P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G,
        ((G₀.n * G₀.n : ℚ)⁻¹) ≤ (P G₀).rmax := by
  rintro ⟨P, hP⟩
  exact no_params_at_new_ceiling G₀ hG₀ ⟨P G₀, hP⟩

#print axioms QMCLeafB.Pn40M5.no_family_at_new_ceiling

/-- The same at `n = 3` (`N = 9`), so the wall is not an artefact of the smallest order. -/
theorem rho0R_nine_ninth_lt_one : QMCLeafB.EngineIterates.rho0R 9 (1 / 9) < 1 := by
  have hN : 2 ≤ 9 := by norm_num
  have := rho0R_inv_lt_one 9 hN
  norm_num at this ⊢
  exact this

#print axioms QMCLeafB.Pn40M5.rho0R_nine_ninth_lt_one

/-! ## 8.  The banked family's parameters, field by field (the digest assembly reads)

The phase-40 move is not needed by the *surviving* interface — `Check_rf38_m1.SepStream` never
mentions `rmax`, and `Check_lm38_m5.recording_iff` only asks the one-sided depth to be at most the
ceiling — so the campaign keeps `UnionShallow.paramsKbc2` at `rmaxOf (n·n) = 1/(4N)`.  These are its
parameter facts, each a theorem, together with §3's placement of the ceiling strictly inside the
admissible band. -/

/-- The ceiling of the banked family is `rmaxOf (n·n) = 1/(4N)`. -/
theorem paramsKbc2_rmax_eq (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).rmax
      = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

#print axioms QMCLeafB.Pn40M5.paramsKbc2_rmax_eq

/-- … the halving time is `mHalve (n·n)`. -/
theorem paramsKbc2_m_eq (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).m = QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

#print axioms QMCLeafB.Pn40M5.paramsKbc2_m_eq

/-- … the tolerance is `dqShallow G`, untouched by the ceiling question. -/
theorem paramsKbc2_dq_eq (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq = QMCLeafB.RundataParams.dqShallow G := rfl

#print axioms QMCLeafB.Pn40M5.paramsKbc2_dq_eq

/-- … and its horizon is positive (the `1 ≤ K·m` slot of `solution_of_separating`). -/
theorem paramsKbc2_horizon (G : QuantumMaxCutEnergy.Input) :
    1 ≤ (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m :=
  QMCLeafB.UnionShallow.one_le_Kbc2_mul G

#print axioms QMCLeafB.Pn40M5.paramsKbc2_horizon

/-- **The banked ceiling is strictly inside the admissible band** (`< 1/(n·n)`), so the run
parameters survive untouched — it is only the phase-40 *new* ceiling that has none. -/
theorem paramsKbc2_rmax_lt_inv (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n) :
    ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax : ℝ) < (((G.n * G.n : ℕ)) : ℝ)⁻¹ :=
  params_rmax_lt_inv G hG _

#print axioms QMCLeafB.Pn40M5.paramsKbc2_rmax_lt_inv

/-- **The factor 4 is exactly the enlargement**: `N · rmaxOf N = 1/4`, so the banked ceiling is a
quarter of the ceiling the closing move needs, and `reuse_never_works`'s hypothesis `N·rmax ≤ 1/4`
is met with EQUALITY at the campaign's own parameters. -/
theorem banked_quarter (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n) :
    (((G.n * G.n : ℕ)) : ℝ) * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax : ℝ) = 1 / 4 := by
  rw [paramsKbc2_rmax_eq]
  unfold QMCLeafB.RundataHalving.rmaxOf
  have hN : (((G.n * G.n : ℕ)) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < G.n * G.n := Nat.mul_pos (by omega) (by omega)
    have h' : (0 : ℕ) < G.n * G.n := h
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h')
  push_cast
  field_simp

#print axioms QMCLeafB.Pn40M5.banked_quarter


