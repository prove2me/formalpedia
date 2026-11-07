-- Prove2me | Definitions.Def_QMCLeafB_aud40
-- name    : QMCLeafB_aud40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:19:55.526184+00:00
-- url     : https://prove2.me/theorems/43d3ec44-24ae-4106-beb6-cfe1d1de72ec
-- title:
--   QMCLeafB aud40
-- statement:
--   # `Check_aud40_m7` — phase 40, member m7, direction d3 (`audit40`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_b1d37
/-
# `Check_aud40_m7` — phase 40, member m7, direction d3 (`audit40`)

**Audit of the phase-40 closing move.**  The charter proposes to enlarge the depth ceiling from
`rmaxOf (n·n) = 1/(4n²)` to `1/n²`, on the grounds that at `ρ ≤ 1/N` the reuse cut's attained ranking
`(1−ρ)/(N+ρ)·√σ'` is below the new allowance `(1/N)·√σ'`, and that "a LARGER `rmax` gives a FASTER
contraction, so `hhalve` and `hbudget` get easier".

**Verdict: the factor is right, the direction of the second claim is BACKWARDS, and the parameter
change is impossible; the two requirements are exactly a factor `2` apart.**

* §1–§2  the boundary value `rho0R N (1/N) < 1` (`N ≥ 2`): at `ρ = 1/N` the engine's one-step
  determinant multiplier does not shrink.  Three Bernoulli bounds on the banked closed form.
* §3–§4  `RunParams.hhalve` forces `1 < rho0R (n·n) rmax` (the banked route of `b1d37`'s
  `rmax_lt_one_of_halve`), and `rho0R` is **anti**-monotone in the depth (`rho0R_anti` — the engine's
  own determinant multiplier).  Hence **`rmax < 1/(n·n)`**: the proposed ceiling is exactly the
  infeasible boundary, and a larger ceiling is a *slower* contraction, not a faster one.
* §5  so `rmax = 1/n²` is uninhabited: `no_runParams_at_one_div_card`.
* §6  the reuse lane needs the OPPOSITE inequality — the ceiling must be `≥ 1/N`, attained by the legal
  depth `ρ = 0` — so it is dead at EVERY admissible ceiling (`reuse_lane_dead`).  Phase 38's factor
  result stands; the ceiling simply cannot be moved to meet it.
* §7  what is ceiling-free, so that nothing has to be re-discharged: `hbudget` does not mention `rmax`
  (`rfl`), and the campaign's `rmaxOf (G.n·G.n)` matches the leaf's `1/(4N)` at the SAME `N = G.n·G.n`.

Consequence for the campaign (recorded, not a Lean claim): the leaf does not need the change.
`SepStream` (`Check_rf38_m1`) is the `del ≡ 0` regime, where `hcheck` is `0 ≤ ρ²σ` and `hle` holds at any
ceiling, so `solution_of_separating` fires at the BANKED `paramsKbc2`.

Discipline: `set_option autoImplicit false`; no sorry/admit/axiom/native_decide/unsafe;
`#print axioms` after every load-bearing theorem, each exactly `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Aud40M7

open QMCLeafB
open QMCLeafB.EngineIterates
open QuantumMaxCutEnergy

/-! ## 1.  The closed form at `ρ = 1/N` -/

/-- `RundataHalving.rho0R_factor`'s right-hand side at `ρ = 1/N`, compared with `1`.  The three
factors are `(1−u)^N`, `(N+1)/(N−1)` and `(1+u)^{-2N}` with `u = 1/N²`; the estimate is
`(1−u)^N·(1+u)^N = (1−u²)^N < 1` (so `(1−u)^N < (1+u)^{-N}`) together with
`(1+u)^{3N} ≥ 1+3/N ≥ (N+1)/(N−1)`. -/
theorem aux_one_div (N : ℕ) (hN : 3 ≤ N) :
    (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
      / (1 + 1 / (N : ℝ) ^ 2) ^ (2 * N) < 1 := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set u : ℝ := 1 / (N : ℝ) ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu, div_lt_one hNsq]; nlinarith
  set a : ℝ := 1 - u with ha
  set b : ℝ := 1 + u with hb
  have ha0 : 0 < a := by rw [ha]; linarith
  have hb1 : 1 ≤ b := by rw [hb]; linarith
  have hbNpos : 0 < b ^ N := by positivity
  have hab : a * b = 1 - u ^ 2 := by rw [ha, hb]; ring
  have hab1 : a * b < 1 := by rw [hab]; nlinarith
  have hlt : a ^ N * b ^ N < 1 := by
    rw [← mul_pow]
    calc (a * b) ^ N < 1 ^ N := pow_lt_pow_left₀ hab1 (by positivity) (by omega : N ≠ 0)
      _ = 1 := one_pow N
  have hb3 : b ^ (3 * N) = b ^ (2 * N) * b ^ N := by
    rw [← pow_add]; congr 1; omega
  have hbern : 1 + ((3 * N : ℕ) : ℝ) * u ≤ b ^ (3 * N) := by
    have h := one_add_mul_le_pow (R := ℝ) (a := u) (by linarith) (3 * N)
    simpa [hb] using h
  have hone : ((3 * N : ℕ) : ℝ) * u = 3 / (N : ℝ) := by
    rw [hu]; push_cast; field_simp
  have hkey : ((N : ℝ) + 1) / ((N : ℝ) - 1) ≤ b ^ (3 * N) := by
    have h3N : 3 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hN0]; linarith
    have hr : ((N : ℝ) + 1) / ((N : ℝ) - 1) ≤ 1 + 3 / (N : ℝ) := by
      rw [div_le_iff₀ hN1]
      have e : ((1 : ℝ) + 3 / (N : ℝ)) * ((N : ℝ) - 1) = (N : ℝ) + 2 - 3 / (N : ℝ) := by
        field_simp; ring
      rw [e]; linarith
    have h1 : 1 + 3 / (N : ℝ) ≤ b ^ (3 * N) := by rw [← hone]; linarith
    linarith
  have hstep : a ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1)) < b ^ (2 * N) := by
    have h1 : a ^ N < 1 / b ^ N := (lt_div_iff₀ hbNpos).mpr hlt
    have h2 : a ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
        < (1 / b ^ N) * (((N : ℝ) + 1) / ((N : ℝ) - 1)) :=
      mul_lt_mul_of_pos_right h1 (by positivity)
    have h3 : (((N : ℝ) + 1) / ((N : ℝ) - 1)) / b ^ N ≤ b ^ (2 * N) := by
      rw [div_le_iff₀ hbNpos, ← hb3]; linarith
    calc a ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
        < (1 / b ^ N) * (((N : ℝ) + 1) / ((N : ℝ) - 1)) := h2
      _ = (((N : ℝ) + 1) / ((N : ℝ) - 1)) / b ^ N := by ring
      _ ≤ b ^ (2 * N) := h3
  rw [div_lt_one (by positivity)]
  exact hstep

#print axioms QMCLeafB.Aud40M7.aux_one_div

/-! ## 2.  The boundary value -/

/-- **`rho0R N (1/N) < 1` for `N ≥ 2`.**  At the ceiling the closing move proposes, the engine's
one-step determinant multiplier is at most `1`: the step does not shrink the ellipsoid there. -/
theorem rho0R_one_div_lt_one (N : ℕ) (hN : 2 ≤ N) :
    rho0R N (1 / (N : ℝ)) < 1 := by
  by_cases h2 : N = 2
  · subst h2
    rw [rho0R]
    norm_num
  · have h3 : 3 ≤ N := by omega
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hρ0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    rw [QMCLeafB.RundataHalving.rho0R_factor N hN hρ0]
    have hdiv : (1 / (N : ℝ)) / (N : ℝ) = 1 / (N : ℝ) ^ 2 := by field_simp
    rw [hdiv]
    exact aux_one_div N h3

#print axioms QMCLeafB.Aud40M7.rho0R_one_div_lt_one

/-- The engine's multiplier is ANTI-monotone in the depth, so every depth above the boundary is
infeasible too. -/
theorem rho0R_lt_one_of_one_div_le {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ}
    (h : 1 / (N : ℝ) ≤ ρ) : rho0R N ρ < 1 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hle : rho0R N ρ ≤ rho0R N (1 / (N : ℝ)) := rho0R_anti hN h0 h
  have hlt := rho0R_one_div_lt_one N hN
  linarith

#print axioms QMCLeafB.Aud40M7.rho0R_lt_one_of_one_div_le

/-! ## 3.  `hhalve` forces the multiplier above `1` -/

/-- **`RunParams.hhalve` needs `rho0R (n·n) rmax > 1`** — the banked observation of `b1d37`'s
`rmax_lt_one_of_halve`, isolated.  `(√f)⁻¹ ^ m ≤ 1/2` is impossible with `f ≤ 1`, since then
`(√f)⁻¹ ≥ 1`. -/
theorem one_lt_rho0R_of_hhalve {N : ℕ} (hN : 2 ≤ N) {rmax : ℝ} (h0 : 0 ≤ rmax) {m : ℕ}
    (hh : (Real.sqrt (rho0R N rmax))⁻¹ ^ m ≤ 1 / 2) : 1 < rho0R N rmax := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < rho0R N rmax := rho0R_pos hN h0
  have hs1 : Real.sqrt (rho0R N rmax) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hcon
  have hspos : 0 < Real.sqrt (rho0R N rmax) := Real.sqrt_pos.mpr hpos
  have hinv : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ := by
    rw [← one_div]
    exact (one_le_div hspos).mpr hs1
  have hge : 1 ≤ (Real.sqrt (rho0R N rmax))⁻¹ ^ m := one_le_pow₀ hinv
  linarith

#print axioms QMCLeafB.Aud40M7.one_lt_rho0R_of_hhalve

/-! ## 4.  THE AUDIT'S MAIN REFUTATION: the ceiling is forced strictly below `1/(n·n)` -/

/-- **Every `RunParams` at `2 ≤ n` has `rmax < 1/(n·n)`.**  Contrapositive of §2 with §3: at
`rmax ≥ 1/(n·n)` the multiplier is `≤ 1`, so `hhalve` fails for every halving time `m`.  In particular
the phase-40 ceiling `rmax = 1/n²` is inadmissible. -/
theorem rmax_lt_one_div_card {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) :
    (P.rmax : ℝ) < 1 / ((G.n * G.n : ℕ) : ℝ) := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have h0 : (0 : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast P.hrmax
  have hgt : 1 < rho0R (G.n * G.n) (P.rmax : ℝ) := one_lt_rho0R_of_hhalve hN h0 P.hhalve
  by_contra hcon
  push Not at hcon
  exact absurd (rho0R_lt_one_of_one_div_le hN hcon) (not_lt.mpr hgt.le)

#print axioms QMCLeafB.Aud40M7.rmax_lt_one_div_card

/-- **The admissible band.**  Every ceiling up to the campaign's `1/(4N)` leaves the one-step
multiplier above `1` (so a sufficiently large halving time exists), while every ceiling from `1/N` up
(chained with `rmax_lt_one_div_card`) leaves it at or below `1`.  The feasible ceilings therefore lie in
`[1/(4N), 1/N)` — a window that excludes the closing move's constant `1/N` but contains the campaign's. -/
theorem feasible_below_shallow {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / (4 * (N : ℝ))) : 1 < rho0R N ρ := by
  have hle : rho0R N (1 / (4 * (N : ℝ))) ≤ rho0R N ρ := rho0R_anti hN h0 hρ
  have hlow := QMCLeafB.RundataHalving.rho0R_shallow_lower N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hpos : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
  linarith

#print axioms QMCLeafB.Aud40M7.feasible_below_shallow

/-- **Corollary, strengthening the banked `b1d37.runParams_rmax_lt_one`** (`rmax < 1`) to
`rmax < 1/4` at every order `n ≥ 2`.  What the phase-37/38 uses of `rho ≠ 1` consume is exactly this
(they only ever needed `rmax < 1`), so they all stand unchanged. -/
theorem rmax_lt_quarter {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) : P.rmax < 1 / 4 := by
  have hlt := rmax_lt_one_div_card P hG
  have hcard : (4 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by
    have h : 2 * 2 ≤ G.n * G.n := Nat.mul_le_mul hG hG
    have h' : ((4 : ℕ) : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hpos : (0 : ℝ) < ((G.n * G.n : ℕ) : ℝ) := by linarith
  have h1 : 1 / ((G.n * G.n : ℕ) : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have hR : (P.rmax : ℝ) < (((1 / 4 : ℚ)) : ℝ) := by push_cast; linarith
  exact Rat.cast_lt.mp hR

#print axioms QMCLeafB.Aud40M7.rmax_lt_quarter

/-! ## 5.  `rmax = 1/n²` is uninhabited -/

/-- **No run has the phase-40 ceiling.**  `rmax = 1/(n·n)` contradicts §4. -/
theorem no_runParams_at_one_div_card (G : QuantumMaxCutEnergy.Input) (hG : 2 ≤ G.n) :
    ¬ ∃ P : QMCLeafB.FinalStroke.RunParams G,
        P.rmax = 1 / ((G.n : ℚ) * (G.n : ℚ)) := by
  rintro ⟨P, hP⟩
  have hlt := rmax_lt_one_div_card P hG
  rw [hP] at hlt
  push_cast at hlt
  linarith

#print axioms QMCLeafB.Aud40M7.no_runParams_at_one_div_card

/-! ## 6.  The reuse lane needs the opposite inequality, at EVERY admissible ceiling

`Eq38M2.supporting_normal_ratio`: after a supporting cut at depth `ρ`, the same normal sees the body at
`((1−ρ)/(N+ρ))·√σ'` one round later, while the leaf's allowance is `rmax·√σ'`.  So the reuse lane needs
`(1−ρ)/(N+ρ) ≤ rmax` at every legal depth.  At `ρ = 0` (`hrho` allows it at every run, `hrmax` puts it
under the ceiling) the ratio is exactly `1/N`: -/

/-- The ceiling must be at least `1/N`, if the reuse lane is to work at every legal depth. -/
theorem reuse_min_ceiling {N : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hall : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ r → (1 - ρ) / ((N : ℝ) + ρ) ≤ r) :
    1 / (N : ℝ) ≤ r := by
  have := hall 0 le_rfl hr
  simpa using this

#print axioms QMCLeafB.Aud40M7.reuse_min_ceiling

/-- **The reuse lane is dead at every admissible ceiling.**  `hhalve` puts `rmax` strictly below `1/N`,
while reuse needs it weakly above; the two demands are a factor `2` apart (the true feasibility edge is
`rho0R N (c/N) = 1` at `c ≈ 1/2`, while reuse needs `c ≥ 1`). -/
theorem reuse_lane_dead {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (hG : 2 ≤ G.n) :
    ¬ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ (P.rmax : ℝ) →
        (1 - ρ) / (((G.n * G.n : ℕ) : ℝ) + ρ) ≤ (P.rmax : ℝ) := by
  intro hall
  have hr0 : (0 : ℝ) ≤ (P.rmax : ℝ) := by exact_mod_cast P.hrmax
  have hmin := reuse_min_ceiling (N := G.n * G.n) hr0 hall
  have hlt := rmax_lt_one_div_card P hG
  linarith

#print axioms QMCLeafB.Aud40M7.reuse_lane_dead

/-! ## 7.  What is ceiling-free (nothing here has to be re-discharged)

`RunParams` mentions `rmax` in exactly two fields, `hrmax` and `hhalve`; `hbudget` does not, so the
volume budget is unchanged by any change of ceiling.  The record's `hcheck` does not mention it either;
only `hle : ρ ≤ rmax` does, and that one moves the easy way. -/

/-- Rebuild the parameter set at another ceiling: only `hrmax`/`hhalve` are re-supplied. -/
def withRmax {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (r : ℚ) (h0 : 0 ≤ r)
    (hh : (Real.sqrt (rho0R (G.n * G.n) ((r : ℚ) : ℝ)))⁻¹ ^ P.m ≤ 1 / 2) :
    QMCLeafB.FinalStroke.RunParams G :=
  { P with rmax := r, hrmax := h0, hhalve := hh }

/-- **The volume budget does not see the ceiling** — `hbudget` is the same term at every `rmax`. -/
theorem withRmax_hbudget {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G) (r : ℚ) (h0 : 0 ≤ r)
    (hh : (Real.sqrt (rho0R (G.n * G.n) ((r : ℚ) : ℝ)))⁻¹ ^ P.m ≤ 1 / 2) :
    (withRmax P r h0 hh).hbudget = P.hbudget := rfl

#print axioms QMCLeafB.Aud40M7.withRmax_hbudget

/-- The round count and the tolerance are untouched by the ceiling as well. -/
theorem withRmax_K {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (r : ℚ) (h0 : 0 ≤ r)
    (hh : (Real.sqrt (rho0R (G.n * G.n) ((r : ℚ) : ℝ)))⁻¹ ^ P.m ≤ 1 / 2) :
    (withRmax P r h0 hh).K = P.K := rfl

theorem withRmax_dq {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (r : ℚ) (h0 : 0 ≤ r)
    (hh : (Real.sqrt (rho0R (G.n * G.n) ((r : ℚ) : ℝ)))⁻¹ ^ P.m ≤ 1 / 2) :
    (withRmax P r h0 hh).dq = P.dq := rfl

#print axioms QMCLeafB.Aud40M7.withRmax_K
#print axioms QMCLeafB.Aud40M7.withRmax_dq

/-- **The campaign's ceiling is the leaf's constant at the same `N`.**  `rmaxOf N = 1/(4N)` and the
leaf's allowance is `1/(4N)·√σ'` with `N = G.n·G.n` — one and the same `N`, so phase 38's factor
statement (`reuse_short_of_leaf`) is about the campaign's own constant. -/
theorem rmaxOf_card (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RundataHalving.rmaxOf (G.n * G.n)
      = 1 / (4 * ((G.n : ℚ) * (G.n : ℚ))) := by
  rw [QMCLeafB.RundataHalving.rmaxOf]
  push_cast
  ring

#print axioms QMCLeafB.Aud40M7.rmaxOf_card

/-- `1/N = 4·(1/(4N))`: the proposed ceiling is exactly FOUR times the campaign's, and the true
feasibility edge sits at `≈ 1/(2N)` — twice the campaign's and half the proposal's. -/
theorem ceiling_ratio (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) / (N : ℝ) = 4 * (1 / (4 * (N : ℝ))) := by
  have h : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  field_simp

#print axioms QMCLeafB.Aud40M7.ceiling_ratio

/-! ## 8.  Numeric receipts at the campaign's smallest case (`n = 2`, `N = 4`) -/

/-- At `N = 4` the proposed ceiling `1/4` gives a multiplier below `1`: no halving time exists. -/
theorem rho0R_four_quarter_lt_one : rho0R 4 (1 / 4 : ℝ) < 1 :=
  rho0R_one_div_lt_one 4 (by norm_num)

#print axioms QMCLeafB.Aud40M7.rho0R_four_quarter_lt_one

/-- At `N = 4` the banked ceiling `rmaxOf 4 = 1/16` gives a multiplier above `1` (banked
`RundataHalving.rho0R_shallow_lower`), so `hhalve` is satisfiable there and nowhere at or above `1/4`. -/
theorem one_lt_rho0R_four_shallow :
    1 < rho0R 4 ((QMCLeafB.RundataHalving.rmaxOf 4 : ℚ) : ℝ) := by
  have h := QMCLeafB.RundataHalving.rho0R_shallow_lower 4 (by norm_num)
  have h16 : ((QMCLeafB.RundataHalving.rmaxOf 4 : ℚ) : ℝ) = 1 / (4 * (4 : ℝ)) := by
    rw [QMCLeafB.RundataHalving.rmaxOf]; norm_num
  rw [h16]
  linarith

#print axioms QMCLeafB.Aud40M7.one_lt_rho0R_four_shallow

/-- **`rmaxOf N = 1/(4N)` is strictly inside the feasible region**: the banked campaign ceiling is
below the boundary at every order. -/
theorem rmaxOf_lt_inv (N : ℕ) (hN : 1 ≤ N) :
    ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) < 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcast : ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) = 1 / (4 * (N : ℝ)) := by
    rw [QMCLeafB.RundataHalving.rmaxOf]; push_cast; ring
  rw [hcast, div_lt_div_iff₀ (by positivity) hN0]
  nlinarith

#print axioms QMCLeafB.Aud40M7.rmaxOf_lt_inv

/-- **THE AUDIT'S ONE-LINE VERDICT.**  At every order `N ≥ 2`: the banked ceiling `rmaxOf N = 1/(4N)`
gives a determinant multiplier above `1` (so `hhalve` is satisfiable there, `rho0R_shallow_lower`),
while the proposed ceiling `1/N` gives one below `1` (so no halving time exists).  The closing move's
parameter change cannot be made; the leaf must close at the banked family. -/
theorem banked_vs_proposed (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) < rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)
      ∧ rho0R N (1 / (N : ℝ)) < 1 := by
  refine ⟨?_, rho0R_one_div_lt_one N hN⟩
  have h := QMCLeafB.RundataHalving.rho0R_shallow_lower N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hcast : ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) = 1 / (4 * (N : ℝ)) := by
    rw [QMCLeafB.RundataHalving.rmaxOf]; push_cast; ring
  rw [hcast]
  have hpos : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
  linarith

#print axioms QMCLeafB.Aud40M7.banked_vs_proposed

/-- The two numeric receipts, side by side: the campaign's ceiling is admissible, the proposal is not. -/
theorem audit_summary :
    rho0R 4 (1 / 4 : ℝ) < 1
      ∧ 1 < rho0R 4 ((QMCLeafB.RundataHalving.rmaxOf 4 : ℚ) : ℝ) :=
  ⟨rho0R_four_quarter_lt_one, one_lt_rho0R_four_shallow⟩

#print axioms QMCLeafB.Aud40M7.audit_summary

end QMCLeafB.Aud40M7


