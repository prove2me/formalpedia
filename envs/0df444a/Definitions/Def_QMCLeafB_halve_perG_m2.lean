-- Prove2me | Definitions.Def_QMCLeafB_halve_perG_m2
-- name    : QMCLeafB_halve_perG_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:07:35.300285+00:00
-- url     : https://prove2.me/theorems/d1c18af5-d13b-4aa4-b72a-a344a793875b
-- title:
--   QMCLeafB halve_perG_m2
-- statement:
--   # leaf B phase 14 — brick `halve-per-G` (swarm `smw1a99tp`, member m2, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_reunion_m7
import Definitions.Def_QMCLeafB_halving
import Definitions.Def_QMCLeafB_roundcount_bound_m2
/-
# leaf B phase 14 — brick `halve-per-G` (swarm `smw1a99tp`, member m2, direction d3)

`RunData.hhalve` is `(√(rho0R N rmax))⁻¹ ^ m ≤ 1/2` at `N = G.n·G.n`.  The shelf proves it at the
*shallow* constants `rmax = 1/(4N)`, `m = 16N²` (`RundataHalving.hhalveOf`), but only at `2 ≤ N`,
and the closing strokes (`QMCLeafB.FinalStroke.endgame_orbit(_sq)`,
`QMCLeafB.FinalReunion.endgame_RSt`) take `rmax : ℚ` and `m : ℕ` as **constants** and ask for

    hhalve : ∀ G, (√(rho0R (G.n·G.n) rmax))⁻¹ ^ m ≤ 1/2.

This file settles that slot in two directions.

§1–§3 **the wrapper.**  The ceiling and the halving time are made per-order,
`rmaxOf (G.n·G.n) = 1/(4·G.n·G.n)` and `mHalve (G.n·G.n) = max 1 (16·(G.n·G.n)²)`, and the halving
inequality is proved for **every** order `N` (`hhalve_perG`).  The two degenerate orders are handled
by hand: `rho0R 0 ρ = -1` and `rho0R 1 ρ = 0`, so `√· = 0` and the left side is `0 ^ mHalve N = 0`
(the exponent is `≥ 1` — which is exactly why `mHalve` carries the `max 1`: at `N = 0` the shallow
time `mOf 0 = 0` would give `x^0 = 1 > 1/2`).  §4 turns that into `RunParams G` for **every** `G`
(`paramsShallow`, `paramsK`), which is what the total function `P : (G : Input) → RunParams G` of
`FinalStroke.endgame_of_parts` needs.  §4b makes the round factor explicit as well: a bit budget
`8√M(c_A+1)/dq ≤ 2^B` gives `K = (1 + n·n·B)·mHalve (n·n)` (`budgetRounds_le_monomial`), so
`RunParts`' guard `P.K * P.m` becomes the monomial `((1+n·n·B)·mHalve (n·n))·mHalve (n·n)`
(`paramsB_K_mul_m`) — the length the fuel program has to produce.  §6 supplies the closing strokes
at those per-order constants: the orbit + interior-bracket combination that the shelf is missing
(`endgame_perG_interior`), its full-bracket twin (`endgame_perG`), and the instantiations at m8's
`InitVerdict.St` and m3's `RoundProgram.RSt` (`endgame_St_interior`, `endgame_RSt_interior`,
`endgame_St_bound_interior`, `endgame_RSt_bound_interior`).

§5 **the constants cannot stay global.**  `hhalve` at a *constant* `rmax > 0` and a *constant* `m`
is **false**, so those slots of the closing strokes are not inhabitable as stated:
`rho0R N rmax = (1−1/N²)^N·(N+1)/(N−1)/(1+rmax/N)^{2N} ≤ (1+4/N)/(1+2·rmax) ≤ 1` once
`N ≥ 9/(2·rmax)`, whence `(√·)⁻¹ ≥ 1` and the `m`-th power is `≥ 1 > 1/2`
(`not_forall_hhalve`, `not_forall_hhalve_input`).  So the per-order wrapper is not cosmetic: the
ceiling and the halving time *have* to be indexed by the order, as they are here.  (`rmax = 0`
escapes §5 but is excluded by the run itself: `hle` then forces `ρ = 0` and `hcheck` forces
`δ = 0`, i.e. no separation — `Check_brick_halving_m5`'s header.)

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.HalvePerG

open QuantumMaxCutEnergy

/-- The request coding of the leaf, as in `Check_brick_verdict_sound` / `Check_final_stroke_m7`. -/
local instance instRequestCodingHalvePerG :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The two degenerate orders

`rho0R N ρ = ((N)²−1)^N·(N+1)/((N−1)·(N+ρ)^{2N})` is the engine's determinant multiplier.  The
shallow halving inequality is proved from that formula under `2 ≤ N`; at `N = 0` and `N = 1` the
formula collapses, and these two values are all the degenerate case needs. -/

/-- **Order `0`.**  `((0)²−1)^0·(0+1)/((0−1)·(0+ρ)^0) = 1/(-1) = -1`. -/
theorem rho0R_zero (ρ : ℝ) : QMCLeafB.EngineIterates.rho0R 0 ρ = -1 := by
  unfold QMCLeafB.EngineIterates.rho0R
  norm_num

/-- **Order `1`.**  The numerator carries `(1²−1)^1 = 0` and the denominator `(1−1)·(1+ρ)² = 0`, and
`0/0 = 0` in `ℝ`. -/
theorem rho0R_one (ρ : ℝ) : QMCLeafB.EngineIterates.rho0R 1 ρ = 0 := by
  unfold QMCLeafB.EngineIterates.rho0R
  norm_num

/-! ## 2.  The per-order constants -/

/-- The shallow ceiling `1/(4N)` is nonnegative at **every** order (at `N = 0` it is `1/0 = 0`),
so `RunParams.hrmax` is available without a lower bound on the order. -/
theorem rmaxOf_nonneg (N : ℕ) : 0 ≤ QMCLeafB.RundataHalving.rmaxOf N := by
  unfold QMCLeafB.RundataHalving.rmaxOf
  rcases eq_or_ne (N : ℚ) 0 with h | h
  · simp [h]
  · have hN : (0 : ℚ) < (N : ℚ) := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have h4 : (0 : ℚ) < 4 * (N : ℚ) := by positivity
    exact (div_pos one_pos h4).le

/-- The ceiling `1/(4N)` cast to `ℝ`.  Valid at every order. -/
theorem rmaxOf_cast (N : ℕ) :
    ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) = 1 / (4 * (N : ℝ)) := by
  unfold QMCLeafB.RundataHalving.rmaxOf
  push_cast
  ring

/-- **The halving time of the per-order wrapper.**  The shallow `16N²`, but at least `1` so that the
degenerate orders `N = 0, 1` — where `mOf` is `0` and a `0`-th power is `1` — give a usable
exponent.  This is the only change the wrapper makes to `RundataHalving.mOf`. -/
def mHalve (N : ℕ) : ℕ := max 1 (QMCLeafB.RundataHalving.mOf N)

theorem one_le_mHalve (N : ℕ) : 1 ≤ mHalve N := le_max_left _ _

/-- At every order `N ≥ 2` the wrapper's halving time *is* the shallow one `16N²`.  This is the
rewrite the fuel wire needs, since `RunParts`' guards are on `K * m`. -/
theorem mHalve_eq_mOf (N : ℕ) (hN : 2 ≤ N) : mHalve N = QMCLeafB.RundataHalving.mOf N := by
  refine max_eq_right ?_
  unfold QMCLeafB.RundataHalving.mOf
  have h1 : 1 ≤ N * N := by
    have h := Nat.mul_le_mul hN hN
    omega
  omega

theorem mHalve_eq (N : ℕ) (hN : 2 ≤ N) : mHalve N = 16 * (N * N) := by
  rw [mHalve_eq_mOf N hN]
  rfl

/-! ## 3.  The halving inequality at every order -/

/-- **`hhalve` at the shallow ceiling `1/(4N)`, for *every* order `N`.**

`N ≥ 2` is `RundataHalving.hhalveOf`, transported from `mOf N` to `mHalve N` by monotonicity of
`x ↦ x^k` on `[0,1]` (`(√rho0R N rmaxOf N)⁻¹ ∈ [0,1]` because `rho0R N rmaxOf N ≥ 1 + 1/(8N) > 1`,
`RundataHalving.rho0R_shallow_lower`).  `N ≤ 1` is by hand: `rho0R 0 ρ = -1` and `rho0R 1 ρ = 0`
have `√ = 0`, so the left side is `0`, raised to the positive exponent `mHalve N`. -/
theorem hhalve_perG (N : ℕ) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N
      ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)))⁻¹ ^ mHalve N ≤ 1 / 2 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- the degenerate orders: both sides are `0`
    interval_cases N
    · rw [rho0R_zero]
      have h0 : Real.sqrt (-1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
      rw [h0, inv_zero, zero_pow (by have := one_le_mHalve 0; omega)]
      norm_num
    · rw [rho0R_one]
      have h0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
      rw [h0, inv_zero, zero_pow (by have := one_le_mHalve 1; omega)]
      norm_num
  · -- `N ≥ 2`: the shallow halving inequality, exponent enlarged
    have hb := QMCLeafB.RundataHalving.hhalveOf N hN
    rw [rmaxOf_cast] at hb
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h0 : (0 : ℕ) < N := by omega
      exact_mod_cast h0
    have hlow := QMCLeafB.RundataHalving.rho0R_shallow_lower N hN
    have hx1 : (1 : ℝ) ≤ QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))) := by
      have h8 : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
      linarith
    have hs : (1 : ℝ) ≤
        Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))) := by
      have h := Real.sqrt_le_sqrt hx1
      simpa using h
    have hb0 : (0 : ℝ) ≤ (Real.sqrt
        (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hb1 : (Real.sqrt
        (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))))⁻¹ ≤ 1 := by
      have hp : (0 : ℝ) < Real.sqrt
          (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))) :=
        lt_of_lt_of_le one_pos hs
      rw [← one_div, div_le_one hp]
      exact hs
    have hmono : QMCLeafB.RundataHalving.mOf N ≤ mHalve N := by
      rw [mHalve_eq_mOf N hN]
    have hfin := le_trans (pow_le_pow_of_le_one hb0 hb1 hmono) hb
    rwa [rmaxOf_cast]

/-! ## 3b.  The halving time can be *linear*

`16N²` is far from what the shallow ceiling needs.  The same three lines give a **linear** halving
time: `rho0R N (1/(4N)) ≥ 1 + 1/(8N)` (`RundataHalving.rho0R_shallow_lower`), so
`(√·)⁻¹ ≤ (1 + 1/(8N))^{-1/2}`, and Bernoulli at `u = 1/(8N)` with `k = 8N` gives
`(1+u)^{8N} ≥ 1 + 8Nu = 2`, i.e. `(1+u)^{-8N} ≤ 1/2`.  Hence `m = 16N + 1` already halves the
potential — a factor `N` below `mOf N = 16N²`, and it makes the fuel count `K·m` a much smaller
polynomial.  (`mHalve` above is kept as it is because `Check_fuelwire_m4` is built on it; this is the
sharper alternative, and `mHalveLin_le_mHalve` transfers any statement to the older time.) -/

/-- The linear halving time `16N + 1` (also `≥ 1` at every order, without a `max`). -/
def mHalveLin (N : ℕ) : ℕ := 16 * N + 1

theorem one_le_mHalveLin (N : ℕ) : 1 ≤ mHalveLin N := by
  unfold mHalveLin
  omega

theorem mHalveLin_le_mHalve (N : ℕ) (hN : 2 ≤ N) : mHalveLin N ≤ mHalve N := by
  have hupper : 16 * (N * N) ≤ mHalve N := by
    unfold mHalve QMCLeafB.RundataHalving.mOf
    exact le_max_right _ _
  have hstep : 16 * N + 1 ≤ 16 * (N * N) := by
    have h4 : N + 1 ≤ N * N := by
      have ha : N + 1 ≤ 2 * N := by omega
      have hb : 2 * N ≤ N * N := by
        have h := Nat.mul_le_mul_left N hN
        rwa [Nat.mul_comm N 2] at h
      exact le_trans ha hb
    calc 16 * N + 1 ≤ 16 * (N + 1) := by
          have hN1 : 16 * (N + 1) = 16 * N + 16 := by ring
          omega
      _ ≤ 16 * (N * N) := Nat.mul_le_mul_left 16 h4
  unfold mHalveLin
  exact le_trans hstep hupper

/-- **The halving inequality with a linear halving time.**  `(√(rho0R N (1/(4N))))⁻¹ ^ (16N+1) ≤ 1/2`
— Bernoulli, no analysis. -/
theorem hhalve_perG_lin (N : ℕ) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N
      ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)))⁻¹ ^ mHalveLin N ≤ 1 / 2 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · rw [rho0R_zero]
      have h0 : Real.sqrt (-1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
      rw [h0, inv_zero, zero_pow (by unfold mHalveLin; omega)]
      norm_num
    · rw [rho0R_one]
      have h0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
      rw [h0, inv_zero, zero_pow (by unfold mHalveLin; omega)]
      norm_num
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h0 : (0 : ℕ) < N := by omega
      exact_mod_cast h0
    rw [rmaxOf_cast]
    have hlow := QMCLeafB.RundataHalving.rho0R_shallow_lower N hN
    have hbase : (1 + 1 / (8 * (N : ℝ)))
        ≤ QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))) := hlow
    have hpos : (0 : ℝ) < 1 + 1 / (8 * (N : ℝ)) := by positivity
    have hxpos : (0 : ℝ) < QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ))) := by linarith
    -- `(√(rho0R))⁻¹ ≤ (√(1+1/(8N)))⁻¹ ≤ 1`
    have hle : (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))))⁻¹
        ≤ (Real.sqrt (1 + 1 / (8 * (N : ℝ))))⁻¹ := by
      rw [inv_le_inv₀ (Real.sqrt_pos.mpr hxpos) (Real.sqrt_pos.mpr hpos)]
      exact Real.sqrt_le_sqrt hbase
    have hone : (Real.sqrt (1 + 1 / (8 * (N : ℝ))))⁻¹ ≤ 1 := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (1 + 1 / (8 * (N : ℝ))) := by
        have h2 : (1 : ℝ) ≤ 1 + 1 / (8 * (N : ℝ)) := by
          have h3 : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
          linarith
        calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
          _ ≤ Real.sqrt (1 + 1 / (8 * (N : ℝ))) := Real.sqrt_le_sqrt h2
      rw [← one_div, div_le_one (lt_of_lt_of_le one_pos h1)]
      exact h1
    have hb0 : (0 : ℝ) ≤
        (Real.sqrt (QMCLeafB.EngineIterates.rho0R N (1 / (4 * (N : ℝ)))))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    refine le_trans (pow_le_pow_left₀ hb0 hle (mHalveLin N)) ?_
    refine le_trans (pow_le_pow_of_le_one (by positivity) hone
      (by unfold mHalveLin; omega : 16 * N ≤ mHalveLin N)) ?_
    have hstep : (Real.sqrt (1 + 1 / (8 * (N : ℝ))))⁻¹ ^ (16 * N)
        = ((1 + 1 / (8 * (N : ℝ)))⁻¹) ^ (8 * N) := by
      rw [show 16 * N = 2 * (8 * N) by ring, pow_mul, inv_pow,
        Real.sq_sqrt (le_of_lt hpos)]
    rw [hstep]
    rw [inv_pow]
    have hX : (0 : ℝ) < (1 + 1 / (8 * (N : ℝ))) ^ (8 * N) := by positivity
    rw [← one_div, div_le_iff₀ hX]
    have hposu : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
    have hbern := one_add_mul_le_pow (R := ℝ) (a := 1 / (8 * (N : ℝ)))
      (by linarith) (8 * N)
    have e2 : (((8 * N : ℕ)) : ℝ) * (1 / (8 * (N : ℝ))) = 1 := by
      push_cast
      field_simp
    rw [e2] at hbern
    linarith

/-! ## 4.  The numeric half of `RunData`, per order and total in `G`

`FinalStroke.endgame_of_parts` needs `P : (G : Input) → RunParams G` — a **total** function, because
a `structure` in `Type` cannot be produced on a case split inside the term.  `RunParams.hhalve` is
the only field that sees the order, and §3 discharges it at every order, so these definitions are
total with no case analysis at the call site. -/

/-- **`RunParams G` at the shallow constants**, with the round factor of `runParamsOf`
(`SimLoop.simRounds` at the leaf's potential, radius and halving time). -/
noncomputable def paramsShallow (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOf G dq hdq
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n)) (rmaxOf_nonneg _)
    (mHalve (G.n * G.n)) (one_le_mHalve _) (hhalve_perG (G.n * G.n))

/-- **`RunParams G` at the shallow constants with a round factor of the caller's choosing** (only
`K ≥ budgetRounds G dq (mHalve (G.n·G.n))`).  This is the form the fuel slot consumes. -/
noncomputable def paramsK (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (_hdq : 0 < dq) (K : ℕ)
    (hK : QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) ≤ K) :
    QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.FinalStroke.runParamsOfK G dq _hdq
    (QMCLeafB.RundataHalving.rmaxOf (G.n * G.n)) (rmaxOf_nonneg _)
    (mHalve (G.n * G.n)) (one_le_mHalve _) K hK (hhalve_perG (G.n * G.n))

/-- The ceiling of `paramsK` is the shallow one. -/
theorem paramsK_rmax (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) (K : ℕ)
    (hK : QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) ≤ K) :
    (paramsK G dq hdq K hK).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

/-- The halving time of `paramsK` is `mHalve (G.n·G.n)`, i.e. `16·(G.n·G.n)²` at every order
`2 ≤ G.n`. -/
theorem paramsK_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) (K : ℕ)
    (hK : QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) ≤ K) :
    (paramsK G dq hdq K hK).m = mHalve (G.n * G.n) := rfl

/-- The round factor of `paramsK` is the caller's `K`. -/
theorem paramsK_K (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) (K : ℕ)
    (hK : QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) ≤ K) :
    (paramsK G dq hdq K hK).K = K := rfl

/-- The round factor of `paramsShallow` is `runParamsOf`'s `simRounds` value. -/
theorem paramsShallow_K (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) :
    (paramsShallow G dq hdq).K
      = QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) := rfl

/-- The halving time of `paramsShallow` is `mHalve (G.n·G.n)`, i.e. `16·(G.n·G.n)²` at `2 ≤ G.n`. -/
theorem paramsShallow_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) :
    (paramsShallow G dq hdq).m = mHalve (G.n * G.n) := rfl

/-- The ceiling of `paramsShallow` is the shallow one. -/
theorem paramsShallow_rmax (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) :
    (paramsShallow G dq hdq).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl

/-- **The round count of `RunParts` at `paramsK`, in closed form.**  `RunParts`' twelve fields are
all guarded by `k < P.K * P.m` and `hverdict` compares the leaf's bit against
`SimLoop.anyOk ok (P.K * P.m)`; this is the rewrite that turns both into the fuel's own count
`K G * mHalve (G.n·G.n)`. -/
theorem paramsK_K_mul_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) (K : ℕ)
    (hK : QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) ≤ K) :
    (paramsK G dq hdq K hK).K * (paramsK G dq hdq K hK).m = K * mHalve (G.n * G.n) := rfl

/-- The same at the shallow ceil and the `runParamsOf` round factor. -/
theorem paramsShallow_K_mul_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq) :
    (paramsShallow G dq hdq).K * (paramsShallow G dq hdq).m
      = QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n)) * mHalve (G.n * G.n) := rfl

/-! ## 4b.  The round factor made explicit: `K = (1 + n·n·B)·mHalve (n·n)`

`paramsK` still takes the round factor `K` on faith.  What the fuel slot can actually produce is a
*bit budget* `B`: `Fuel.fuelTake` needs `T p ≤ (encodeRequest p.1).length^(2^k)`, and
`RoundCountBound.simRounds_le_of_bound` turns `8√M(c_A+1)/dq ≤ 2^B` into
`simRounds ≤ (1 + n·n·B)·m`.  So the honest per-order round count is the explicit monomial
`(1 + n·n·B)·mHalve (n·n)`, with `B` the input's bit budget. -/

/-- **A bit budget dominates `budgetRounds`.**  The `K` side of `RunParams`, in the shape the fuel
program supplies it: if `8·√M·(c_A+1)/dq ≤ 2^B` at the leaf's own `M = 2n² + 2dq²`,
`c_A = Rq G`, then `K := (1 + n·n·B)·mHalve (n·n)` is above the campaign's round count. -/
theorem budgetRounds_le_monomial (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (hn : 2 ≤ G.n) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : Real.sqrt (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B) :
    QMCLeafB.FinalStroke.budgetRounds G dq (mHalve (G.n * G.n))
      ≤ (1 + G.n * G.n * B) * mHalve (G.n * G.n) := by
  have hM : (0 : ℝ) < (((2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) := by
    have h1 : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
      nlinarith [sq_nonneg (G.n : ℚ), sq_nonneg dq]
    exact_mod_cast h1
  have hdq' : (0 : ℝ) < ((dq : ℚ) : ℝ) := by exact_mod_cast hdq
  have hcA : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by
    have h := QMCLeafB.EngineRuntime.Rq_nonneg G
    exact_mod_cast h
  exact QMCLeafB.RoundCountBound.simRounds_le_of_bound hn hM hdq' hcA hB1 hB
    (mHalve (G.n * G.n))

/-- **`RunParams G` from a bit budget**, total in `G`.  At `2 ≤ G.n` the round factor is the
explicit monomial `(1 + n·n·B G)·mHalve (n·n)` (§4b); at the degenerate orders, where no run is
needed, it falls back to `paramsShallow` so that the family is total. -/
noncomputable def paramsB (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G', 1 ≤ B G')
    (hB : ∀ G', Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G') :
    QMCLeafB.FinalStroke.RunParams G :=
  if h : 2 ≤ G.n then
    paramsK G dq hdq ((1 + G.n * G.n * B G) * mHalve (G.n * G.n))
      (budgetRounds_le_monomial G dq hdq h (B G) (hB1 G) (hB G))
  else paramsShallow G dq hdq

theorem paramsB_K (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G', 1 ≤ B G')
    (hB : ∀ G', Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (hn : 2 ≤ G.n) :
    (paramsB G dq hdq B hB1 hB).K = (1 + G.n * G.n * B G) * mHalve (G.n * G.n) := by
  unfold paramsB
  rw [dif_pos hn]
  exact paramsK_K G dq hdq _ _

theorem paramsB_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G', 1 ≤ B G')
    (hB : ∀ G', Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (hn : 2 ≤ G.n) :
    (paramsB G dq hdq B hB1 hB).m = mHalve (G.n * G.n) := by
  unfold paramsB
  rw [dif_pos hn]
  exact paramsK_m G dq hdq _ _

theorem paramsB_rmax (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G', 1 ≤ B G')
    (hB : ∀ G', Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (hn : 2 ≤ G.n) :
    (paramsB G dq hdq B hB1 hB).rmax = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := by
  unfold paramsB
  rw [dif_pos hn]
  exact paramsK_rmax G dq hdq _ _

/-- **The round count of `RunParts` at `paramsB`, in closed form**: the monomial squared,
`((1 + n·n·B)·mHalve (n·n))·mHalve (n·n)`.  This is what `hverdict` and the twelve prefix guards
of `RunParts` see, and what `fuel`'s length must be. -/
theorem paramsB_K_mul_m (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G', 1 ≤ B G')
    (hB : ∀ G', Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (hn : 2 ≤ G.n) :
    (paramsB G dq hdq B hB1 hB).K * (paramsB G dq hdq B hB1 hB).m
      = ((1 + G.n * G.n * B G) * mHalve (G.n * G.n)) * mHalve (G.n * G.n) := by
  rw [paramsB_K G dq hdq B hB1 hB hn, paramsB_m G dq hdq B hB1 hB hn]

/-! ## 5.  Why the constants cannot stay global

The shallow halving inequality is *not* available at a constant ceiling.  The obstruction is the
order dependence of the determinant multiplier: at fixed `ρ`, `rho0R N ρ` tends to `e^{-2ρ} ≤ 1`,
while the inequality `(√·)⁻¹ ^ m ≤ 1/2` needs `rho0R N ρ > 1` outright (if `rho0R N ρ ≤ 1` then
`√· ≤ 1`, so `(√·)⁻¹ ≥ 1` — and positivity of `rho0R` makes `√· > 0` — so the `m`-th power is
`≥ 1`).  §5 makes the consequent explicit with an elementary bound instead of a limit:
`rho0R N ρ ≤ (1+4/N)/(1+2ρ)`. -/

/-- **`rho0R` is below `1` once the order beats `1/ρ`.**  From the factorised form,
`rho0R N ρ = (1−1/N²)^N·(N+1)/(N−1)/(1+ρ/N)^{2N}`, with `(1−1/N²)^N ≤ 1`,
`(N+1)/(N−1) ≤ 1 + 4/N` and Bernoulli `(1+ρ/N)^{2N} ≥ 1 + 2ρ`. -/
theorem rho0R_le_one_of_le_ratio (N : ℕ) (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 < ρ)
    (hNr : 9 / (N : ℝ) ≤ 2 * ρ) : QMCLeafB.EngineIterates.rho0R N ρ ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h0 : (0 : ℕ) < N := by omega
    exact_mod_cast h0
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  -- the `(1-1/N²)^N ≤ 1` factor
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    rw [sub_nonneg, div_le_one (by positivity)]
    exact h1
  have hbase1 : (1 - 1 / (N : ℝ) ^ 2) ^ N ≤ 1 := by
    refine pow_le_one₀ hbase0 (by linarith [div_nonneg (zero_le_one' ℝ) (sq_nonneg (N : ℝ))])
  -- the `(N+1)/(N-1) ≤ 1 + 4/N` factor
  have hmid : ((N : ℝ) + 1) / ((N : ℝ) - 1) ≤ 1 + 4 / (N : ℝ) := by
    have hkey : (4 : ℝ) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    rw [div_le_iff₀ hNm1]
    have hexp : (1 + 4 / (N : ℝ)) * ((N : ℝ) - 1) = (N : ℝ) + 3 - 4 / (N : ℝ) := by
      field_simp
      ring
    rw [hexp]
    linarith
  have hmid_nn : (0 : ℝ) ≤ ((N : ℝ) + 1) / ((N : ℝ) - 1) :=
    div_nonneg (by positivity) hNm1.le
  have hnum_nn : (0 : ℝ) ≤ (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1)) :=
    mul_nonneg (pow_nonneg hbase0 _) hmid_nn
  have hnum : (1 - 1 / (N : ℝ) ^ 2) ^ N * (((N : ℝ) + 1) / ((N : ℝ) - 1))
      ≤ 1 + 4 / (N : ℝ) := by
    have h := mul_le_mul hbase1 hmid hmid_nn (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  -- Bernoulli on the denominator
  have hden : 1 + 2 * ρ ≤ (1 + ρ / (N : ℝ)) ^ (2 * N) := by
    have hρN : (0 : ℝ) < ρ / (N : ℝ) := by positivity
    have hbern := one_add_mul_le_pow (R := ℝ) (a := ρ / (N : ℝ)) (by linarith) (2 * N)
    have e : (((2 * N : ℕ)) : ℝ) * (ρ / (N : ℝ)) = 2 * ρ := by
      push_cast
      field_simp
    rwa [e] at hbern
  have hpos : (0 : ℝ) < 1 + 2 * ρ := by linarith
  have h49 : (4 : ℝ) / (N : ℝ) ≤ 9 / (N : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) hNpos.le
  rw [QMCLeafB.RundataHalving.rho0R_factor N hN hρ.le]
  refine le_trans (div_le_div_of_nonneg_left hnum_nn hpos hden) ?_
  rw [div_le_one hpos]
  linarith

/-- **At a positive ceiling `ρ` there are orders where the halving inequality fails.**  Take
`n = max 2 ⌈9/(2ρ)⌉₊`: then `n·n ≥ 9/(2ρ)`, `rho0R (n·n) ρ ≤ 1`, and the `m`-th power of the
inverse root is at least `1`. -/
theorem exists_sq_order_gt_half (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    ∃ n : ℕ, 1 / 2 < (Real.sqrt (QMCLeafB.EngineIterates.rho0R (n * n) ρ))⁻¹ ^ m := by
  set n : ℕ := max 2 ⌈9 / (2 * ρ)⌉₊ with hn
  have hn2 : 2 ≤ n := le_max_left _ _
  have hceil : 9 / (2 * ρ) ≤ (⌈9 / (2 * ρ)⌉₊ : ℝ) := Nat.le_ceil _
  have hle_n : 9 / (2 * ρ) ≤ (n : ℝ) := by
    have hcast : ((⌈9 / (2 * ρ)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_max_right (2 : ℕ) ⌈9 / (2 * ρ)⌉₊
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h0 : (0 : ℕ) < n := by omega
    exact_mod_cast h0
  have hsq_ge : (n : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : (1 : ℕ) ≤ n := by omega
      exact_mod_cast h
    push_cast
    nlinarith
  have hN2 : 2 ≤ n * n := by
    have h := Nat.mul_le_mul hn2 hn2
    omega
  have hratio : 9 / ((n * n : ℕ) : ℝ) ≤ 2 * ρ := by
    have h2ρ : (0 : ℝ) < 2 * ρ := by linarith
    have h9 : 9 ≤ 2 * ρ * (n : ℝ) := by
      have h := hle_n
      rw [div_le_iff₀ h2ρ] at h
      linarith
    have h9' : 9 ≤ 2 * ρ * ((n * n : ℕ) : ℝ) := by nlinarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((n * n : ℕ) : ℝ))]
    linarith
  refine ⟨n, ?_⟩
  have hle1 := rho0R_le_one_of_le_ratio (n * n) hN2 hρ hratio
  have hpos0 : (0 : ℝ) < QMCLeafB.EngineIterates.rho0R (n * n) ρ :=
    QMCLeafB.EngineIterates.rho0R_pos hN2 hρ.le
  have hsq_le : Real.sqrt (QMCLeafB.EngineIterates.rho0R (n * n) ρ) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hle1
  have hsq_pos : (0 : ℝ) < Real.sqrt (QMCLeafB.EngineIterates.rho0R (n * n) ρ) :=
    Real.sqrt_pos.mpr hpos0
  have hinv : (1 : ℝ) ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R (n * n) ρ))⁻¹ := by
    rw [← one_div, one_le_div hsq_pos]
    exact hsq_le
  have hge : (1 : ℝ) ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R (n * n) ρ))⁻¹ ^ m :=
    one_le_pow₀ hinv
  linarith

/-- **A constant ceiling cannot serve all orders.**  This is the negation of the `hhalve` slot of
`QMCLeafB.FinalStroke.endgame_orbit(_sq)` / `QMCLeafB.FinalReunion.endgame_RSt` at any positive
constant ceiling, hence §3/§4 are the only way to inhabit that slot. -/
theorem not_forall_hhalve (rmax : ℚ) (hrmax : 0 < rmax) (m : ℕ) :
    ¬ ∀ N : ℕ,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ((rmax : ℚ) : ℝ)))⁻¹ ^ m ≤ 1 / 2 := by
  intro h
  have hρ : (0 : ℝ) < ((rmax : ℚ) : ℝ) := by exact_mod_cast hrmax
  obtain ⟨n, hn⟩ := exists_sq_order_gt_half ((rmax : ℚ) : ℝ) hρ m
  exact absurd (h (n * n)) (not_le.mpr hn)

/-- The same, in the shape the closing strokes state it: `hhalve : ∀ G, …` is false at a constant
ceiling, for the input `⟨n, 0⟩` of order `n`. -/
theorem not_forall_hhalve_input (rmax : ℚ) (hrmax : 0 < rmax) (m : ℕ) :
    ¬ ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax : ℚ) : ℝ)))⁻¹ ^ m
        ≤ 1 / 2 := by
  intro h
  have hρ : (0 : ℝ) < ((rmax : ℚ) : ℝ) := by exact_mod_cast hrmax
  obtain ⟨n, hn⟩ := exists_sq_order_gt_half ((rmax : ℚ) : ℝ) hρ m
  exact absurd (h ⟨n, fun _ => 0⟩) (not_le.mpr hn)


/-! ## 6.  The closing stroke at per-order constants

`FinalStroke.endgame_orbit_of_parts` is the orbit closing stroke with the *full* bracket, and
`FinalStroke.endgame_of_dominated_rounds_interior` is the interior bracket with the shelf's *ball*
size slot.  Neither is the combination the endgame actually needs — the loop size slot must be the
reachable-orbit one (§4b of `Check_final_stroke_m7`) *and* the run bundle must be asked for only
strictly below `-Rq G/40000` (so the brick never has to produce the feasible round).  §6.1 supplies
that combination; §6.2/§6.3 drop the numeric half of `RunData` into `paramsK`, i.e. they are the
endgame with `rmax`, `hrmax`, `m`, `hm1`, `hhalve` **gone** from the residual. -/

/-- **The per-order endgame, interior bracket, orbit size slot.**  `RunData` only below
`-Rq G / 40000`, and the state grows by a monomial `C·(L+1)^k` per round along the orbit. -/
theorem endgame_perG_interior {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : σ) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict T0 G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.solution_of_loop_orbit init fuel round verdict hinit hfuel hr hv
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow round C k hk hmono a j hj)
    (QMCLeafB.FinalStroke.loopBit init round verdict T0)
    (QMCLeafB.FinalStroke.hspec_of_tape_free init fuel round verdict T0 hinitTape hfuelLen)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (QMCLeafB.FinalStroke.loopBit init round verdict T0) htop hd)

/-- **The same with the full bracket.**  `RunData` everywhere on `[-Rq G, 0]`. -/
theorem endgame_perG {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : σ) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts init fuel round verdict hinit hfuel hr hv
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => QMCLeafB.FinalStroke.orbit_of_monomial_pow round C k hk hmono a j hj)
    T0 hinitTape hfuelLen hd

/-- **`d9f601e5` at m8's `σ = InitVerdict.St`, per-order constants, interior bracket.**  The
residual is the fuel length, the round's growth class, `htop` (the verdict program's job) and
`RunParts` at `paramsK` — the numeric half of `RunData`, including `rmax`/`m`/`hhalve`, is
discharged by §3/§4. -/
theorem endgame_St_interior
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G QMCLeafB.InitVerdict.dqV (mHalve (G.n * G.n)) ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (hr : Automatic.Poly round)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.InitVerdict.St) (j : ℕ),
      (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * mHalve (p.1.1.n * p.1.1.n))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
        (fun G' _ => K G' * mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          (fun G' _ => K G' * mHalve (G'.n * G'.n))) G t
        (paramsK G QMCLeafB.InitVerdict.dqV (by norm_num [QMCLeafB.InitVerdict.dqV])
          (K G) (hK G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_perG_interior QMCLeafB.InitVerdict.init fuel round QMCLeafB.InitVerdict.verdict
    QMCLeafB.InitVerdict.poly_init hfuel hr QMCLeafB.InitVerdict.poly_verdict
    C k hk hmono (fun G' _ => K G' * mHalve (G'.n * G'.n)) QMCLeafB.InitVerdict.init_tape
    hfuelLen htop
    (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData)

/-- **`d9f601e5` at m3's `σ = RoundProgram.RSt`, per-order constants, interior bracket,
`dq = 1`.**  `dq = 1` because `RSt.mu` is the box bound `2n² + 2dq²` of `initShapeOf`. -/
theorem endgame_RSt_interior
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.budgetRounds G 1
      (mHalve (G.n * G.n)) ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * mHalve (p.1.1.n * p.1.1.n))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G' * mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G' * mHalve (G'.n * G'.n))) G t
        (paramsK G 1 (by norm_num) (K G) (hK G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_perG_interior init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    C k hk hmono (fun G' _ => K G' * mHalve (G'.n * G'.n)) hinitTape hfuelLen htop
    (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData)

/-! ### 6.05  The size slot in the form the round can actually satisfy

§6.0's `hmono` (and m7's `endgame_orbit`/`endgame_RSt`, and `orbit_of_monomial_pow`) ask for

    ∀ s j, (enc (round^[j] s)).length ≤ C · ((enc s).length + 1) ^ k,

i.e. for **every** `j`, unbounded.  m3's round appends one `ok` flag to the state's record list per
round, so for fixed `s` the left side grows linearly in `j` while the right side is constant: the form
is unsatisfiable for a real round (m1's d7 puts it sharply).  `FinalStroke.poly_loop_state_orbit` only
ever uses the bound at `j ≤ a.2.length`, and `a.2.length ≤ (encSt a).length` because the fuel's own
encoding is part of `encSt a` — so the correct hypothesis is the reachable-orbit one with `j` bounded
by the **fuel length**, which a linear-in-`j` growth absorbs in a low-degree `sizes`.  The theorems
below take `sizes` and that orbit bound directly. -/

/-- **The per-order endgame from a reachable-orbit size bound** (no `hmono`). -/
theorem endgame_perG_orbit {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict T0 G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.solution_of_loop_orbit init fuel round verdict hinit hfuel hr hv sizes horbit
    (QMCLeafB.FinalStroke.loopBit init round verdict T0)
    (QMCLeafB.FinalStroke.hspec_of_tape_free init fuel round verdict T0 hinitTape hfuelLen)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (QMCLeafB.FinalStroke.loopBit init round verdict T0) htop hd)

/-- **`d9f601e5` at `RoundProgram.RSt`, per-order constants, explicit round count, orbit size
slot.**  The `RunParts`-residual form: with `RunParts` at `paramsB` below `-Rq G/40000` and the two
top/bottom program facts, this is the statement. -/
theorem endgame_RSt_bound_orbit
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ B G)
    (hB : ∀ G' : QuantumMaxCutEnergy.Input,
      Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((1 : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length
        = ((1 + p.1.1.n * p.1.1.n * B p.1.1) * mHalve (p.1.1.n * p.1.1.n))
            * mHalve (p.1.1.n * p.1.1.n))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
          * mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
            * mHalve (G'.n * G'.n))) G t
        (paramsB G 1 (by norm_num) B hB1 hB)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_perG_orbit init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    sizes horbit
    (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n)) * mHalve (G'.n * G'.n))
    hinitTape hfuelLen htop
    (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData)

/-! ### 6.1  The endgame whose round count is an explicit monomial

`endgame_RSt_interior` still takes `K` and `hK`.  With `paramsB` (§4b) both are replaced by a bit
budget `B` and the hypothesis `8√M(c_A+1)/dq ≤ 2^B`, and the round count becomes the explicit
monomial `((1 + n·n·B)·mHalve (n·n))·mHalve (n·n)` — which is exactly the length the fuel program
must produce and the `anyOk` prefix `hverdict` compares against. -/

/-- **`d9f601e5` at `RoundProgram.RSt`, `dq = 1`, per-order constants, explicit round count.** -/
theorem endgame_RSt_bound_interior
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ B G)
    (hB : ∀ G' : QuantumMaxCutEnergy.Input,
      Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((1 : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length
        = ((1 + p.1.1.n * p.1.1.n * B p.1.1) * mHalve (p.1.1.n * p.1.1.n))
            * mHalve (p.1.1.n * p.1.1.n))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
          * mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
            * mHalve (G'.n * G'.n))) G t
        (paramsB G 1 (by norm_num) B hB1 hB)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_perG_interior init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    C k hk hmono
    (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n)) * mHalve (G'.n * G'.n))
    hinitTape hfuelLen htop
    (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData)

/-- **The same at `InitVerdict.St`**, with the oracle tolerance `dq` a parameter. -/
theorem endgame_St_bound_interior
    (dq : ℚ) (hdq : 0 < dq)
    (B : QuantumMaxCutEnergy.Input → ℕ) (hB1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ B G)
    (hB : ∀ G' : QuantumMaxCutEnergy.Input,
      Real.sqrt (((2 * (G'.n : ℚ) ^ 2 + 2 * dq ^ 2 : ℚ)) : ℝ) * 8
        * (((QMCLeafB.EngineRuntime.Rq G' : ℚ) : ℝ) + 1) / ((dq : ℚ) : ℝ) ≤ (2 : ℝ) ^ B G')
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (hr : Automatic.Poly round)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : QMCLeafB.InitVerdict.St) (j : ℕ),
      (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length
        = ((1 + p.1.1.n * p.1.1.n * B p.1.1) * mHalve (p.1.1.n * p.1.1.n))
            * mHalve (p.1.1.n * p.1.1.n))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
        (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
          * mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n))
            * mHalve (G'.n * G'.n))) G t
        (paramsB G dq hdq B hB1 hB)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_perG_interior QMCLeafB.InitVerdict.init fuel round QMCLeafB.InitVerdict.verdict
    QMCLeafB.InitVerdict.poly_init hfuel hr QMCLeafB.InitVerdict.poly_verdict
    C k hk hmono
    (fun G' _ => ((1 + G'.n * G'.n * B G') * mHalve (G'.n * G'.n)) * mHalve (G'.n * G'.n))
    QMCLeafB.InitVerdict.init_tape hfuelLen htop
    (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData)

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.HalvePerG.rho0R_zero
#print axioms QMCLeafB.HalvePerG.rho0R_one
#print axioms QMCLeafB.HalvePerG.rmaxOf_nonneg
#print axioms QMCLeafB.HalvePerG.rmaxOf_cast
#print axioms QMCLeafB.HalvePerG.one_le_mHalve
#print axioms QMCLeafB.HalvePerG.mHalve_eq_mOf
#print axioms QMCLeafB.HalvePerG.mHalve_eq
#print axioms QMCLeafB.HalvePerG.hhalve_perG
#print axioms QMCLeafB.HalvePerG.one_le_mHalveLin
#print axioms QMCLeafB.HalvePerG.mHalveLin_le_mHalve
#print axioms QMCLeafB.HalvePerG.hhalve_perG_lin
#print axioms QMCLeafB.HalvePerG.paramsShallow
#print axioms QMCLeafB.HalvePerG.paramsK
#print axioms QMCLeafB.HalvePerG.paramsK_rmax
#print axioms QMCLeafB.HalvePerG.paramsK_m
#print axioms QMCLeafB.HalvePerG.paramsK_K
#print axioms QMCLeafB.HalvePerG.paramsShallow_K
#print axioms QMCLeafB.HalvePerG.paramsShallow_m
#print axioms QMCLeafB.HalvePerG.paramsShallow_rmax
#print axioms QMCLeafB.HalvePerG.paramsK_K_mul_m
#print axioms QMCLeafB.HalvePerG.paramsShallow_K_mul_m
#print axioms QMCLeafB.HalvePerG.budgetRounds_le_monomial
#print axioms QMCLeafB.HalvePerG.paramsB
#print axioms QMCLeafB.HalvePerG.paramsB_K
#print axioms QMCLeafB.HalvePerG.paramsB_m
#print axioms QMCLeafB.HalvePerG.paramsB_rmax
#print axioms QMCLeafB.HalvePerG.paramsB_K_mul_m
#print axioms QMCLeafB.HalvePerG.rho0R_le_one_of_le_ratio
#print axioms QMCLeafB.HalvePerG.exists_sq_order_gt_half
#print axioms QMCLeafB.HalvePerG.not_forall_hhalve
#print axioms QMCLeafB.HalvePerG.not_forall_hhalve_input
#print axioms QMCLeafB.HalvePerG.endgame_perG_orbit
#print axioms QMCLeafB.HalvePerG.endgame_RSt_bound_orbit
#print axioms QMCLeafB.HalvePerG.endgame_perG
#print axioms QMCLeafB.HalvePerG.endgame_St_interior
#print axioms QMCLeafB.HalvePerG.endgame_RSt_interior
#print axioms QMCLeafB.HalvePerG.endgame_RSt_bound_interior
#print axioms QMCLeafB.HalvePerG.endgame_St_bound_interior

end QMCLeafB.HalvePerG


