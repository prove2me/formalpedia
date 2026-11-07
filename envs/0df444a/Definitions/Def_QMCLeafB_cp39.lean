-- Prove2me | Definitions.Def_QMCLeafB_cp39
-- name    : QMCLeafB_cp39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:25:31.542353+00:00
-- url     : https://prove2.me/theorems/f996819c-0567-447b-9e49-9f0ae8552c08
-- title:
--   QMCLeafB cp39
-- statement:
--   # `Check_cp39_m5` — phase 39, member m5, direction d3 (`concrete-programme`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_dc35
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_b1d37
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_pbit33
/-
# `Check_cp39_m5` — phase 39, member m5, direction d3 (`concrete-programme`)

**The leaf's last object `SepStream` is REFUTED at the concrete campaign programme — for every
normal stream — and the failure is repaired only by a change of PROGRAMME.**

`Check_rf38_m1.SepStream P c hc` asks for a nonzero rational normal stream placing the engine's
accumulated centre on the far side of the WHOLE relaxation at every round below the horizon, for
every `G` and every `t`.  This file proves that at the campaign programme
(`UnionShallow.paramsKbc2`) the object is **UNSATISFIABLE**, and it identifies the programme change
that is actually forced.

## The mechanism (three live bundles and one identity)

1. `BallM2.sliver_ball_campaign` (`Def_QMCLeafB_ball_m2`) — the sliver body at `(G₁,t₁)` carries the
   explicit Euclidean ball of radius `rSliver = 1/9120000 = dq/(8(cAq+1))`, i.e. **exactly the
   campaign's `hbudget` radius**, and `(G₁,t₁)` is inside the oracle bracket.
2. `Bypass35M6.shallowCut_of_separating` (`Def_QMCLeafB_by35`) — a far-side rational stream gives
   `ShallowCut` with `del ≡ 0` (no `rmax`, no `σ`, no ellipsoid).
3. `DC35M1.not_shallowCut_of_ball_horizon` (`Def_QMCLeafB_dc35`) — a ball of radius `r > 0` in the
   body plus `det A₀ · rho0R(N,rmax)^(K·m) · r^{2N} > 1` refutes `ShallowCut`.

The criterion is **not** an extra hypothesis at a `RunParams`.  With `M = 2n² + 2dq²` (the initial
shape `initShapeOf N M = M⁻¹ • 1`), `volPot N (initShapeOf N M) = M^{N/2}` and
`det (castM (initShapeOf N M)) = M^{-N}`, so

* `hbudget` (`M^{N/2} · 2^{-K} < r^N`) gives `2^K > M^{N/2} · r^{-N}`,
* `hhalve` (`(√rho0R)^{-m} ≤ 1/2`) gives `rho0R^m ≥ 4`,

hence `rho0R^{K·m} = (rho0R^m)^K ≥ 4^K = (2^K)^2 > M^N · r^{-2N}` — the criterion, **exactly, for
every `rmax`**.  The sliver ball sits at the `hbudget` radius, so the two `RunParams` axioms are
critical against it and the strictness of `hbudget` decides it.  Therefore `ShallowCut` is empty at
`(G₁,t₁)` for **every** `K`, `m`, `rmax` and every `cAq ≥ ∑ᵢⱼ|wᵢⱼ|`, at the campaign tolerance
`dq = 1/380000`.

## The programme change this forces

* `SepStream` must be restricted to what the leaf actually consumes — the oracle bracket
  (`-Rq ≤ t < -Rq/40000`) and the bit-`false` stratum.  `SepSlot` below is that object, and
  `solution_of_sepSlot` is the leaf from it (no `SelfRecG` detour).
* Even restricted, at the campaign programme the object FORCES the bit `true` at the sliver
  (`sepSlot_forces_bit_true`).  So the repair is a **GATE change** (`ok ↔ RelaxMem`: a
  body-carrying point reads `true`), or a **BODY change** (thin / rational-level-set relaxations,
  where `bodyRec_of_level` produces the record with no separation at all) — never a change of the
  depth schedule, because the refutation is `rmax`-free.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration (all exactly `[propext, Classical.choice, Quot.sound]`);
imports are published `Definitions.*` bundles only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 60000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Cp39M5

open Matrix
open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)

/-! ## 0.  The sliver, the campaign programme, and the campaign tolerance -/

/-- The sliver input (two vertices, one edge of weight `1`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁

/-- The sliver threshold. -/
abbrev t₁ : ℚ := QMCLeafB.AnchorFactsM2.t₁

/-- The campaign parameter family at the sliver. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.AnchorFactsM2.P₁

/-- The campaign programme, as a family. -/
abbrev Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  fun G => QMCLeafB.UnionShallow.paramsKbc2 G

theorem hn₁ : 2 ≤ G₁.n := QMCLeafB.AnchorFactsM2.hn₁

/-- The campaign tolerance at the sliver. -/
theorem dq_sliver : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

/-- `(G₁,t₁)` lies in the oracle bracket. -/
theorem sliver_bracket :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ t₁ ∧
      ((t₁ : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₁_mem_bracket

/-! ## 1.  The two closed forms of the initial shape

`initShapeOf N M = M⁻¹ • 1`, so the volume potential is `M^{N/2}` and the determinant is `M^{-N}`.
At the engine's order `N = n·n = 4` these are `M²` and `M⁻⁴` — the two quantities `hbudget` and the
horizon criterion are priced in. -/

/-- The volume potential of the initial shape, at order `4`. -/
theorem volPot_init_four (M : ℚ) :
    QMCLeafB.EngineIterates.volPot 4 (QMCLeafB.Boundary.initShapeOf 4 M) = ((M : ℝ)) ^ 2 := by
  unfold QMCLeafB.EngineIterates.volPot
  rw [QMCLeafB.Boundary.castM_initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((M : ℝ)⁻¹) ^ 2), inv_pow, inv_inv]

#print axioms QMCLeafB.Cp39M5.volPot_init_four

/-- The determinant of the initial shape, at order `4`. -/
theorem det_init_four (M : ℚ) :
    (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf 4 M)).det
      = ((M : ℝ)⁻¹) ^ 4 := by
  rw [QMCLeafB.Boundary.castM_initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

#print axioms QMCLeafB.Cp39M5.det_init_four

/-! ## 2.  **The critical identity**: `hbudget` + `hhalve` ⟹ the horizon criterion

No `rmax` appears in the conclusion's *size*: the two `RunParams` axioms compose to exactly the ball
floor's exponent.  The ball radius `R` of `hbudget` and the ball radius `r` of the criterion are
linked only by `R ≤ r`. -/

/-- **THE CRITICAL IDENTITY.**  At order `4`, any body carrying a ball of radius `r ≥ R`, where `R`
is the `hbudget` radius, and any horizon `K·m` with the halving time `m`, satisfies the ball-floor
criterion `det A₀ · rho0R^{K·m} · r^{2N} > 1`. -/
theorem criterion_of_budget_halve

    (M : ℚ) (hM : 0 < M) (K m : ℕ) (rmax : ℚ) (hrmax : 0 ≤ rmax)
    (R r : ℝ) (hR : 0 < R) (hRr : R ≤ r)
    (hbudget : QMCLeafB.EngineIterates.volPot 4 (QMCLeafB.Boundary.initShapeOf 4 M)
      * (1 / 2) ^ K < R ^ 4)
    (hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)))⁻¹ ^ m ≤ 1 / 2) :
    1 < (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf 4 M)).det
      * (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m) * r ^ (2 * 4) := by
  have hr : (0 : ℝ) < r := lt_of_lt_of_le hR hRr
  have hy : (0 : ℝ) < QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ) :=
    QMCLeafB.EngineIterates.rho0R_pos (by norm_num) (by exact_mod_cast hrmax)
  have h2K : (0 : ℝ) < (2 : ℝ) ^ K := pow_pos (by norm_num) K
  have hR4 : (0 : ℝ) < R ^ 4 := pow_pos hR 4
  have hr4 : (0 : ℝ) < r ^ 4 := pow_pos hr 4
  have hr8 : (0 : ℝ) < r ^ 8 := pow_pos hr 8
  -- (i)  hbudget  ⟹  M²/r⁴ < 2^K
  have hbud : ((M : ℝ)) ^ 2 * ((2 : ℝ) ^ K)⁻¹ < R ^ 4 := by
    have h := hbudget
    rw [volPot_init_four] at h
    have hpow : ((1 / 2 : ℝ)) ^ K = ((2 : ℝ) ^ K)⁻¹ := by rw [one_div, inv_pow]
    rwa [hpow] at h
  have hcross : ((M : ℝ)) ^ 2 < R ^ 4 * (2 : ℝ) ^ K := by
    have hstep : ((M : ℝ) ^ 2 * ((2 : ℝ) ^ K)⁻¹) * (2 : ℝ) ^ K
        < R ^ 4 * (2 : ℝ) ^ K := mul_lt_mul_of_pos_right hbud h2K
    have hleft : ((M : ℝ) ^ 2 * ((2 : ℝ) ^ K)⁻¹) * (2 : ℝ) ^ K = (M : ℝ) ^ 2 := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt h2K), mul_one]
    linarith [hstep, hleft]
  have hratioR : ((M : ℝ)) ^ 2 / R ^ 4 < (2 : ℝ) ^ K := by
    rw [div_lt_iff₀ hR4]
    rw [mul_comm]
    exact hcross
  have hratio : ((M : ℝ)) ^ 2 / r ^ 4 < (2 : ℝ) ^ K := by
    refine lt_of_le_of_lt ?_ hratioR
    have h4 : R ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (le_of_lt hR) hRr 4
    exact div_le_div_of_nonneg_left (by positivity) hR4 h4
  -- (ii)  hhalve  ⟹  4 ≤ rho0R^m
  have hs : (0 : ℝ) < Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) :=
    Real.sqrt_pos.2 hy
  have h2m : (2 : ℝ) ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ))) ^ m := by
    have h1 : ((Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ))) ^ m)⁻¹
        ≤ (2 : ℝ)⁻¹ := by
      rw [← inv_pow]
      have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [← h2]
      exact hhalve
    exact (inv_le_inv₀ (pow_pos hs m) (by norm_num)).1 h1
  have h4m : (4 : ℝ) ≤ (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ m := by
    have hsq : ((Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ))) ^ m) ^ 2
        = (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ m := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt hy.le]
    have h22 : (2 : ℝ) ^ 2
        ≤ ((Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ))) ^ m) ^ 2 := by
      nlinarith [h2m, pow_pos hs m]
    rw [hsq] at h22
    norm_num at h22
    exact h22
  -- (iii) the exponent comparison
  have h4K : (4 : ℝ) ^ K
      ≤ ((QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ m) ^ K :=
    pow_le_pow_left₀ (by norm_num) h4m K
  have h4Ksq : (4 : ℝ) ^ K = ((2 : ℝ) ^ K) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul, Nat.mul_comm 2 K, pow_mul]
  have hyKm : (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m)
      = ((QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ m) ^ K := by
    rw [Nat.mul_comm K m, pow_mul]
  have hexp : ((M : ℝ) ^ 2 / r ^ 4) ^ 2 = (M : ℝ) ^ 4 / r ^ 8 := by
    rw [div_pow, ← pow_mul, ← pow_mul]
  have hmain : (M : ℝ) ^ 4 / r ^ 8
      < (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m) := by
    have hsq : ((M : ℝ) ^ 2 / r ^ 4) ^ 2 < ((2 : ℝ) ^ K) ^ 2 := by
      nlinarith [hratio, h2K, show (0 : ℝ) ≤ (M : ℝ) ^ 2 / r ^ 4 by positivity]
    rw [hexp, ← h4Ksq] at hsq
    rw [hyKm]
    exact lt_of_lt_of_le hsq h4K
  -- (iv)  assemble
  have hM4 : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
  have hM' : (M : ℝ) ^ 4
      < (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m) * r ^ 8 := by
    have h := hmain
    rw [div_lt_iff₀ hr8] at h
    linarith [h]
  have hfin : (1 : ℝ)
      < ((M : ℝ) ^ 4)⁻¹
        * ((QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m) * r ^ 8) := by
    have hpos : (0 : ℝ) < ((M : ℝ) ^ 4)⁻¹ := by positivity
    have hstep := mul_lt_mul_of_pos_left hM' hpos
    rwa [inv_mul_cancel₀ (ne_of_gt hM4)] at hstep
  rw [det_init_four]
  have he : ((M : ℝ)⁻¹) ^ 4 * (QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m)
        * r ^ (2 * 4)
      = ((M : ℝ) ^ 4)⁻¹
        * ((QMCLeafB.EngineIterates.rho0R 4 ((rmax : ℚ) : ℝ)) ^ (K * m) * r ^ 8) := by
    rw [inv_pow]
    norm_num
    ring
  rw [he]
  exact hfin

#print axioms QMCLeafB.Cp39M5.criterion_of_budget_halve

/-! ## 3.  The sliver ball, at any programme with the campaign tolerance

`runBall G t P` depends on `P` only through `P.dq` (the norm bound is `2n² + 2dq²` too), so the
banked sliver ball transports to every `P` with `P.dq = 1/380000`. -/

/-- The relaxed body depends on the programme only through its tolerance. -/
theorem relaxBallP_congr_dq (P : QMCLeafB.FinalStroke.RunParams G₁) (hdq : P.dq = 1 / 380000) :
    ∀ z, z ∈ relaxBallP G₁ t₁ P ↔ z ∈ QMCLeafB.BallM2.runBall G₁ t₁ P₁ := by
  intro z
  simp only [QMCLeafB.BallM2.runBall, QMCLeafB.ThinRec34M4.relaxBallP]
  rw [hdq, dq_sliver]

#print axioms QMCLeafB.Cp39M5.relaxBallP_congr_dq

/-- The sliver body carries the campaign-radius ball at ANY programme with the campaign tolerance. -/
theorem sliver_ball_of_dq (P : QMCLeafB.FinalStroke.RunParams G₁) (hdq : P.dq = 1 / 380000) :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs)
      QMCLeafB.BallM2.rSliver ⊆ relaxBallP G₁ t₁ P := by
  intro z hz
  have h := QMCLeafB.BallM2.sliver_ball_campaign
  rw [QMCLeafB.BallM2.sliver_campaign_radius] at h
  exact (relaxBallP_congr_dq P hdq z).2 (h hz)

#print axioms QMCLeafB.Cp39M5.sliver_ball_of_dq

/-- The same ball in the `∀ y, ‖y‖ ≤ r` shape the horizon criterion consumes. -/
theorem ball_hyp_sliver (P : QMCLeafB.FinalStroke.RunParams G₁) (hdq : P.dq = 1 / 380000) :
    ∀ y : Fin (G₁.n * G₁.n) → ℝ, (∑ i, y i ^ 2) ≤ QMCLeafB.BallM2.rSliver ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs) ∈ relaxBallP G₁ t₁ P := by
  intro y hy
  refine sliver_ball_of_dq P hdq ?_
  show (∑ i, ((y + QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs) i
    - (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs) i) ^ 2) ≤ QMCLeafB.BallM2.rSliver ^ 2
  simpa using hy

#print axioms QMCLeafB.Cp39M5.ball_hyp_sliver

/-! ## 4.  **THE REFUTATION AT THE CONCRETE PROGRAMME**

Every admissible `RunParams` at `G₁` whose tolerance is the campaign's `1/380000` is refuted at the
sliver: its own `hbudget` and `hhalve` put the ball-floor criterion strictly above `1`, and the body
carries that ball.  No horizon, no `rmax`, no `cAq` can avoid it. -/

/-- **NO SHALLOW-CUT STREAM AT THE SLIVER, AT ANY PROGRAMME.** -/
theorem not_shallowCut_at_sliver
    (P : QMCLeafB.FinalStroke.RunParams G₁) (hn : 2 ≤ G₁.n) (hdq : P.dq = 1 / 380000) :
    ¬ ShallowCut G₁ t₁ P hn := by
  have hcA2 : (2 : ℝ) ≤ (P.cAq : ℝ) := by
    have h := P.hAsum
    rw [QMCLeafB.BallM2.wMatrix_G₁_asum] at h
    linarith
  have hdqR : ((P.dq : ℚ) : ℝ) = 1 / 380000 := by rw [hdq]; norm_num
  set R : ℝ := (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef, hdqR]
    have h1 : (0 : ℝ) < 8 * ((P.cAq : ℝ) + 1) := by linarith
    exact div_pos (by norm_num) h1
  have hRle : R ≤ QMCLeafB.BallM2.rSliver := by
    rw [hRdef, hdqR, QMCLeafB.BallM2.rSliver]
    have h1 : (24 : ℝ) ≤ 8 * ((P.cAq : ℝ) + 1) := by linarith
    have h3 : (1 : ℝ) / 380000 / (8 * ((P.cAq : ℝ) + 1)) ≤ 1 / 380000 / 24 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 24) h1
    have h4 : (1 : ℝ) / 380000 / 24 = 1 / 9120000 := by norm_num
    rw [h4] at h3
    exact h3
  have hNN : G₁.n * G₁.n = 4 := rfl
  have hbudget := P.hbudget
  rw [hNN] at hbudget
  have hhalve := P.hhalve
  rw [hNN] at hhalve
  refine QMCLeafB.DC35M1.not_shallowCut_of_ball_horizon G₁ t₁ P hn
    (le_of_lt (QMCLeafB.B1D37M5.runParams_rmax_lt_one P hn))
    (X₀ := QMCLeafB.BallM2.Xs) (r := QMCLeafB.BallM2.rSliver)
    (by norm_num [QMCLeafB.BallM2.rSliver]) (ball_hyp_sliver P hdq) ?_
  show (1 : ℝ) < (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf 4
      (2 * (G₁.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
    * (QMCLeafB.EngineIterates.rho0R 4 ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)
    * QMCLeafB.BallM2.rSliver ^ (2 * 4)
  exact criterion_of_budget_halve (2 * (G₁.n : ℚ) ^ 2 + 2 * P.dq ^ 2)
    (by have := P.hdq; positivity) P.K P.m P.rmax P.hrmax R QMCLeafB.BallM2.rSliver
    hRpos hRle hbudget hhalve

#print axioms QMCLeafB.Cp39M5.not_shallowCut_at_sliver

/-! ## 5.  `SepStream`, verbatim, and its refutation at the campaign programme -/

/-- A nonzero rational stream which, at every round below the horizon, places the accumulated centre
on the far side of the relaxation: a supporting-hyperplane certificate.  Character-identical to
`Check_rf38_m1.SepStream`. -/
def SepStream (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- **THE REFUTATION.**  At the campaign programme the leaf's last object is UNSATISFIABLE: no
nonzero rational normal stream — with any selection rule whatsoever — places the accumulated centre
on the far side of the sliver relaxation at every round.  A separating stream gives `ShallowCut`
with `del ≡ 0` (`Bypass35M6.shallowCut_of_separating`), and the sliver body's own campaign-radius
ball refutes `ShallowCut` at every admissible programme (`not_shallowCut_at_sliver`). -/
theorem not_sepStream_campaign
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream Pfam c hc := by
  intro hsep
  exact not_shallowCut_at_sliver P₁ hn₁ dq_sliver
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P₁) hn₁ (c G₁ t₁) (hc G₁ t₁)
      (hsep G₁ t₁ hn₁))

#print axioms QMCLeafB.Cp39M5.not_sepStream_campaign

/-- The same, in existential form: there is no separating stream at the campaign programme. -/
theorem no_sepStream_campaign :
    ¬ ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
        (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
      SepStream Pfam c hc := by
  rintro ⟨c, hc, hsep⟩
  exact not_sepStream_campaign c hc hsep

#print axioms QMCLeafB.Cp39M5.no_sepStream_campaign

/-! ## 6.  The repair: the exact object the leaf consumes, and what it forces

`SepStream` is stronger than what the leaf uses: `solution_of_separating` consumes it only at bracket
points with a bit-`false` verdict.  `SepSlot` is that object.  It gives the leaf
(`solution_of_sepSlot`) — and at the campaign programme it is satisfiable only if the bit reads
`true` at the sliver, because the sliver body is unseparable. -/

/-- **The repaired object.**  Separation is demanded only where the leaf uses it: on the oracle
bracket, at bit-`false` points.  A strict weakening of `SepStream`. -/
def SepSlot (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    ((t : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- The repaired object gives the all-cut identity at the bit-`false` bracket points. -/
theorem selfRecG_of_sepSlot
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot o P c hc) : QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G) hn (c G t) (hc G t)
      (h G t hn hlo hlt hb))

#print axioms QMCLeafB.Cp39M5.selfRecG_of_sepSlot

/-- **THE LEAF FROM THE REPAIRED OBJECT.**  `FinishLine.SolutionStatement` from the `Poly` bit, the
count, the top slice, the upper slot and `SepSlot` — the last binder is the only analytic one. -/
theorem solution_of_sepSlot
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot o P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_sepSlot o P c hc h)

#print axioms QMCLeafB.Cp39M5.solution_of_sepSlot

/-- **THE PROGRAMME CHANGE IS FORCED.**  At every programme family whose tolerance at the sliver is
the campaign's, the repaired object is satisfiable only if the verdict bit reads `true` at `(G₁,t₁)`:
there is no separating direction there at all.  So the repair is a change of GATE or BODY, never a
change of the depth schedule. -/
theorem sepSlot_forces_bit_true
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hdq : (P G₁).dq = 1 / 380000)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot o P c hc) : o G₁ t₁ = true := by
  cases hb : o G₁ t₁ with
  | true => rfl
  | false =>
      exact absurd
        (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G₁) hn₁ (c G₁ t₁) (hc G₁ t₁)
          (h G₁ t₁ hn₁ sliver_bracket.1 sliver_bracket.2 hb))
        (not_shallowCut_at_sliver (P G₁) hn₁ hdq)

#print axioms QMCLeafB.Cp39M5.sepSlot_forces_bit_true

/-- At the campaign family: `SepSlot` at `paramsKbc2` forces the campaign bit `true` at the sliver. -/
theorem sepSlot_forces_bit_true_campaign
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot o Pfam c hc) : o G₁ t₁ = true :=
  sepSlot_forces_bit_true o Pfam dq_sliver c hc h

#print axioms QMCLeafB.Cp39M5.sepSlot_forces_bit_true_campaign

/-! ## 7.  The concrete programme: `o33` at `P33`

Everything except `SepSlot` is a programme fact at the campaign bit: the `Poly` bit is `ho33`, the
count is `hKm33`, the top slice is `htop_roundGT`.  So at `(o33, P33)` the repaired object is the
leaf's only gap — and by §6 it is satisfiable only with the bit `true` at the sliver. -/

/-- `P33`'s tolerance at the sliver is the campaign's. -/
theorem P33_dq_sliver : (QMCLeafB.Pbit33.P33 G₁).dq = 1 / 380000 := by
  show QMCLeafB.RundataParams.dqShallow G₁ = 1 / 380000
  rw [← QMCLeafB.UnionShallow.paramsKbc2_dq, QMCLeafB.EmptyBodyM5.dq₁_eq]

#print axioms QMCLeafB.Cp39M5.P33_dq_sliver

/-- `SepSlot` at the campaign bit forces the bit `true` at the sliver. -/
theorem sepSlot_forces_o33_true
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot QMCLeafB.Pbit33.o33 (fun G => QMCLeafB.Pbit33.P33 G) c hc) :
    QMCLeafB.Pbit33.o33 G₁ t₁ = true :=
  sepSlot_forces_bit_true QMCLeafB.Pbit33.o33 (fun G => QMCLeafB.Pbit33.P33 G)
    P33_dq_sliver c hc h

#print axioms QMCLeafB.Cp39M5.sepSlot_forces_o33_true

/-- **THE LEAF AT THE CONCRETE CAMPAIGN PROGRAMME.**  `d9f601e5` from the upper slot and the
repaired separation object — everything else is discharged at `(o33, P33)`. -/
theorem solution_concrete
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : SepSlot QMCLeafB.Pbit33.o33 (fun G => QMCLeafB.Pbit33.P33 G) c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sepSlot QMCLeafB.Pbit33.o33 (fun G => QMCLeafB.Pbit33.P33 G)
    (QMCLeafB.Pbit33.ho33 5 (by norm_num))
    (fun G => by have := QMCLeafB.Pbit33.hKm33 G; omega)
    (fun G t _ hlo hhi => QMCLeafB.ConformanceM8.htop_roundGT (fun G => QMCLeafB.Pbit33.T33 G)
      QMCLeafB.Pbit33.one_le_T33 G t hlo hhi)
    hok c hc h

#print axioms QMCLeafB.Cp39M5.solution_concrete

/-- **The verbatim object is dead at `P33` too** (the family `solution_concrete` runs). -/
theorem not_sepStream_P33
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream (fun G => QMCLeafB.Pbit33.P33 G) c hc := by
  intro hsep
  exact not_shallowCut_at_sliver (QMCLeafB.Pbit33.P33 G₁) hn₁ P33_dq_sliver
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := QMCLeafB.Pbit33.P33 G₁) hn₁
      (c G₁ t₁) (hc G₁ t₁) (hsep G₁ t₁ hn₁))

#print axioms QMCLeafB.Cp39M5.not_sepStream_P33

/-- **THE SHARP FORM OF THE PROGRAMME CHANGE.**  At any programme family with the campaign tolerance,
a bit-`false` verdict at the sliver makes the repaired object UNSATISFIABLE.  So the repair must make
the bit read `true` there (gate) or remove the body (thin/level-set) — nothing else works. -/
theorem not_sepSlot_of_bit_false
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hdq : (P G₁).dq = 1 / 380000) (hb : o G₁ t₁ = false)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepSlot o P c hc := by
  intro h
  rw [sepSlot_forces_bit_true o P hdq c hc h] at hb
  exact Bool.noConfusion hb

#print axioms QMCLeafB.Cp39M5.not_sepSlot_of_bit_false

/-! ## 8.  Summary of the decision

* `not_sepStream_campaign` / `no_sepStream_campaign` — the leaf's last object, verbatim, is FALSE at
  the campaign programme for EVERY nonzero rational normal stream.  Not a bad selection rule: no
  stream at all.
* `not_shallowCut_at_sliver` — the underlying fact is horizon-free: at `(G₁,t₁)`, at every
  `RunParams` with the campaign tolerance, the body's own `hbudget`-radius ball refutes every
  shallow-cut record.  Changing `K`, `m`, `rmax` or `cAq` cannot help.
* `SepSlot` / `solution_of_sepSlot` / `solution_concrete` — the repaired object (bracket ∩
  bit-`false`) closes the leaf at `(o33, P33)` with the upper slot as the only other hypothesis.
* `sepSlot_forces_bit_true` / `sepSlot_forces_o33_true` — even the repaired object forces the bit
  `true` at the sliver, so the programme change is a GATE change (`ok ↔ RelaxMem`) or a BODY change
  (thin / rational-level-set relaxations), not a change of the depth schedule.
-/

end QMCLeafB.Cp39M5


