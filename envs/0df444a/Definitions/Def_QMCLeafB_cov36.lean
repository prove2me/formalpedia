-- Prove2me | Definitions.Def_QMCLeafB_cov36
-- name    : QMCLeafB_cov36
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:32:55.039502+00:00
-- url     : https://prove2.me/theorems/7da1c5e7-781b-4d70-839d-ec01d1cdc1d7
-- title:
--   QMCLeafB cov36
-- statement:
--   # `Check_cov36_m7` — phase 36, member m7, direction `coverage36`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_oklevel
/-
# `Check_cov36_m7` — phase 36, member m7, direction `coverage36`

## The question

The phase-36 plan (FINAL ARCHITECTURE of `results/qmc-tm2-endgame.md`; the coordinator's reading in
the brief) splits the leaf's last duty by the band parameter `Δ` at `G₁`:

* **FAT** (`Δ > 0`, "the whole open band"): the body carries a ball of radius `≈ Δ/6`, and m1's
  radius-free ball/horizon theorem (`DC35M1.not_shallowCut_of_ball_horizon`) forces the bit
  **TRUE**, so `hfalse` is vacuous there;
* **FACE** (`Δ = 0`, "measure-zero"): the body is the segment
  `{Qᵢᵢ = 1+δ/4, Q₀₁+Q₁₀ = −(2+3δ/2)}`, where the all-`false` record is to be built
  (`del ≡ 0` separating/tight cuts).

Both halves are being worked (d1/d4 face, d3 fat).  **Nobody checked that the two halves cover the
band.**  This file checks it.  The answer is NO — and the gap is not the obvious one.

## The missing bound: the fat criterion needs a ball ABOVE a horizon radius

m1's criterion is not "positive content" but `pConst · r^(2N) > 1`, where
`pConst = det A₀ · rho0R(N, rmax)^(K·m)` and `r` is the radius of a ball **inside** the body.  The
library's content statements are all one-sided: `DregM6.dreg_band` says the *campaign* radius
`dq/24` does not fit, m3 bounds cube content, m8 bounds parallelotope content — nothing bounds the
inradius **from above**, which is what decides whether m1's criterion can fire at all.

§1 supplies it.  At the band the two objective constraints are `−(2+3δ/2) ≤ frob` and
`frob ≤ −(2+3δ/2) + Δ`, while the probe matrix `!![0,r/2;r/2,0]` sits at Frobenius distance
`r/√2 ≤ r` from the centre and raises `frob` by exactly `r` (`probe_norm`, `probe_frob`).  Hence
**`ball_radius_le_slack : r ≤ Δ`** — a ball inside the band body has radius at most `Δ`.

## What is machine-checked here

| # | theorem | content |
|---|---------|---------|
| 1 | `ball_radius_le_slack` | the inradius bound `r ≤ Δ` |
| 2 | `no_horizon_ball` | on `{pConst·Δ^8 ≤ 1}` **m1's fat criterion is unsatisfiable**: no centre, no radius, no ball.  The FAT half is provably silent there, not merely unproven |
| 3 | `no_campaign_ball` | the campaign-radius ball (`BallM2.no_runParts_of_ball`) does not fit either, on the whole collar at once — `DregM6.dreg_band`'s ball-freeness extended off its narrow band, and to the face |
| 4 | `cubic_thin` | any axis-aligned cube in the body has `ℓ/2 ≤ Δ`, hence m3's sharp cube threshold (`(ℓ/2)^{n·n} ≤ volPot A₀·2^{-K}`) can only bite for `Δ^{n·n} > volPot A₀·2^{-K}` |
| 5 | `exists_collar` | the collar is **inhabited inside the band**: a rational `0 < Δ < min(d0, dq/24)` with `pConst·Δ^8 ≤ 1`.  Archimedes supplies it, so no numeral with `1.6·10⁵` digits is ever written |
| 6 | `coverage_gap`, `collar_dossier` | at that `Δ`: body **nonempty** (`DregM6.not_bodyEmpty`), point **interior** (`−Rq ≤ t < 0`), **off the face** (`Δ ≠ 0`), and all three banked record-refuting mechanisms silent |
| 7 | `dichotomy_false` | the negated split: "at every interior band point with nonempty body, either the fat criterion has a ball witness or `Δ = 0`" is **FALSE** |
| 8 | `body_mono_level`, `face_body_subset` | `relaxBodyLE` is monotone in the level, so `body(0) ⊆ body(Δ)` — the monotonicity runs the WRONG way for the repair (see below) |
| 9 | `face_no_ball`, `face_no_cube` | at `Δ = 0` the body is ball-free and cube-free at EVERY scale, so the whole volume class of obstructions is vacuous on the face — nothing about the face's content can obstruct the record |
| 10 | `Km_le`, `detA0_le_one`, `rho_le_two`, `pConst_le` | a **certified** size: `K·m ≤ 23003136`, `det A₀ ≤ 1`, `rho0R ≤ 2`, hence `pConst ≤ 2^23003136` |
| 11 | `collar_of_pow_bound` | a usable explicit threshold: any `Δ` with `Δ^8·2^23003136 ≤ 1` is a collar point (`pConst·Δ^8 ≤ 1`), e.g. `Δ = 2^(-2875392) ≈ 10^(-865500)` |

## The numbers (computed, not machine-checked in Lean; inputs pin everything)

`bitCost 2 = 4`, `mHalve 4 = 256`, `Kbc2 256 G₁ = 256·9·(4+1+4+1+2+27) = 89856`,
`K·m = 89856·256 = 23 003 136`; `rmax = rmaxOf 4 = 1/16`;
`rho0R 4 (1/16) = 253125·16^8/(3·65^8) = 1.1372784082…`; `det A₀ = (8+2dq²)^{-4} ≈ 2.44·10⁻⁴`.
Hence `log₁₀ pConst ≈ 1 285 108` and **`pConst^(-1/8) ≈ 3·10⁻¹⁶⁰⁶³⁹`**.  So the certified
volume-silent collar is `Δ ≲ 3·10⁻¹⁶⁰⁶³⁹`, while the campaign band top is `1/18240000 ≈ 5.5·10⁻⁸`:
the FAT half covers all but a sliver of relative width `~10⁻¹⁶⁰⁶³¹`.  (The brief's "`10⁻¹⁴⁰⁰⁰⁰`" is
the same order — a coarse estimate of the same quantity.)

## The consequence for the phase

The gap is astronomically thin, so this is **not** an alarm about the plan's quantitative margins —
it is a statement about the *shape* of the case analysis, and it has one sharp corollary:

> **The face record does not cover the collar, and monotonicity works against extending it.**
> `face_body_subset` gives `body(0) ⊆ body(Δ)`.  A `del ≡ 0` record's content is that the run's
> accumulated centre is **outside** the body at every round (`ShallowCut` with a supporting/separating
> normal).  A *larger* body is *harder* to be outside of.  So a face record implies nothing about the
> collar; on the contrary, a collar record would imply a face record.  The face is the EASY end of the
> record branch, not the hard one.

So one of two things must be added to the plan, and the brief says neither:

* **(a)** state the FAT half on its true domain `{pConst·r_body^(2N) > 1}` and hand the collar to the
  record — which then needs a *strictly stronger* record theorem than the face's, uniform in
  `Δ ∈ [0, pConst^(-1/8)]`; or
* **(b)** make the bit true on the collar by a route that is not volume-limited — i.e. a landing
  theorem at the top face (`BH35M5.ReachTop` class: `topGate_iff_mem` accepts the band's own
  top-edge member `XQ Δ` for every `Δ ≥ 0`, `dreg_topGate_inhabited`), which is exactly the
  obligation the face record was introduced to avoid.

A third possibility — that the collar is empty because some *other* banked result forces the bit true
there — is excluded for the pinched-sound gate by `BH35M5.dreg_bit_complete_fails` (the bit is
`false` at every `Δ < d0` for a pinched-sound register) and is not supplied for the repaired gate by
anything in the shelf.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration; published `Definitions.Def_QMCLeafB_*` imports only.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Cov36M7

open QuantumMaxCutEnergy

/-! ## 0.  The band's datum at `G₁`, and the two level identities in `ℝ` -/

/-- The campaign's two-vertex input (`Rq = 2`, one edge of weight `1`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.DregM6.G₁

/-- The campaign's parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.DregM6.P₁

/-- The band tolerance `δ = P₁.dq = 1/380000`. -/
abbrev d0 : ℚ := 1 / 380000

theorem dq_r : ((P₁.dq : ℚ) : ℝ) = 1 / 380000 := QMCLeafB.DregM6.dq_r

theorem cAq_eq : P₁.cAq = 2 := QMCLeafB.DregM6.cAq_eq

theorem n_G₁ : G₁.n = 2 := rfl

theorem two_le_n : 2 ≤ G₁.n := by rw [n_G₁]

/-- The body's level `u = t − Rq/40000` at the band point `t = tStar + Δ`. -/
theorem u_r (Δ : ℚ) :
    (((QMCLeafB.DregM6.tStar + Δ : ℚ)) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 2 * (1 / 380000 : ℝ)) + (Δ : ℝ) :=
  QMCLeafB.DregM6.thresh_eq Δ

/-- The level test's ceiling `u + δ/2` at the band point, in closed form. -/
theorem level_r (Δ : ℚ) :
    ((((QMCLeafB.DregM6.tStar + Δ : ℚ)) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
      + ((P₁.dq : ℚ) : ℝ) / 2
      = -(2 + 3 * (1 / 380000 : ℝ) / 2) + (Δ : ℝ) := by
  rw [u_r, dq_r]; ring

#print axioms QMCLeafB.Cov36M7.level_r

/-! ## 1.  The inradius bound: a ball in the band body has `√2·r ≤ Δ`

The body's two objective constraints are
`frob ≥ −(2 + 3δ/2)` (`DregM6.frob_floor`, the real `n = 2` floor, orthogonal PSD direction)
and `frob ≤ u + δ/2 = −(2 + 3δ/2) + Δ`.  A Frobenius step of length `r` in the direction
`!![0,1;1,0]/√2` raises `frob` by exactly `√2·r`, so a ball of radius `r` cannot fit unless `√2r ≤ Δ`.
This is the missing one-sided bound: it is what converts "the body has positive content" into
"the body has a ball the horizon can see". -/

/-- `unflat` is additive (flat coordinates are a linear chart). -/
theorem unflat_add {n : ℕ} (y z : Fin (n * n) → ℝ) :
    QMCLeafB.Boundary.unflat (y + z)
      = QMCLeafB.Boundary.unflat y + QMCLeafB.Boundary.unflat z := by
  ext i j
  simp [QMCLeafB.Boundary.unflat, Matrix.add_apply, Pi.add_apply]

#print axioms QMCLeafB.Cov36M7.unflat_add

/-- `frob` is additive in the matrix argument. -/
theorem frob_add {n : ℕ} (A X Y : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob A (X + Y)
      = QMCLeafB.BallFloor.frob A X + QMCLeafB.BallFloor.frob A Y := by
  simp only [QMCLeafB.BallFloor.frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

#print axioms QMCLeafB.Cov36M7.frob_add

/-- **The probe.**  At `G₁` (`wMatrix = !![0,1;1,0]`) the probe matrix
`Y = !![0, r/2; r/2, 0]` has `‖Y‖² = r²/2 ≤ r²` and `frob A Y = r` — so a Frobenius step of *length*
`r` in this direction raises the objective by exactly `r`, at half the norm budget.  (Using `r/2`
instead of `r/√2` keeps the arithmetic rational; the bound below is correspondingly sharper:
`r ≤ Δ`, not `√2·r ≤ Δ`.) -/
theorem probe_norm (r : ℝ) :
    (∑ k : Fin (2 * 2),
        (QMCLeafB.AnswerProducer.flat
          (!![(0 : ℝ), r / 2; r / 2, 0]) : Fin (2 * 2) → ℝ) k ^ 2) = r ^ 2 / 2 := by
  rw [QMCLeafB.Boundary.sum_sq_flat]
  simp [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

#print axioms QMCLeafB.Cov36M7.probe_norm

theorem probe_norm_le (r : ℝ) :
    (∑ k : Fin (2 * 2),
        (QMCLeafB.AnswerProducer.flat
          (!![(0 : ℝ), r / 2; r / 2, 0]) : Fin (2 * 2) → ℝ) k ^ 2) ≤ r ^ 2 := by
  rw [probe_norm]; nlinarith [sq_nonneg r]

#print axioms QMCLeafB.Cov36M7.probe_norm_le

theorem probe_frob (r : ℝ) :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁)
      (!![(0 : ℝ), r / 2; r / 2, 0]) = r := by
  rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two,
    QMCLeafB.OkLevelM5.wMatrix_G₁]
  simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]

#print axioms QMCLeafB.Cov36M7.probe_frob

/-! ## 1.  THE INRADIUS BOUND

The band body at `Δ` satisfies `−(2+3δ/2) ≤ frob ≤ −(2+3δ/2) + Δ`, while a Frobenius step of
length `r` in the `!![0,1;1,0]` direction raises `frob` by exactly `r`.  Hence a ball of radius `r`
inside the body forces `r ≤ Δ`.  This is the one-sided bound the phase-36 split was missing: the
banked content statements (`DregM6.dreg_band`'s campaign-radius ball-freeness, m8's parallelotope,
m3's cube) all say "the body has no content ABOVE a threshold"; none of them bounds the content
FROM ABOVE, which is what decides whether m1's fat criterion can fire. -/

/-- **The inradius bound.**  If a ball of radius `r > 0` (in flat coordinates) around `flat X₀`
sits inside the band's relaxation at `t = tStar + Δ`, then `r ≤ Δ`. -/
theorem ball_radius_le_slack {Δ : ℚ} (hΔ : 0 ≤ Δ)
    {X₀ : Matrix (Fin 2) (Fin 2) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) :
    r ≤ (Δ : ℝ) := by
  -- the centre is a body point
  have hcentre : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      ((((QMCLeafB.DregM6.tStar + Δ : ℚ)) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) ((P₁.dq : ℚ) : ℝ) X₀ := by
    have h0 : (∑ i : Fin (2 * 2), (0 : Fin (2 * 2) → ℝ) i ^ 2) ≤ r ^ 2 := by
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      positivity
    have := (hball 0 h0).1
    rwa [zero_add, QMCLeafB.Boundary.unflat_flat] at this
  have hfloor : -(2 + 3 * ((P₁.dq : ℚ) : ℝ) / 2)
      ≤ QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X₀ :=
    QMCLeafB.DregM6.frob_floor hcentre
  -- the probe direction
  have hmemball : (QMCLeafB.AnswerProducer.flat
        (!![(0 : ℝ), r / 2; r / 2, 0]) + QMCLeafB.AnswerProducer.flat X₀)
      ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁ :=
    hball _ (probe_norm_le r)
  have hbody := hmemball.1
  rw [unflat_add, QMCLeafB.Boundary.unflat_flat, QMCLeafB.Boundary.unflat_flat] at hbody
  have hle := hbody.2.2
  rw [frob_add, probe_frob] at hle
  have hlev := level_r Δ
  rw [dq_r] at hlev hfloor hle
  linarith

#print axioms QMCLeafB.Cov36M7.ball_radius_le_slack

/-! ## 2.  m1's fat criterion is SILENT on the volume-thin collar

`DC35M1.not_shallowCut_of_ball_horizon` fires when a ball of radius `r > 0` lies in the relaxation
and `1 < det A₀ · rho0R(N, rmax)^(K·m) · r^(2N)`.  §1 bounds `r ≤ Δ`, so on the collar
`{Δ : pConst·Δ^8 ≤ 1}` there is no `r`, no centre and no ball satisfying that hypothesis: the
volume/visit route to "the bit is TRUE on the open band" cannot be instantiated. -/

/-- The determinant-horizon constant of m1's criterion, at `paramsKbc2/G₁`. -/
noncomputable def pConst : ℝ :=
  (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G₁.n * G₁.n)
      (2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2))).det
    * (QMCLeafB.EngineIterates.rho0R (G₁.n * G₁.n) ((P₁.rmax : ℚ) : ℝ)) ^ (P₁.K * P₁.m)

theorem pConst_pos : 0 < pConst := by
  have hN : 2 ≤ G₁.n * G₁.n := by rw [n_G₁]; norm_num
  have hNm : (0 : ℚ) < 2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2 := by
    have := P₁.hdq; positivity
  refine mul_pos ?_ (pow_pos (QMCLeafB.EngineIterates.rho0R_pos hN ?_) _)
  · exact (QMCLeafB.Boundary.initShapeOf_cast_posDef hNm).det_pos
  · have := P₁.hrmax; positivity

#print axioms QMCLeafB.Cov36M7.pConst_pos

/-- **The fat criterion cannot fire on the collar.**  No ball in the band's relaxation satisfies
`1 < pConst · r^8` when `pConst · Δ^8 ≤ 1`. -/
theorem no_horizon_ball {Δ : ℚ} (hΔ : 0 ≤ Δ)
    {X₀ : Matrix (Fin 2) (Fin 2) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁)
    (hsmall : pConst * (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) ≤ 1) :
    ¬ (1 < pConst * r ^ (2 * (G₁.n * G₁.n))) := by
  have hrd : r ≤ (Δ : ℝ) := ball_radius_le_slack hΔ hr hball
  have hp8 : r ^ (2 * (G₁.n * G₁.n)) ≤ (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) :=
    pow_le_pow_left₀ hr.le hrd _
  have := mul_le_mul_of_nonneg_left hp8 pConst_pos.le
  linarith

#print axioms QMCLeafB.Cov36M7.no_horizon_ball

/-! ## 3.  THE COVERAGE GAP: the collar is inhabited inside the band

`pConst` is astronomically large at `paramsKbc2/G₁`, so the collar `{Δ : pConst·Δ^8 ≤ 1}` is
astronomically close to `0`.  Nothing below evaluates `pConst`: Archimedes produces a rational `Δ`
inside the collar and inside the band at once.  (An explicit numeral would need on the order of
`10^5`–`10^6` decimal digits — which is exactly why the FAT half's phrase "the whole open band"
cannot be read as a `∀` over `Δ`.) -/

/-- **The collar is inhabited inside the band.**  There is a rational `0 < Δ < d0` with
`pConst·Δ^8 ≤ 1`. -/
theorem exists_collar :
    ∃ Δ : ℚ, 0 < Δ ∧ Δ < d0
      ∧ (Δ : ℝ) < ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1))
      ∧ pConst * (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) ≤ 1 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, pConst ≤ (N : ℝ) := ⟨⌈pConst⌉₊, Nat.le_ceil pConst⟩
  set m : ℕ := max N 9120001 with hm
  have hmN : pConst ≤ (m : ℝ) := le_trans hN (by exact_mod_cast Nat.le_max_left N 9120001)
  have hm380 : (9120001 : ℕ) ≤ m := Nat.le_max_right N 9120001
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have h1 : (1 : ℕ) ≤ m := le_trans (by norm_num) hm380
    exact_mod_cast h1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmposQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hmpos
  have hexp : 2 * (G₁.n * G₁.n) = 8 := by rw [n_G₁]
  have hpow : (m : ℝ) ≤ (m : ℝ) ^ (2 * (G₁.n * G₁.n)) := by
    rw [hexp]
    exact le_self_pow₀ hm1 (by norm_num)
  refine ⟨1 / (m : ℚ), ?_, ?_, ?_, ?_⟩
  · exact div_pos one_pos hmposQ
  · have h380' : (380001 : ℕ) ≤ m := le_trans (by norm_num) hm380
    have h380 : (380001 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h380'
    have hle : (1 : ℚ) / (m : ℚ) ≤ 1 / 380001 :=
      one_div_le_one_div_of_le (by norm_num) h380
    have hlt : (1 : ℚ) / 380001 < 1 / 380000 := by norm_num
    exact lt_of_le_of_lt hle hlt
  · have hbigQ : (9120001 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm380
    have hle2 : (1 : ℚ) / (m : ℚ) ≤ 1 / 9120001 :=
      one_div_le_one_div_of_le (by norm_num) hbigQ
    have hlt2 : (1 : ℚ) / 9120001 < 1 / 9120000 := by norm_num
    have hQ : (1 : ℚ) / (m : ℚ) < 1 / 9120000 := lt_of_le_of_lt hle2 hlt2
    have hR : (((1 : ℚ) / (m : ℚ) : ℚ) : ℝ) < (((1 : ℚ) / 9120000 : ℚ) : ℝ) := by
      exact_mod_cast hQ
    have hEq : ((((1 : ℚ) / 9120000 : ℚ)) : ℝ)
        = ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)) := by
      rw [dq_r, cAq_eq]; norm_num
    linarith [hR, hEq]
  · have hcast : (((1 : ℚ) / (m : ℚ) : ℚ) : ℝ) = 1 / (m : ℝ) := by push_cast; ring
    rw [hcast, hexp, div_pow, one_pow, mul_one_div, div_le_iff₀ (by positivity), one_mul]
    exact le_trans hmN hpow

#print axioms QMCLeafB.Cov36M7.exists_collar

/-- The band point `tStar + Δ` sits in the leaf's interior bracket `[−Rq, 0]` for every
`Δ ∈ (0, d0)`. -/
theorem band_in_bracket {Δ : ℚ} (hΔ0 : 0 < Δ) (hΔ : Δ < d0) :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ QMCLeafB.DregM6.tStar + Δ
      ∧ QMCLeafB.DregM6.tStar + Δ ≤ 0 := by
  have hRq : QMCLeafB.EngineRuntime.Rq G₁ = 2 := QMCLeafB.DregM6.Rq_eq
  have hdq : d0 = 1 / 380000 := rfl
  rw [hdq] at hΔ
  constructor
  · unfold QMCLeafB.DregM6.tStar
    rw [hRq]; linarith
  · unfold QMCLeafB.DregM6.tStar
    linarith

#print axioms QMCLeafB.Cov36M7.band_in_bracket

/-- **THE COVERAGE GAP.**  There is a rational `Δ` with `0 < Δ < d0` such that, at
`(G₁, tStar + Δ)`:

* the relaxed body is **NONEMPTY** (`DregM6.not_bodyEmpty`);
* the point is in the interior bracket `[−Rq, 0]` (`band_in_bracket`);
* `Δ ≠ 0`, i.e. the point is **NOT on the measure-zero face**;
* **m1's fat criterion is unsatisfiable there** (`no_horizon_ball`): no centre and no radius `r`
  give a ball inside the relaxation with `1 < pConst·r^8`.

So the phase-36 dichotomy "FAT (bit true, volume route) `∨` FACE (`Δ = 0`, record)" does not cover
the band: this point is in neither half.  (The collar is where BOTH banked pairwise mechanisms are
provably silent; the record there is neither refuted nor built.) -/
theorem coverage_gap :
    ∃ Δ : ℚ, 0 < Δ ∧ Δ < d0
      ∧ ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (QMCLeafB.DregM6.tStar + Δ) P₁
      ∧ (-QMCLeafB.EngineRuntime.Rq G₁ ≤ QMCLeafB.DregM6.tStar + Δ
          ∧ QMCLeafB.DregM6.tStar + Δ ≤ 0)
      ∧ Δ ≠ 0
      ∧ (∀ (X₀ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ), 0 < r →
          (∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
            (y + QMCLeafB.AnswerProducer.flat X₀)
              ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) →
          ¬ (1 < pConst * r ^ (2 * (G₁.n * G₁.n)))) := by
  obtain ⟨Δ, hΔ0, hΔd, hΔr, hsmall⟩ := exists_collar
  refine ⟨Δ, hΔ0, hΔd, ?_, band_in_bracket hΔ0 hΔd, ?_, ?_⟩
  · have hΔ0R : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ0.le
    refine QMCLeafB.DregM6.not_bodyEmpty Δ hΔ0R ?_
    have h2 : (Δ : ℝ) < (d0 : ℝ) := by exact_mod_cast hΔd
    have h3 : ((d0 : ℚ) : ℝ) = 1 / 380000 := by norm_num [d0]
    rw [h3] at h2
    linarith
  · intro h
    rw [h] at hΔ0
    exact lt_irrefl (0 : ℚ) hΔ0
  · intro X₀ r hr hball
    exact no_horizon_ball hΔ0.le hr hball hsmall

#print axioms QMCLeafB.Cov36M7.coverage_gap

/-- **THE DICHOTOMY IS FALSE.**  The exact statement the phase-36 plan needs — "at every interior
band point with nonempty body, either the fat criterion has a ball witness, or `Δ = 0`" — is
refuted. -/
theorem dichotomy_false :
    ¬ (∀ Δ : ℚ, 0 ≤ Δ → Δ < d0 →
        ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (QMCLeafB.DregM6.tStar + Δ) P₁ →
        (∃ (X₀ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ), 0 < r
            ∧ (∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
                (y + QMCLeafB.AnswerProducer.flat X₀)
                  ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁)
            ∧ 1 < pConst * r ^ (2 * (G₁.n * G₁.n)))
          ∨ Δ = 0) := by
  intro H
  obtain ⟨Δ, hΔ0, hΔd, hne, _hb, hΔne, hno⟩ := coverage_gap
  rcases H Δ hΔ0.le hΔd hne with ⟨X₀, r, hr, hball, hbig⟩ | h0
  · exact hno X₀ r hr hball hbig
  · exact hΔne h0

#print axioms QMCLeafB.Cov36M7.dichotomy_false

/-- A ball inclusion converts to the pointwise form `ball_radius_le_slack` consumes. -/
theorem subset_ball_hyp {Δ : ℚ} {X₀ : Matrix (Fin 2) (Fin 2) ℝ} {r : ℝ}
    (hsub : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) :
    ∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁ := by
  intro y hy
  refine hsub ?_
  simpa [QMCLeafB.Boundary.eucBallF] using hy

#print axioms QMCLeafB.Cov36M7.subset_ball_hyp

/-- **The campaign-ball route is silent on the collar too.**  No ball of the campaign radius
`dq/(8(cA+1))` fits in the band's relaxation once `Δ` is below that radius — so
`BallM2.no_runParts_of_ball` (phase 24's workhorse, and the `hC`/`hbit` confinement of phases 31/34)
cannot be instantiated there either.  `DregM6.dreg_band` proves this for `Δ ≤ 1/18240000`; the
inradius bound proves it on the whole collar at once, including the face `Δ = 0`. -/
theorem no_campaign_ball {Δ : ℚ} (hΔ0 : 0 ≤ Δ)
    (hΔr : (Δ : ℝ) < ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1))) :
    ∀ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
      ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
            (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
          ⊆ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) := by
  intro X₀ hsub
  have hcA : (0 : ℝ) ≤ ((P₁.cAq : ℚ) : ℝ) := by exact_mod_cast P₁.hcAq
  have hdq : (0 : ℝ) < ((P₁.dq : ℚ) : ℝ) := by exact_mod_cast P₁.hdq
  have hden : (0 : ℝ) < 8 * (((P₁.cAq : ℚ) : ℝ) + 1) := by linarith
  have hr : (0 : ℝ) < ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)) :=
    div_pos hdq hden
  have := ball_radius_le_slack hΔ0 hr (subset_ball_hyp hsub)
  linarith

#print axioms QMCLeafB.Cov36M7.no_campaign_ball

/-- **The cube route is silent on the collar too.**  If an axis-aligned cube of side `ℓ` (in flat
coordinates) sits in the band's relaxation, then `ℓ/2 ≤ Δ`: a cube of side `ℓ` contains the ball of
radius `ℓ/2`, and §1 bounds the inradius by `Δ`.  Hence m3's sharp cube threshold
(`Falsify35bM3.cube_threshold_of_bodyRec` forces `(ℓ/2)^(n·n) ≤ volPot A₀ · (1/2)^K`) can only bite
for `Δ^(n·n) > volPot A₀ · (1/2)^K`. -/
theorem cubic_thin {Δ : ℚ} (hΔ0 : 0 ≤ Δ) {c : Fin (2 * 2) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : ∀ y : Fin (2 * 2) → ℝ, (∀ i, |y i| ≤ ℓ / 2) →
      (y + c) ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) :
    ℓ / 2 ≤ (Δ : ℝ) := by
  have hr : (0 : ℝ) < ℓ / 2 := by linarith
  refine ball_radius_le_slack (X₀ := QMCLeafB.Boundary.unflat c) hΔ0 hr ?_
  intro y hy
  rw [QMCLeafB.Boundary.flat_unflat]
  refine hcube y ?_
  intro i
  have h1 : (y i) ^ 2 ≤ ∑ j, (y j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (y j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq (le_trans h1 hy) (by linarith)

#print axioms QMCLeafB.Cov36M7.cubic_thin

/-- **THE COLLAR DOSSIER.**  There is a band point which is interior, nonempty, off the face, and at
which ALL THREE banked record-refuting mechanisms are provably silent:

* m1's radius-free ball/horizon criterion (`no_horizon_ball`);
* the campaign-radius ball of `BallM2.no_runParts_of_ball` (`no_campaign_ball`);
* m3's/m8's content thresholds, via `cubic_thin` (`ℓ/2 ≤ Δ` for any cube in the body).

So at this point the record is neither refuted nor supplied by the banked machinery, and the bit is
not forced true: it is exactly the class the phase-36 split leaves unassigned. -/
theorem collar_dossier :
    ∃ Δ : ℚ, 0 < Δ ∧ Δ < d0
      ∧ (Δ : ℝ) < ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1))
      ∧ ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (QMCLeafB.DregM6.tStar + Δ) P₁
      ∧ (-QMCLeafB.EngineRuntime.Rq G₁ ≤ QMCLeafB.DregM6.tStar + Δ
          ∧ QMCLeafB.DregM6.tStar + Δ ≤ 0)
      ∧ Δ ≠ 0
      ∧ (∀ (X₀ : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ), 0 < r →
          (∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
            (y + QMCLeafB.AnswerProducer.flat X₀)
              ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) →
          ¬ (1 < pConst * r ^ (2 * (G₁.n * G₁.n))))
      ∧ (∀ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
          ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
                (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
              ⊆ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁))
      ∧ (∀ (c : Fin (2 * 2) → ℝ) (ℓ : ℝ), 0 < ℓ →
          (∀ y : Fin (2 * 2) → ℝ, (∀ i, |y i| ≤ ℓ / 2) →
            (y + c) ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + Δ) P₁) →
          ℓ / 2 ≤ (Δ : ℝ)) := by
  obtain ⟨Δ, hΔ0, hΔd, hΔr, hsmall⟩ := exists_collar
  have hΔ0R : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ0.le
  have hne : ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (QMCLeafB.DregM6.tStar + Δ) P₁ := by
    refine QMCLeafB.DregM6.not_bodyEmpty Δ hΔ0R ?_
    have h2 : (Δ : ℝ) < (d0 : ℝ) := by exact_mod_cast hΔd
    have h3 : ((d0 : ℚ) : ℝ) = 1 / 380000 := by norm_num [d0]
    rw [h3] at h2
    linarith
  exact ⟨Δ, hΔ0, hΔd, hΔr, hne, band_in_bracket hΔ0 hΔd, by
      (intro h; rw [h] at hΔ0; exact lt_irrefl (0 : ℚ) hΔ0),
    fun X₀ r hr hball => no_horizon_ball hΔ0.le hr hball hsmall,
    fun X₀ => no_campaign_ball hΔ0.le hΔr X₀,
    fun c ℓ hℓ hcube => cubic_thin hΔ0.le hℓ hcube⟩

#print axioms QMCLeafB.Cov36M7.collar_dossier

/-! ## 4.  The repair's membership side: the body is monotone in the level

The collar's `Δ > 0` bodies CONTAIN the `Δ = 0` body, because `relaxBodyLE` only weakens as the level
`u` rises.  So the face is the *hardest* instance of the collar: any face record that uses only the
separating geometry (m6's `shallowCut_of_separating`, m2's `bodyRec_of_tight`/`shallowCut_of_tight`)
transfers to the whole collar, while one that uses the face's degeneracy does not.  Conversely the
membership side of a `topGate`-style landing at the face transfers upward for free. -/

/-- `relaxBodyLE` is monotone in the level. -/
theorem body_mono_level {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} {u u' : ℝ} (h : u ≤ u')
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE A u' δ X :=
  ⟨hX.1, hX.2.1, le_trans hX.2.2 (by linarith)⟩

#print axioms QMCLeafB.Cov36M7.body_mono_level

/-- At the band the level rises with `Δ`, so the face body is contained in every collar body. -/
theorem face_body_subset {Δ : ℚ} (hΔ : 0 ≤ Δ) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      ((((QMCLeafB.DregM6.tStar + 0 : ℚ)) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) ((P₁.dq : ℚ) : ℝ) X) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      ((((QMCLeafB.DregM6.tStar + Δ : ℚ)) : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) ((P₁.dq : ℚ) : ℝ) X := by
  have hΔR : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  refine body_mono_level ?_ hX
  have h1 := u_r 0
  have h2 := u_r Δ
  linarith

#print axioms QMCLeafB.Cov36M7.face_body_subset

/-! ## 5.  The face `Δ = 0` is ball-free and cube-free at EVERY scale

The inradius bound at `Δ = 0` says a ball in the face body has radius `≤ 0`, and `cubic_thin` says a
cube in it has side `≤ 0`.  So the whole volume class of obstructions (m1's horizon ball, the
campaign ball, m3's cube, m8's parallelotope) is VACUOUS on the face, at every scale and not only at
the campaign's.  This is the sharpest possible statement of why the face record is unrefuted: nothing
about the face's *content* can obstruct it, and the face is the only band point where that is so. -/

/-- **No ball of positive radius sits in the face body.** -/
theorem face_no_ball {X₀ : Matrix (Fin 2) (Fin 2) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + 0) P₁) :
    False := by
  have h := ball_radius_le_slack (Δ := 0) le_rfl hr hball
  have h0 : ((0 : ℚ) : ℝ) = 0 := by norm_num
  rw [h0] at h
  linarith

#print axioms QMCLeafB.Cov36M7.face_no_ball

/-- **No cube of positive side sits in the face body.** -/
theorem face_no_cube {c : Fin (2 * 2) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : ∀ y : Fin (2 * 2) → ℝ, (∀ i, |y i| ≤ ℓ / 2) →
      (y + c) ∈ QMCLeafB.BallM2.runBall G₁ (QMCLeafB.DregM6.tStar + 0) P₁) :
    False := by
  have h := cubic_thin (Δ := 0) le_rfl hℓ hcube
  have h0 : ((0 : ℚ) : ℝ) = 0 := by norm_num
  rw [h0] at h
  linarith

#print axioms QMCLeafB.Cov36M7.face_no_cube

/-! ## 6.  A certified upper bound on `pConst`: the collar's thinness is a THEOREM

§3 produced a collar point by Archimedes, which needs nothing about the size of `pConst`.  This
section certifies the size, so that a consumer can write an explicit threshold if they want one:
`pConst ≤ 2^23003136`, `2^23003136 ≈ 10^6924000`, hence `pConst^(-1/8) ≥ 2^(-2875392) ≈ 10^(-865500)`
and every `Δ ≤ 2^(-2875392)` certainly lies in the collar.  (The true value is `pConst ≈ 10^1285108`,
so this is a deliberately crude certificate.) -/

/-- `mHalve 4 = mOf 4 = 16·16 = 256`. -/
theorem mHalve_four : QMCLeafB.HalvePerG.mHalve 4 = 256 := by
  rw [QMCLeafB.HalvePerG.mHalve_eq_mOf 4 (by norm_num)]
  unfold QMCLeafB.RundataHalving.mOf
  norm_num

#print axioms QMCLeafB.Cov36M7.mHalve_four

/-- `bitCost 2 = 4` (from `Nat.size_le`: `n.size ≤ k ↔ n < 2^k`). -/
theorem bitCost_two : QMCLeafB.Hspec.bitCost 2 ≤ 4 := by
  unfold QMCLeafB.Hspec.bitCost
  have h1 : Nat.size (2 : ℚ).num.natAbs ≤ 2 := by
    rw [Nat.size_le]; norm_num
  have h2 : Nat.size (2 : ℚ).den ≤ 1 := by
    rw [Nat.size_le]; norm_num
  omega

#print axioms QMCLeafB.Cov36M7.bitCost_two

/-- The campaign's round count at `G₁`: `K·m = 89856·256 = 23003136`. -/
theorem Km_le : P₁.K * P₁.m ≤ 23003136 := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K, QMCLeafB.UnionShallow.paramsKbc2_m]
  unfold QMCLeafB.UnionShallow.Kbc2
  rw [show G₁.n * G₁.n = 4 from rfl, mHalve_four, show G₁.n = 2 from rfl,
    QMCLeafB.DregM6.Rq_eq]
  have hb := bitCost_two
  nlinarith [hb]

#print axioms QMCLeafB.Cov36M7.Km_le

/-- The engine's initial determinant at `G₁` is at most `1` (`det A₀ = (2n² + 2dq²)^(-n²)`). -/
theorem detA0_le_one :
    (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G₁.n * G₁.n)
        (2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2))).det ≤ 1 := by
  rw [QMCLeafB.Boundary.castM_initShapeOf, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]
  have hM : (1 : ℝ) ≤ ((2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2 : ℚ) : ℝ) := by
    have := P₁.hdq
    have hn : G₁.n = 2 := rfl
    rw [hn]
    push_cast
    nlinarith [this]
  have hinv : ((2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2 : ℚ) : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hM
  exact pow_le_one₀ (by positivity) hinv

#print axioms QMCLeafB.Cov36M7.detA0_le_one

/-- The per-round determinant factor at `G₁` is below `2` (`rho0R 4 (1/16) = 1.1372784082…`). -/
theorem rho_le_two :
    QMCLeafB.EngineIterates.rho0R (G₁.n * G₁.n) ((P₁.rmax : ℚ) : ℝ) ≤ 2 := by
  have hrmax : P₁.rmax = 1 / 16 := by
    have := QMCLeafB.UnionShallow.paramsShallowKf_rmax
      (Kf := fun G => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G)
      (hK := fun G => QMCLeafB.UnionShallow.shallowKbound_Kbc2 G) (G := G₁)
    rw [this]
    unfold QMCLeafB.RundataHalving.rmaxOf
    norm_num
  rw [hrmax, show G₁.n * G₁.n = 4 from rfl]
  unfold QMCLeafB.EngineIterates.rho0R
  norm_num

#print axioms QMCLeafB.Cov36M7.rho_le_two

/-- **A certified size for the horizon constant.** -/
theorem pConst_le : pConst ≤ 2 ^ 23003136 := by
  have hN : 2 ≤ G₁.n * G₁.n := by rw [show G₁.n = 2 from rfl]; norm_num
  have hrp : (0 : ℝ) ≤ QMCLeafB.EngineIterates.rho0R (G₁.n * G₁.n) ((P₁.rmax : ℚ) : ℝ) :=
    (QMCLeafB.EngineIterates.rho0R_pos hN (by have := P₁.hrmax; positivity)).le
  have h1 : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G₁.n * G₁.n)
      (2 * (G₁.n : ℚ) ^ 2 + 2 * P₁.dq ^ 2))).det
      * (QMCLeafB.EngineIterates.rho0R (G₁.n * G₁.n) ((P₁.rmax : ℚ) : ℝ)) ^ (P₁.K * P₁.m)
      ≤ 1 * 2 ^ (P₁.K * P₁.m) :=
    mul_le_mul detA0_le_one (pow_le_pow_left₀ hrp rho_le_two _) (pow_nonneg hrp _)
      (by norm_num)
  have h2 : (1 : ℝ) * 2 ^ (P₁.K * P₁.m) ≤ 2 ^ 23003136 := by
    rw [one_mul]
    exact pow_le_pow_right₀ (by norm_num) Km_le
  exact le_trans h1 h2

#print axioms QMCLeafB.Cov36M7.pConst_le

/-- **A usable explicit threshold.**  Any rational `Δ` with `Δ^8 · 2^23003136 ≤ 1` is a collar
point (`pConst·Δ^8 ≤ 1`), so `Δ = 2^(-2875392)` — about `10^(-865500)` — is certified to be in
the collar without any evaluation of `pConst`. -/
theorem collar_of_pow_bound {Δ : ℚ}
    (h : (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) * 2 ^ 23003136 ≤ 1) :
    pConst * (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) ≤ 1 := by
  have hp := pConst_le
  have h0 : (0 : ℝ) ≤ (Δ : ℝ) ^ (2 * (G₁.n * G₁.n)) := by
    rw [show 2 * (G₁.n * G₁.n) = 8 from rfl]
    positivity
  nlinarith [hp, h, h0]

#print axioms QMCLeafB.Cov36M7.collar_of_pow_bound

end QMCLeafB.Cov36M7


