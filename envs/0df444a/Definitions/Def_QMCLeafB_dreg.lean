-- Prove2me | Definitions.Def_QMCLeafB_dreg
-- name    : QMCLeafB_dreg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:55:53.554538+00:00
-- url     : https://prove2.me/theorems/142c4496-0d63-455e-beac-2fe19fde77a9
-- title:
--   QMCLeafB dreg
-- statement:
--   # `Check_dreg_m6` — phase 25, member m6, direction d8 (`n2-exact-decision`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thrice
import Definitions.Def_QMCLeafB_ball_m2
/-
# `Check_dreg_m6` — phase 25, member m6, direction d8 (`n2-exact-decision`)

**The question this file machine-decides.**  At a `ThriceM3.ThirdStratum` point (interior, real body
nonempty, no pinched member) the bit is forced `false`, and `BallM2.no_runParts_of_ball` forbids an
all-`false` run at any body that contains the campaign ball `dq/(8(cA+1))`.  The phase-24 conclusion
left exactly one dreg: points whose body is nonempty but **thinner than the campaign ball**.  Is that
dreg empty (branch (a), "empty by design" via the ε/dq split) or real (branches (b)/(c))?

**Answer: it is real, already at `n = 2`, in a `Θ(δ)`-wide interval — and it is not removable by any
slack split.**  At the campaign's own two-vertex input `G₁` (one edge of weight `1`; `Rq = 2`,
`δ = P₁.dq = 1/380000`, `ε = 1/20000`, `cA = 2`, campaign ball radius `δ/24 = 1/9120000`):

* `frob_floor` — the real relaxed body obeys the objective floor `⟪A,X⟫ ≥ −(2 + 3δ/2)` at **every**
  threshold (the `n = 2` real counterpart of `EmptyBodyM5.frob_ge_of_relaxMem`, which is stated for
  *rational* members; the real body needs its own floor because `BodyEmpty` is about `relaxBodyLE`);
* `body_witness` — for every objective slack `Δ ≥ 0` the explicit matrix
  `Xd Δ = !![1+δ/4, −(1+3δ/4)+Δ/2; −(1+3δ/4)+Δ/2, 1+δ/4]` lies in the real body at threshold
  `u = u* + Δ`, `u* = −2 − 2δ` (it has PSD slack exactly `δ/2` and objective value `u + δ/2`);
* `not_pinchFeasible` — no *pinched* member exists there for `Δ < δ`
  (`EmptyBodyM5.frob_ge_of_pinched` floors a pinched member at `−2 − δ/2 > u + δ/2`);
* `mat_ball_free` / `no_ball` — **no ball of the campaign radius fits** for `Δ < δ/24`: every body
  point has objective slack `≤ Δ < δ/24`, and moving a unit-diagonal matrix by a Frobenius ball of
  radius `r` raises `⟪A,X⟫` by `r` (the off-diagonal perturbation `!![0,r/2;r/2,0]` costs `r²/2` of
  Frobenius norm and `r` of objective).  Hence `no_runParts_of_ball`'s hypothesis is **unsatisfiable**
  at these points: the volume obstruction cannot touch them;
* `dreg_interior` / `dreg_stratum_inhabited` — the band is inside the leaf's own interior bracket
  `[−Rq, −Rq/40000)`, so it is not an artefact of a degenerate threshold.

**Design consequence (`bracket_cost`, machine-checked arithmetic).**  The band's bottom sits at
distance `ε` above `−Rq` for *every* admissible `dq`, and its width is `Θ(δ)` — so no ε/dq split
removes it (branch (a) is dead at `n = 2`); removing it needs the *bracket* redesign `t ≥ −Rq + 2δ`,
and that costs `2δ` of threshold, i.e. `2δ = (W/10000)/(9·Rq+1) ≤ W/10000` of the leaf's own slack
budget: a factor `9·Rq+1` inside it.  At `G₁`: `2δ = 1/190000` against `W/10000 = 1/10000`, ratio
exactly `19 = 9·Rq+1`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom cone `[propext, Classical.choice, Quot.sound]` (`#print axioms` at the end of every section).
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.DregM6

open QuantumMaxCutEnergy

/-! ## 0.  The n = 2 datum, at the campaign's own parameters -/

/-- The campaign's two-vertex input, one edge of weight `1` (`abbrev`, so `Fin G₁.n` is `Fin 2`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The campaign's parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

theorem dq_eq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

/-- `dq` as a real number (rewrite form). -/
theorem dq_r : ((P₁.dq : ℚ) : ℝ) = 1 / 380000 := by rw [dq_eq]; norm_num

theorem eps_eq : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁

theorem Rq_eq : QMCLeafB.EngineRuntime.Rq G₁ = 2 := QMCLeafB.EmptyBodyM5.Rq_G₁

theorem cAq_eq : P₁.cAq = 2 := by
  have h : P₁.cAq = QMCLeafB.EngineRuntime.Rq G₁ := rfl
  rw [h, Rq_eq]

/-- **The campaign ball radius at `G₁` is `dq/24 = 1/9120000`** (the radius
`BallM2.no_runParts_of_ball` uses). -/
theorem rBall_eq :
    ((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)) = 1 / 9120000 := by
  rw [dq_r, cAq_eq]
  norm_num

/-- The bottom of the dreg band: `u* = −2 − 2δ`, i.e. `t = u* + ε = −Rq + 17/380000`. -/
def tStar : ℚ := -(2 : ℚ) + 17 / 380000

/-- The real threshold `u = t_Δ − ε` at the band point `t_Δ = tStar + Δ`. -/
theorem thresh_eq (Δ : ℚ) :
    (((tStar + Δ : ℚ)) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 2 * (1 / 380000 : ℝ)) + (Δ : ℝ) := by
  rw [Rq_eq]
  unfold tStar
  push_cast
  ring

/-! ## 1.  The real body's objective floor at `n = 2`

`BodyEmpty` is stated over the **real** relaxation, so the `n = 2` floor is needed in `ℝ` (the
banked `EmptyBodyM5.frob_ge_of_relaxMem` is about *rational* members).  The input is
`A = !![0,1;1,0]`, so `⟪A,X⟫ = X₀₁ + X₁₀` and only the sum of the two off-diagonal entries matters. -/

theorem frob_floor {u d : ℝ} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u d X) :
    -(2 + 3 * d / 2) ≤ QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X := by
  obtain ⟨hpsd, hdiag, _htr⟩ := hX
  have h11 := hpsd (fun _ : Fin 2 => (1 : ℝ))
  have hsq : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
  have hqf : QMCLeafB.BallFloor.qfR X (fun _ : Fin 2 => (1 : ℝ))
      = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp only [Fin.sum_univ_two]
    ring
  rw [hsq, hqf] at h11
  have hd0 : X 0 0 ≤ 1 + d / 4 := by
    have := (abs_le.mp (hdiag 0)).2
    linarith
  have hd1 : X 1 1 ≤ 1 + d / 4 := by
    have := (abs_le.mp (hdiag 1)).2
    linarith
  have hfrob : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X = X 0 1 + X 1 0 := by
    simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two,
      QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
      QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
    ring
  rw [hfrob]
  linarith

#print axioms QMCLeafB.DregM6.frob_floor

/-! ## 2.  The dreg witness: a body point with prescribed objective slack -/

/-- The off-diagonal perturbation `!![0,c;c,0]`: `⟪A,·⟫ = 2c`, `‖·‖_F² = 2c²`. -/
def E2 (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, c; c, 0]

theorem frob_E2 (c : ℝ) :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) (E2 c) = 2 * c := by
  simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  simp only [E2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem frobNormSq_E2 (c : ℝ) : QMCLeafB.BallFloor.frobNormSq (E2 c) = 2 * c ^ 2 := by
  simp only [QMCLeafB.BallFloor.frobNormSq, Fin.sum_univ_two]
  simp only [E2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The witness matrix: unit-diagonal-centred, off-diagonal `−(1+3δ/4) + Δ/2`. -/
def Xd (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + (1 / 380000 : ℝ) / 4, -((1 + 3 * (1 / 380000 : ℝ) / 4)) + a / 2;
     -((1 + 3 * (1 / 380000 : ℝ) / 4)) + a / 2, 1 + (1 / 380000 : ℝ) / 4]

theorem frob_Xd (a : ℝ) :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) (Xd a)
      = -(2 + 3 * (1 / 380000 : ℝ) / 2) + a := by
  simp only [QMCLeafB.BallFloor.frob, Fin.sum_univ_two,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  simp only [Xd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **The `n = 2` algebraic core**: for `a ≥ 0`, `d ≥ 0`, `a ≤ 2 + 3d/2` the quadratic form of the
witness dominates `−(d/2)·‖x‖²`.  (Certificate: `(1+3d/4−a/4)(x₀−x₁)² + (a/4)(x₀+x₁)² ≥ 0`.) -/
theorem qf_core {d a x0 x1 : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a) (ha2 : a ≤ 2 + 3 * d / 2) :
    -(d / 2) * (x0 ^ 2 + x1 ^ 2)
      ≤ (1 + d / 4) * (x0 ^ 2 + x1 ^ 2) + (-(2 + 3 * d / 2) + a) * (x0 * x1) := by
  nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x0 + x1),
    mul_nonneg (show (0 : ℝ) ≤ 1 + 3 * d / 4 - a / 4 by linarith) (sq_nonneg (x0 - x1)),
    mul_nonneg (show (0 : ℝ) ≤ a / 4 by linarith) (sq_nonneg (x0 + x1))]

/-- **The witness lies in the real body at threshold `u* + a`, for every slack `a ≥ 0`.** -/
theorem body_witness (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2 + 3 * (1 / 380000 : ℝ) / 2) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      (-(2 + 2 * (1 / 380000 : ℝ)) + a) (1 / 380000 : ℝ) (Xd a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hexp : QMCLeafB.BallFloor.qfR (Xd a) x
        = (1 + (1 / 380000 : ℝ) / 4) * (x 0 ^ 2 + x 1 ^ 2)
          + (-(2 + 3 * (1 / 380000 : ℝ) / 2) + a) * (x 0 * x 1) := by
      rw [QMCLeafB.BallFloor.qfR_eq_sum]
      simp only [Fin.sum_univ_two]
      simp only [Xd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [hexp]
    have hsq : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hsq]
    exact qf_core (by norm_num) ha0 ha2
  · intro i
    have hd : Xd a i i - 1 = (1 / 380000 : ℝ) / 4 := by
      fin_cases i <;> simp [Xd]
    rw [hd]
    norm_num
  · rw [frob_Xd]
    linarith

#print axioms QMCLeafB.DregM6.body_witness

/-! ## 3.  No pinched member in the band

The rational floor of a *pinched* member (`EmptyBodyM5.frob_ge_of_pinched`) is `−2 − δ/2`, while the
band's threshold gives `u + δ/2 = −2 − 3δ/2 + Δ`.  So every `Δ < δ` is pinched-empty. -/

theorem not_pinchFeasible (Δ : ℚ) (hΔ : Δ < 1 / 380000) :
    ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ (tStar + Δ) P₁ := by
  rintro ⟨Q, hM, hdiag⟩
  rw [dq_eq] at hM hdiag
  have hge := QMCLeafB.EmptyBodyM5.frob_ge_of_pinched (u := _) (δ := 1 / 380000) (c := 1)
    (by norm_num) QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00 QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10 QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11 hdiag hM
  have hle := hM.trace_le
  have hu : (tStar + Δ) - QMCLeafB.RundataCert.eps G₁ = -2 - 2 * (1 / 380000) + Δ := by
    rw [eps_eq]
    unfold tStar
    ring
  rw [hu] at hle
  have hge' : -1 * (2 + (1 / 380000 : ℚ) / 2)
      ≤ QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁) Q := hge
  linarith [hge', hle, hΔ]

#print axioms QMCLeafB.DregM6.not_pinchFeasible

/-! ## 4.  Ball-freeness: the volume route cannot fire

A Frobenius ball of radius `r` around a body point raises `⟪A,·⟫` by `r` (perturbation
`!![0,r/2;r/2,0]`: `‖·‖_F² = r²/2`, `⟪A,·⟫ = r`), while every body point at `u* + Δ` has objective
slack at most `Δ`.  So `Δ < r` excludes the ball.  Here `r = δ/24 = 1/9120000`, the campaign's own
radius at `G₁`. -/

/-- **The body at `u* + Δ` contains no Frobenius ball of radius `δ/24`** (matrix form). -/
theorem mat_ball_free (Δ : ℚ) (hΔ0 : 0 ≤ (Δ : ℝ)) (hΔr : (Δ : ℝ) < (1 / 380000 : ℝ) / 24)
    (X₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (∀ Y : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.frobNormSq (Y - X₀) ≤ (1 / 9120000 : ℝ) ^ 2 →
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
          (-(2 + 2 * (1 / 380000 : ℝ)) + (Δ : ℝ)) (1 / 380000 : ℝ) Y) := by
  intro hall
  by_cases hbody : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      (-(2 + 2 * (1 / 380000 : ℝ)) + (Δ : ℝ)) (1 / 380000 : ℝ) X₀
  · have hfloor := frob_floor hbody
    have htrace := hbody.2.2
    have hy := hall (X₀ + E2 ((1 / 9120000 : ℝ) / 2)) ?_
    · have hfr : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) (X₀ + E2 ((1 / 9120000 : ℝ) / 2))
          = QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X₀ + 2 * ((1 / 9120000 : ℝ) / 2) := by
        rw [QMCLeafB.BallFloor.frob_add, frob_E2]
      nlinarith [hy.2.2, hfr, htrace, hfloor, hΔr]
    · have hsub : X₀ + E2 ((1 / 9120000 : ℝ) / 2) - X₀ = E2 ((1 / 9120000 : ℝ) / 2) := by
        abel
      rw [hsub, frobNormSq_E2]
      nlinarith
  · exact hbody (hall X₀ (by
      rw [show X₀ - X₀ = 0 by abel]
      rw [show QMCLeafB.BallFloor.frobNormSq (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 by
        simp [QMCLeafB.BallFloor.frobNormSq]]
      norm_num))

#print axioms QMCLeafB.DregM6.mat_ball_free

/-- **Ball-freeness in the form `no_runParts_of_ball` consumes**: no `X₀` carries the campaign's
ball `dq/(8(cA+1))` into the run's relaxation at a band point. -/
theorem no_ball (Δ : ℚ) (hΔ0 : 0 ≤ (Δ : ℝ)) (hΔr : (Δ : ℝ) < (1 / 380000 : ℝ) / 24)
    (X₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
        ⊆ QMCLeafB.BallM2.runBall G₁ (tStar + Δ) P₁) := by
  rw [rBall_eq]
  intro hsub
  refine mat_ball_free Δ hΔ0 hΔr X₀ (fun Y hY => ?_)
  have hmem : QMCLeafB.AnswerProducer.flat Y
      ∈ QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) (1 / 9120000) := by
    simp only [QMCLeafB.Boundary.eucBallF, Set.mem_ofPred_eq]
    have hflat : QMCLeafB.AnswerProducer.flat Y - QMCLeafB.AnswerProducer.flat X₀
        = QMCLeafB.AnswerProducer.flat (Y - X₀) := QMCLeafB.Boundary.flat_sub Y X₀
    have h1 : ∀ k, QMCLeafB.AnswerProducer.flat Y k - QMCLeafB.AnswerProducer.flat X₀ k
        = QMCLeafB.AnswerProducer.flat (Y - X₀) k := fun k => congrFun hflat k
    simp only [h1]
    rw [QMCLeafB.Boundary.sum_sq_flat]
    exact hY
  have hrun := hsub hmem
  have hb : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
      (((tStar + Δ : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
      (((P₁.dq : ℚ) : ℝ)) (QMCLeafB.Boundary.unflat (QMCLeafB.AnswerProducer.flat Y)) := hrun.1
  rwa [QMCLeafB.Boundary.unflat_flat, thresh_eq, dq_r] at hb

#print axioms QMCLeafB.DregM6.no_ball

/-! ## 5.  The band is inside the leaf's bracket, and the stratum is inhabited -/

theorem dreg_interior (Δ : ℚ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ < 1) :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ tStar + Δ ∧
      (((tStar + Δ : ℚ)) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) := by
  rw [Rq_eq]
  constructor
  · unfold tStar
    linarith
  · unfold tStar
    have hΔ1' : ((Δ : ℚ) : ℝ) < 1 := by exact_mod_cast hΔ1
    push_cast
    linarith

#print axioms QMCLeafB.DregM6.dreg_interior

/-- **The nonemptiness of the real body in the band** (`¬ BodyEmpty`), from the witness. -/
theorem not_bodyEmpty (Δ : ℚ) (hΔ0 : 0 ≤ (Δ : ℝ))
    (hΔ2 : (Δ : ℝ) ≤ 2 + 3 * (1 / 380000 : ℝ) / 2) :
    ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (tStar + Δ) P₁ := by
  intro hE
  refine hE (Xd (Δ : ℝ)) ?_
  rw [thresh_eq, dq_r]
  exact body_witness (Δ : ℝ) hΔ0 hΔ2

#print axioms QMCLeafB.DregM6.not_bodyEmpty

/-- **THE DREG IS REAL (n = 2).**  There is a threshold in the leaf's interior bracket at which the
real relaxed body is nonempty, no pinched member exists, and no ball of the campaign radius is
contained in the run's relaxation.  In particular `BallM2.no_runParts_of_ball`'s hypothesis is
unsatisfiable there, while `ThriceM3.bit_false_of_not_pinchFeasible` still forces the bit `false`:
the third stratum is inhabited and *not* refutable by volume. -/
theorem dreg_stratum_inhabited :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G₁ ≤ t ∧
      ((t : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) ∧
      ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t P₁ ∧
      ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ t P₁ ∧
      (∀ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
        ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
            (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
            ⊆ QMCLeafB.BallM2.runBall G₁ t P₁)) := by
  refine ⟨tStar + 1 / 18240000, (dreg_interior _ (by norm_num) (by norm_num)).1,
    (dreg_interior _ (by norm_num) (by norm_num)).2, ?_, ?_, ?_⟩
  · exact not_bodyEmpty _ (by norm_num) (by norm_num)
  · exact not_pinchFeasible _ (by norm_num)
  · intro X₀
    exact no_ball _ (by norm_num) (by norm_num) X₀

#print axioms QMCLeafB.DregM6.dreg_stratum_inhabited

/-- **The dreg band is an interval, not a point**: every `Δ ∈ [0, 1/18240000]` gives an interior
threshold whose body is nonempty, pinched-member-free and ball-free. -/
theorem dreg_band (Δ : ℚ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 18240000) :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ tStar + Δ ∧
      (((tStar + Δ : ℚ)) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) ∧
      ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (tStar + Δ) P₁ ∧
      ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ (tStar + Δ) P₁ ∧
      (∀ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
        ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
            (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
            ⊆ QMCLeafB.BallM2.runBall G₁ (tStar + Δ) P₁)) := by
  have hΔr : (Δ : ℝ) < (1 / 380000 : ℝ) / 24 := by
    have h1 : (Δ : ℝ) ≤ (1 / 18240000 : ℝ) := by
      have h2 : ((Δ : ℚ) : ℝ) ≤ ((1 / 18240000 : ℚ) : ℝ) := by exact_mod_cast hΔ1
      simpa using h2
    nlinarith
  have hint := dreg_interior Δ hΔ0 (by linarith)
  exact ⟨hint.1, hint.2, not_bodyEmpty Δ (by exact_mod_cast hΔ0) (by nlinarith),
    not_pinchFeasible Δ (by nlinarith), fun X₀ => no_ball Δ (by exact_mod_cast hΔ0) hΔr X₀⟩

#print axioms QMCLeafB.DregM6.dreg_band

/-- **The volume route is vacuous on the band**: `BallM2.no_runParts_of_ball`'s ball hypothesis has
no instance at a band point, for any centre. -/
theorem volume_route_vacuous (Δ : ℚ) (hΔ0 : 0 ≤ (Δ : ℝ))
    (hΔr : (Δ : ℝ) < (1 / 380000 : ℝ) / 24) :
    ¬ ∃ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
          (((P₁.dq : ℚ) : ℝ) / (8 * (((P₁.cAq : ℚ) : ℝ) + 1)))
          ⊆ QMCLeafB.BallM2.runBall G₁ (tStar + Δ) P₁ := by
  rintro ⟨X₀, hX₀⟩
  exact no_ball Δ hΔ0 hΔr X₀ hX₀

#print axioms QMCLeafB.DregM6.volume_route_vacuous

/-- **Consistency with the banked sliver.**  The sliver `t₁` is the band point `Δ = 3δ/4`: inside
the pinched-empty range `Δ < δ` (`not_pinchFeasible` applies there and reproduces
`EmptyBodyM5.no_pinched_member_G₁`), but **outside** the ball-free range `Δ < δ/24` — exactly as
`BallM2.sliver_ball_campaign` requires (`t₁` does carry a ball; the dreg below it does not). -/
theorem dreg_below_sliver : tStar + 1 / 18240000 < QMCLeafB.AnchorFactsM2.t₁ := by
  unfold tStar QMCLeafB.AnchorFactsM2.t₁
  norm_num

#print axioms QMCLeafB.DregM6.dreg_below_sliver

/-- The sliver is at `Δ = 3δ/4`: pinched-empty but **not** ball-free — the boundary between the dreg
and the sliver class, at the exact numbers. -/
theorem sliver_at_three_quarter :
    tStar + 3 / 4 * (1 / 380000) = QMCLeafB.AnchorFactsM2.t₁ ∧
      (3 / 4 : ℚ) * (1 / 380000) < 1 / 380000 ∧
      ¬ ((3 / 4 : ℚ) * (1 / 380000) < (1 / 380000) / 24) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  unfold tStar QMCLeafB.AnchorFactsM2.t₁
  norm_num

#print axioms QMCLeafB.DregM6.sliver_at_three_quarter

/-- **The dreg is exactly a live third-stratum demand.**  Given the campaign's own read-out data
(the bit equation, `ok ⇒ member` at the pinched centres, and the pinched diagonal), the bit at a band
point reads `false` (`ThriceM3.bit_false_of_not_pinchFeasible`) while the body is nonempty — so
`ThriceM3.ThirdStratum` demands a `RunParts` there, and `volume_route_vacuous` says the volume
obstruction cannot discharge or refute that demand.  The campaign's residual is live on the whole
band. -/
theorem third_stratum_demanded (Δ : ℚ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 18240000)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (rb : ℕ → Bool)
    (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o G₁ (tStar + Δ) = QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cX k)
        (tStar + Δ - QMCLeafB.RundataCert.eps G₁) P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - P₁.dq / 4) :
    o G₁ (tStar + Δ) = false ∧ ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (tStar + Δ) P₁ := by
  have hpin : ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ (tStar + Δ) P₁ :=
    not_pinchFeasible Δ (by nlinarith)
  have hcast : (Δ : ℝ) ≤ (1 / 18240000 : ℝ) := by
    have h2 : ((Δ : ℚ) : ℝ) ≤ ((1 / 18240000 : ℚ) : ℝ) := by exact_mod_cast hΔ1
    simpa using h2
  have hne : ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ (tStar + Δ) P₁ :=
    not_bodyEmpty Δ (by exact_mod_cast hΔ0) (by nlinarith)
  exact ⟨QMCLeafB.ThriceM3.bit_false_of_not_pinchFeasible hbit hok hdia hpin, hne⟩

#print axioms QMCLeafB.DregM6.third_stratum_demanded

/-! ## 6.  The design consequence: the bracket, not the split, has to move

The band's bottom is at `u* = −2 − 2δ`, i.e. at distance `ε` above `−Rq` **for every admissible
`dq`** (the `ε/δ` split changes `δ`, and `u*` tracks it) — so no split removes the band.  Removing it
needs the bracket bottom raised to `−Rq + 2δ`; the threshold lost is `2δ`, which at `G₁` is
`1/190000` against the leaf's slack `W/10000 = 1/10000` (ratio exactly `19 = 9·Rq+1`). -/

/-- The total weight at `G₁`: `Rq = 2·∑w = 2` forces `∑w = 1`. -/
theorem weight_sum_G₁ : (∑ e, ((G₁.weights e : ℚ≥0) : ℚ)) = 1 := by
  have h : QMCLeafB.EngineRuntime.Rq G₁ = 2 * ∑ e, ((G₁.weights e : ℚ≥0) : ℚ) := rfl
  rw [Rq_eq] at h
  linarith

#print axioms QMCLeafB.DregM6.weight_sum_G₁

/-- **`2δ` at `G₁`, and the leaf's slack at `G₁`.**  Raising the bracket bottom by the band's width
`2δ` costs `1/190000`, and the leaf's whole slack budget is `W/10000 = 1/10000` (`W = ∑w = Rq/2`):
exactly `19 = 9·Rq+1` times as large. -/
theorem bracket_cost :
    2 * QMCLeafB.RundataParams.dqShallow G₁ = 1 / 190000 ∧
    19 * (2 * QMCLeafB.RundataParams.dqShallow G₁) = 1 / 10000 ∧
    (∑ e, ((G₁.weights e : ℚ≥0) : ℚ)) / 10000 = 1 / 10000 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [QMCLeafB.EmptyBodyM5.dqShallow_G₁]; norm_num
  · rw [QMCLeafB.EmptyBodyM5.dqShallow_G₁]; norm_num
  · rw [weight_sum_G₁]

#print axioms QMCLeafB.DregM6.bracket_cost

end QMCLeafB.DregM6


