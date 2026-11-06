-- Prove2me | Definitions.Def_QMCLeafB_cov36b
-- name    : QMCLeafB_cov36b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:33:46.746449+00:00
-- url     : https://prove2.me/theorems/c42997e3-26d7-4e0c-9386-c255382a11e3
-- title:
--   QMCLeafB cov36b
-- statement:
--   # `Check_cov36b_m7` — phase 36, member m7, direction `coverage36` (second file)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_oklevel
import Definitions.Def_QMCLeafB_sim_loop_m6
/-
# `Check_cov36b_m7` — phase 36, member m7, direction `coverage36` (second file)

## Why this file exists

m8's `Check_asm36_m8` (direction d5, f1) states that m1's radius-free ball/horizon criterion
(`DC35M1.not_shallowCut_of_ball_horizon`) **cannot be transported to records**, because
`encl_of_bodyRec` produces the record's own `cd` stream and not a `NormalCut`, so `ShallowCut` is
out of reach.  The conclusion they draw — "prove the record-level obstruction separately" — is
right, but the *sharpness* they get is not forced: their `no_runParts_of_ball_horizon` uses the
crude doubling budget `volPot A₀ · 2^{-K} < r^(n·n)`, i.e. a threshold `r ≳ 2^{-K/(n·n)}`, which at
`P33` is `~10^{-6762}`.

**The determinant telescope transplants directly.**  `RunParts.hle` says `(cd k).rho ≤ P.rmax` at
every cut round — so the record's cuts ARE shallow at the ceiling depth `rmax` — and the engine's
general-stream invariant `Prefix.body_containment_prefix` (`k < T` hypotheses only) plus
`EngineIterates.Aat_det_ge` (arbitrary `cd`, `ρ ≤ ρmax`) give

> `det A_{K·m} ≥ det A₀ · rho0R(N, rmax)^(K·m)`

**at the record's own stream**, with no `ShallowCut` and no `NormalCut` anywhere.  The radius-free
criterion therefore holds verbatim at record level with m1's own constant `pConst`, and the true
threshold is `pConst^(-1/(2N)) ≈ 3·10^{-160639}` — not `10^{-6762}`.

## What is machine-checked

* `pConstG` — m1's constant at an arbitrary `(G, P)`.
* `bodyRec_containment` — the record's relaxation lies in every iterate's ellipsoid.
* `no_bodyRec_of_ball_horizon` — **a ball in the relaxation of radius `r > 0` with
  `1 < pConstG · r^(2·n·n)` refutes `BodyRec`**, i.e. `∀ o, ¬ Nonempty (RunParts o G t P)`
  (so `RunParts` forces `o G t = true`).
* `bit_true_of_ball_horizon_G1` — the same at `paramsKbc2/G₁`, where `pConstG G₁ P₁` is literally
  `Check_cov36_m7.pConst`; composing with `Check_cov36_m7.no_horizon_ball` says the criterion is
  **silent on the collar**, so this sharpening does not close the coverage gap.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Cov36BM7

open QuantumMaxCutEnergy

abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.DregM6.G₁

abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.DregM6.P₁

/-- m1's determinant-horizon constant at an arbitrary program family. -/
noncomputable def pConstG (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) : ℝ :=
  (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
    * (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)

/-! ## The main theorem: the determinant-horizon criterion at RECORD level

Nothing here mentions `ShallowCut` or `NormalCut`.  The two inputs are
`Prefix.body_containment_prefix` (the engine's containment invariant, prefix-guarded — exactly the
`RunParts` guards) and `Prefix.Aat_det_ge_prefix` (determinant growth in the shallow regime,
prefix-guarded).  `RunParts.hle` is what makes the second apply: every recorded depth is at most
`P.rmax`, i.e. the record's cuts are shallow at the ceiling. -/

theorem bodyRec_containment {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P) (hbit : o G t = false) :
    ∀ k, k ≤ P.K * P.m → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
          ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ) →
      QMCLeafB.BallFloor.Ell
        (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd k))
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) z := by
  classical
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by
    have := P.hdq; positivity
  have hall : ∀ k, k < P.K * P.m → B.ok k = false := fun k hk =>
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1
      (by rw [← B.hverdict]; exact hbit) k hk
  refine QMCLeafB.SimLoop.Prefix.body_containment_prefix (n := G.n * G.n) (T := P.K * P.m) hN
    (QMCLeafB.Boundary.initShapeOf_cast_posDef hNm)
    (fun k hk => B.hwit k hk (hall k hk))
    (fun k hk => B.hrho k hk (hall k hk))
    (fun k hk => B.hcne k hk (hall k hk))
    (0 : Fin (G.n * G.n) → ℝ)
    (QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
      ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ))
    (fun z hz => QMCLeafB.Boundary.ell_initShapeOf hNm
      (QMCLeafB.Boundary.relaxBall_norm hz))
    ?_
  intro k hk z hz
  have hδ0 : (0 : ℚ) ≤ B.del k := B.hdel0 k hk (hall k hk)
  have hchk : (B.del k) ^ 2 ≤ ((B.cd k).rho) ^ 2
      * QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p :=
    B.hcheck k hk (hall k hk)
  have hσR : 0 < QMCLeafB.EngineIterates.sigmaR
      (QMCLeafB.EngineIterates.cutCR B.cd k) (QMCLeafB.EngineIterates.cutPR B.cd k) :=
    QMCLeafB.EngineIterates.sigmaR_pos
      (QMCLeafB.SimLoop.Aat_cast_posDef_prefix hN
        (QMCLeafB.Boundary.initShapeOf_cast_posDef hNm)
        (fun j hj => B.hwit j hj (hall j hj)) (fun j hj => B.hrho j hj (hall j hj))
        (fun j hj => B.hcne j hj (hall j hj)) k (le_of_lt hk))
      (QMCLeafB.SimLoop.cast_witness_prefix
        (fun j hj => B.hwit j hj (hall j hj)) hk)
      (QMCLeafB.EngineIterates.cast_normal_ne (B.hcne k hk (hall k hk)))
  have hδle : (((B.del k : ℚ)) : ℝ)
      ≤ ((B.cd k).rho : ℝ)
        * Real.sqrt ((QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ) :=
    QMCLeafB.EngineIterates.margin_le_of_sq_check hδ0 (B.hrho k hk (hall k hk))
      (QMCLeafB.EngineIterates.sigmaQ_pos_of_cast hσR).le hchk
  have hσeq : ((QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ)
      = QMCLeafB.EngineIterates.sigmaR
          (QMCLeafB.EngineIterates.cutCR B.cd k) (QMCLeafB.EngineIterates.cutPR B.cd k) :=
    QMCLeafB.EngineIterates.cast_sigmaQ (B.cd k).c (B.cd k).p
  rw [hσeq] at hδle
  exact le_trans (neg_le_neg hδle) (B.hcut k hk (hall k hk) z hz)

#print axioms QMCLeafB.Cov36BM7.bodyRec_containment

/-- **THE RECORD-LEVEL RADIUS-FREE OBSTRUCTION, with m1's sharp constant.**  A ball of radius `r > 0`
inside the relaxation, together with `1 < pConstG·r^(2·n·n)`, forces the bit `TRUE`: every all-false
record is impossible.  This is `DC35M1.not_shallowCut_of_ball_horizon` transplanted to `RunParts`
without going through `ShallowCut`, so m8's `no_runParts_of_ball_horizon` — which uses the crude
doubling budget and gives `r ≳ 10^{-6762}` at `P33` — is superseded by the determinant threshold
`pConstG^(-1/(2N)) ≈ 3·10^{-160639}` at `P₁`. -/
theorem bit_true_of_ball_horizon {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
            ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ)
            ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ))
    (hK : 1 < pConstG G P * r ^ (2 * (G.n * G.n)))
    (B : QMCLeafB.FinalStroke.RunParts o G t P) :
    o G t = true := by
  classical
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by
    have := P.hdq; positivity
  by_contra hcon
  have hbit : o G t = false := by
    rcases h : o G t with _ | _
    · rfl
    · exact absurd h hcon
  have hall : ∀ k, k < P.K * P.m → B.ok k = false := fun k hk =>
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1
      (by rw [← B.hverdict]; exact hbit) k hk
  -- containment of the relaxation in the final ellipsoid
  have hcont := bodyRec_containment hn B hbit
  have hball' : ∀ y : Fin (G.n * G.n) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀
        - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m))
        ⬝ᵥ (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
            (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
              (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))
          *ᵥ (y + QMCLeafB.AnswerProducer.flat X₀
            - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m)))
        ≤ 1 :=
    fun y hy => hcont (P.K * P.m) (le_refl _) (y + QMCLeafB.AnswerProducer.flat X₀) (hball y hy)
  have hposdef := QMCLeafB.SimLoop.Aat_cast_posDef_prefix hN
    (QMCLeafB.Boundary.initShapeOf_cast_posDef hNm)
    (fun j hj => B.hwit j hj (hall j hj)) (fun j hj => B.hrho j hj (hall j hj))
    (fun j hj => B.hcne j hj (hall j hj)) (P.K * P.m) (le_refl _)
  have hfloor := QMCLeafB.BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell hposdef hr hball'
  -- determinant growth
  have hdet := QMCLeafB.SimLoop.Aat_det_ge_prefix (n := G.n * G.n) hN
    (QMCLeafB.Boundary.initShapeOf_cast_posDef hNm)
    (fun j hj => B.hwit j hj (hall j hj)) (fun j hj => B.hrho j hj (hall j hj))
    (fun j hj => B.hcne j hj (hall j hj)) P.hrmax
    (fun j hj => B.hle j hj (hall j hj)) (P.K * P.m) (le_refl _)
  -- assemble
  have hr2 : (0 : ℝ) < r ^ (2 * (G.n * G.n)) := by positivity
  have h1 : (QMCLeafB.EngineIterates.castM (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2))).det
        * (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((P.rmax : ℚ) : ℝ)) ^ (P.K * P.m)
        * r ^ (2 * (G.n * G.n))
      ≤ (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).det
        * r ^ (2 * (G.n * G.n)) :=
    mul_le_mul_of_nonneg_right hdet hr2.le
  have h2 : (QMCLeafB.EngineIterates.castM (QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) B.cd (P.K * P.m))).det
        * r ^ (2 * (G.n * G.n)) ≤ 1 := by
    rw [mul_comm]; exact hfloor
  have hK' : 1 < pConstG G P * r ^ (2 * (G.n * G.n)) := hK
  unfold pConstG at hK'
  linarith [le_trans h1 h2]

#print axioms QMCLeafB.Cov36BM7.bit_true_of_ball_horizon

/-! ## The `G₁` specialization, and how it meets `Check_cov36_m7`'s collar

`pConstG G₁ P₁` is literally `Check_cov36_m7.pConst` (same term), so
`Check_cov36_m7.no_horizon_ball` says exactly: on the collar `{pConst·Δ^8 ≤ 1}` the hypothesis `hK`
below is unsatisfiable.  Hence the SHARPEST banked record obstruction is silent on the collar, and
the record there is neither refuted nor built — the coverage gap of `Check_cov36_m7` survives the
sharpening. -/

theorem bit_true_of_ball_horizon_G1 {t : ℚ} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin 2) (Fin 2) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin (2 * 2) → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + QMCLeafB.AnswerProducer.flat X₀)
        ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G₁)
            ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) ((P₁.dq : ℚ) : ℝ)
            ((2 * (2 : ℚ) ^ 2 + 2 * P₁.dq ^ 2 : ℚ) : ℝ))
    (hK : 1 < pConstG G₁ P₁ * r ^ (2 * (2 * 2)))
    (B : QMCLeafB.FinalStroke.RunParts o G₁ t P₁) :
    o G₁ t = true :=
  bit_true_of_ball_horizon (G := G₁) (by rw [show G₁.n = 2 from rfl]) (P := P₁)
    (t := t) (o := o) hr (by simpa using hball) hK B

#print axioms QMCLeafB.Cov36BM7.bit_true_of_ball_horizon_G1

end QMCLeafB.Cov36BM7


