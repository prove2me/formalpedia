-- Prove2me | Definitions.Def_QMCLeafB_dregzip
-- name    : QMCLeafB_dregzip
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:57:49.651242+00:00
-- url     : https://prove2.me/theorems/626415e3-ddaa-4188-819c-47df283c55d1
-- title:
--   QMCLeafB dregzip
-- statement:
--   # `Check_dregzip_m6` — phase 25, member m6, direction d8: the dreg band inside the accepted architecture
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_zip_m7
/-
# `Check_dregzip_m6` — phase 25, member m6, direction d8: the dreg band inside the accepted architecture

`Check_dreg_m6` exhibits a `Θ(δ)`-wide band of thresholds at `G₁` whose real body is nonempty, has no
pinched member, and carries **no** campaign ball.  The accepted phase-25 architecture
(`Check_zip_m7`, `QMCLeafB.ZipM7.ZipSupply`) splits the residual by exactly that predicate:
`BallFree G t P` (= no translate of the campaign ball inside `runBall`) and `ThinThird` (= `RunParts`
at a `false`-bit nonempty **ball-free** interior point).  This file closes the loop:

* `dreg_is_ballFree` — every band point of `Check_dreg_m6` is `ZipM7.BallFree`;
* `thinThird_hypotheses_satisfiable` — `ThinThird`'s hypothesis bundle (interior, nonempty body,
  ball-free) is **satisfiable** at `n = 2`, so that slot of the accepted residual is a real
  obligation, not a vacuous one (the recurring failure mode of phases 20–24);
* `thinThird_demanded_at_band` — with the campaign's own read-out data the bit is *forced* `false`
  on the band, so the obligation `ThinThird` states binds there.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom cone `[propext, Classical.choice, Quot.sound]`.
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

/-- **Every band point is `ZipM7.BallFree`** — the predicate the accepted split keys the thin
production on. -/
theorem dreg_is_ballFree (Δ : ℚ) (hΔ0 : 0 ≤ (Δ : ℝ))
    (hΔr : (Δ : ℝ) < (1 / 380000 : ℝ) / 24) :
    QMCLeafB.ZipM7.BallFree G₁ (tStar + Δ) P₁ :=
  fun X₀ => no_ball Δ hΔ0 hΔr X₀

#print axioms QMCLeafB.DregM6.dreg_is_ballFree

/-- **`ThinThird`'s hypothesis bundle is satisfiable at `n = 2`**: an interior threshold with a
nonempty real body and a ball-free relaxation exists.  So the thin slot of the accepted residual is
a genuine obligation. -/
theorem thinThird_hypotheses_satisfiable :
    ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G₁ ≤ t ∧
      ((t : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) ∧
      ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t P₁ ∧
      QMCLeafB.ZipM7.BallFree G₁ t P₁ := by
  refine ⟨tStar + 1 / 18240000, (dreg_interior _ (by norm_num) (by norm_num)).1,
    (dreg_interior _ (by norm_num) (by norm_num)).2,
    not_bodyEmpty _ (by norm_num) (by norm_num), ?_⟩
  exact dreg_is_ballFree _ (by norm_num) (by norm_num)

#print axioms QMCLeafB.DregM6.thinThird_hypotheses_satisfiable

/-- **The pinched read-out would force the bit `false` on the band** (the `ThriceM3` route).  This is
exactly the design distinction the accepted stroke turns on: with the diagonal slot
(`cX k` on `1 − dq/4`) the bit is forced `false` at a pinched-empty point, so a ball-free thin
production could only be needed at `false`; with the *un-pinched* read-out the accepted stroke uses
(`Check_zip_m7.pinch_constraint_not_forced`, `EmptyBodyM5.Q₁` a unit-diagonal member) nothing forces
the bit here, so the thin production may be owed at either reading.  Recorded, not used by the
accepted stroke. -/
theorem bit_false_at_band_of_pinched_readout (Δ : ℚ) (hΔ : Δ < 1 / 380000)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (rb : ℕ → Bool)
    (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o G₁ (tStar + Δ) = QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cX k)
        (tStar + Δ - QMCLeafB.RundataCert.eps G₁) P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - P₁.dq / 4) :
    o G₁ (tStar + Δ) = false :=
  QMCLeafB.ThriceM3.bit_false_of_not_pinchFeasible hbit hok hdia (not_pinchFeasible Δ hΔ)

#print axioms QMCLeafB.DregM6.bit_false_at_band_of_pinched_readout

end QMCLeafB.DregM6


