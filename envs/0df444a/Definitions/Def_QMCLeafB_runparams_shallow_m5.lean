-- Prove2me | Definitions.Def_QMCLeafB_runparams_shallow_m5
-- name    : QMCLeafB_runparams_shallow_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:36:22.647731+00:00
-- url     : https://prove2.me/theorems/f4ab6e63-9eca-40d1-a546-2b874165e214
-- title:
--   QMCLeafB runparams_shallow_m5
-- statement:
--   # leaf B phase 13 — brick `runparams-shallow` (swarm `smw17fqzz`, member m5, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_halving
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B phase 13 — brick `runparams-shallow` (swarm `smw17fqzz`, member m5, direction d8)

`QMCLeafB.FinalStroke.RunParams G` (`Check_final_stroke_m7`) is the threshold-independent half of
`RunData`, and `Endgame_of_parts` consumes a *total* `P : ∀ G, RunParams G`.  Two of its six
inequalities are the ones that must be *compatible with the run that will be built on top*:

* `hhalve` — only true at a **positive** ceiling below the critical depth; the shelf's
  `runData_hhalve_close` (at `rmax = 0`, `m = 4N`) forces zero cut depth and hence a zero margin
  (`QMCLeafB.RundataCert.del_eq_zero_of_rmax_zero`), so a run with cut rounds cannot use it.
  This file uses `rmax = 1/(4N)`, `m = 16N²` (`QMCLeafB.RundataHalving.hhalveOf`).
* the **ok-branch rounding budget**.  `RunParams` has no field for it, but `RunData.hcert` needs
  `roundCost A (3·dq/4) + dq/2 - εr ≤ εw` at `εw = εr = Rq G/40000`, which *forces* the oracle
  tolerance to be small relative to `Rq G`; a `RunParams` with an arbitrary `dq` cannot be
  inhabited by `RunParts` at all.  This file therefore fixes
  `dq = (Rq G/40000)/(9·Rq G + 1)`, proves the budget (`dqShallow_budget`), and records the
  constraint for the assembler.
* `cAq = Rq G` exactly (the sharp ledger, matching `Check_runparams_m2`'s choice), via
  `∑ᵢⱼ |wMatrixQ G i j| = Rq G`.

`runParamsShallow` is the concrete inhabitant, at `2 ≤ G.n` and `0 < Rq G` — exactly the range on
which `hd` is ever read (`Endgame_of_dominated_rounds_interior` only asks for
`(t : ℝ) < -Rq G/40000`, which forces `Rq G > 0`).  The degenerate `Rq G = 0` and `G.n ≤ 1` cases are
handled inside `VerdictSound.soundEpsOnBracket_of_runData_interior` / `soundAt_of_le_one`.

No `sorry`, no `axiom`, no edits to existing files; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.RundataParams

open QuantumMaxCutEnergy

/-- The tolerance formula at positive total weight. -/
noncomputable def dqShallowCore (G : Input) : ℚ :=
  QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1)

/-- The oracle tolerance of the shallow run: the largest value for which the ok-branch rounding
still fits in the leaf's slack `Rq G/40000`, with a harmless fallback at `Rq G = 0` so that the
parameters are *total* in `G`. -/
noncomputable def dqShallow (G : Input) : ℚ :=
  if QMCLeafB.EngineRuntime.Rq G = 0 then 1 else dqShallowCore G

theorem dqShallowCore_pos (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    0 < dqShallowCore G := by
  unfold dqShallowCore
  have h1 : 0 < QMCLeafB.RundataCert.eps G := QMCLeafB.RundataCert.eps_pos G hRq
  have h2 : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataArith.Rq_nonneg G
  positivity

theorem dqShallow_pos (G : Input) : 0 < dqShallow G := by
  unfold dqShallow
  split_ifs with h
  · norm_num
  · exact dqShallowCore_pos G (by
      have h0 := QMCLeafB.RundataArith.Rq_nonneg G
      rcases lt_or_eq_of_le h0 with h1 | h1
      · exact h1
      · exact absurd h1.symm h)

/-- The rounding cost at the weight matrix, against the *sharp* ledger `Rq G`. -/
theorem roundCost_le (G : Input) {ν : ℚ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) ν
      ≤ 6 * ν * QMCLeafB.EngineRuntime.Rq G := by
  rw [QMCLeafB.RundataCert.roundCost_wMatrixQ]
  have hcoef : (1 + ν) * (2 * ν + ν ^ 2) ≤ 6 * ν := by
    nlinarith [hν0, hν1, mul_nonneg hν0 (sub_nonneg.mpr hν1),
      mul_nonneg (sq_nonneg ν) (sub_nonneg.mpr hν1)]
  have hSnn : (0 : ℚ) ≤ ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSR : ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|
      = QMCLeafB.EngineRuntime.Rq G := QMCLeafB.RundataCert.sum_abs_wMatrixQ G
  calc (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|)
      ≤ (6 * ν) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|) :=
        mul_le_mul_of_nonneg_right hcoef hSnn
    _ = 6 * ν * QMCLeafB.EngineRuntime.Rq G := by rw [hSR]

/-- **The ok-branch rounding budget, at the shallow tolerance and the sharp ledger.** -/
theorem dqShallow_budget (G : Input) (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * dqShallowCore G / 4)
        + dqShallowCore G / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G := by
  have heS0 : QMCLeafB.RundataCert.eps G ≤ QMCLeafB.EngineRuntime.Rq G := by
    unfold QMCLeafB.RundataCert.eps
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 40000)]
    have h := hRq.le
    linarith
  set S := QMCLeafB.EngineRuntime.Rq G with hS
  set e := QMCLeafB.RundataCert.eps G with he
  have hS0 : 0 ≤ S := by rw [hS]; exact QMCLeafB.RundataArith.Rq_nonneg G
  have he0 : 0 < e := by rw [he]; exact QMCLeafB.RundataCert.eps_pos G hRq
  have heS : e ≤ S := by rw [he, hS]; exact heS0
  have hden : (0 : ℚ) < 9 * S + 1 := by linarith
  have hdvd : dqShallowCore G = e / (9 * S + 1) := rfl
  have hle1 : e / (9 * S + 1) ≤ 1 := by
    rw [div_le_iff₀ hden]
    nlinarith [he0.le, hS0]
  have hd1 : 3 * dqShallowCore G / 4 ≤ 1 := by
    rw [hdvd]
    nlinarith
  have hcost := roundCost_le G (ν := 3 * dqShallowCore G / 4)
    (by have h := dqShallowCore_pos G hRq; linarith) hd1
  have hhalf : dqShallowCore G / 2 ≤ e / 2 := by
    rw [hdvd]
    have h1 : e / (9 * S + 1) ≤ e := by
      rw [div_le_iff₀ hden]
      nlinarith [he0.le, hS0]
    linarith
  have hkey : 6 * (3 * dqShallowCore G / 4) * S ≤ e / 2 := by
    rw [hdvd, hS]
    have hstep : 6 * (3 * (e / (9 * S + 1)) / 4) * S = 9 * e * S / (2 * (9 * S + 1)) := by
      field_simp
      ring
    rw [hstep, div_le_iff₀ (by positivity : (0 : ℚ) < 2 * (9 * S + 1))]
    nlinarith [he0.le]
  linarith

/-- **The numeric half of the run, at the shallow constants and the sharp ledger.**  `K` is the
shelf's `simRounds` at `r = dq/(8(c_A+1))`, so `RunData.hbudget` is `runK_budget` verbatim; the
halving inequality is `hhalveOf` at the positive ceiling `rmax = 1/(4·n²)`, `m = 16·(n·n)²`. -/
noncomputable def runParamsShallow (G : Input) (hn : 2 ≤ G.n) :
    QMCLeafB.FinalStroke.RunParams G where
  K := QMCLeafB.RundataArith.runK G (dqShallow G) (QMCLeafB.EngineRuntime.Rq G)
    (QMCLeafB.RundataHalving.mOf (G.n * G.n)) 0
  m := QMCLeafB.RundataHalving.mOf (G.n * G.n)
  dq := dqShallow G
  cAq := QMCLeafB.EngineRuntime.Rq G
  rmax := QMCLeafB.RundataHalving.rmaxOf (G.n * G.n)
  hdq := dqShallow_pos G
  hcAq := QMCLeafB.RundataArith.Rq_nonneg G
  hAsum := le_of_eq (QMCLeafB.EngineRuntime.Rq_abs_sum G)
  hrmax := (QMCLeafB.RundataHalving.rmaxOf_pos (G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn; omega)).le
  hhalve := QMCLeafB.RundataHalving.hhalveOf (G.n * G.n) (by nlinarith)
  hbudget := QMCLeafB.RundataArith.runK_budget G (dqShallow G)
    (QMCLeafB.EngineRuntime.Rq G) (dqShallow_pos G) (QMCLeafB.RundataArith.Rq_nonneg G)
    (QMCLeafB.RundataHalving.mOf_ge_one (G.n * G.n) (by
      have h := Nat.mul_le_mul hn hn; omega)) 0

#print axioms QMCLeafB.RundataParams.dqShallow_pos
#print axioms QMCLeafB.RundataParams.roundCost_le
#print axioms QMCLeafB.RundataParams.dqShallow_budget
#print axioms QMCLeafB.RundataParams.runParamsShallow

end QMCLeafB.RundataParams


