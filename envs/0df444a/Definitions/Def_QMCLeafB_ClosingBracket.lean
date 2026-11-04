-- Prove2me | Definitions.Def_QMCLeafB_ClosingBracket
-- name    : QMCLeafB_ClosingBracket
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:35:36.989685+00:00
-- url     : https://prove2.me/theorems/032764f5-b07a-409d-a1b3-b82b588cca91
-- title:
--   QMCLeafB ClosingBracket
-- statement:
--   The Check_ClosingBracket module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_sim_poly_m4
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_pivot_program_m6
import Definitions.Def_QMCLeafB_run_induction_m1
import Definitions.Def_QMCLeafB_sizes_profile_m7
import Definitions.Def_QMCLeafB_fuel
import Definitions.Def_QMCLeafB_poly_loop_toolkit
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_BitProgram_m3

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder NNReal ENNReal

noncomputable section
namespace QMCLeafB.ClosingBracket

/-! ### The iteration bound consumed by `RunData.hbudget`

  `simRounds_budget` has exactly the inequality `RunData.hbudget` states at the campaign's
  radius δ/(8(c_A+1)) and initial potential `volPot initShapeOf`; choose `K := simRounds` at
  `m = 4(n·n)` to instantiate both `hbudget` and `hhalve`. -/

/-- **Iteration bound for `RunData.hbudget`**: at `K = simRounds` the potential contracts below the
  body's volume floor (the `hbudget` slot of `RunData` in `Check_brick_verdict_sound`). -/
theorem runData_hbudget_close (n : ℕ) (M : ℚ) (hM : 0 < M) (dq cAq : ℚ) (hδq : 0 < dq)
    (hcAq : 0 ≤ cAq) {m : ℕ} (hm1 : 1 ≤ m) :
    QMCLeafB.EngineIterates.volPot (n * n) (QMCLeafB.Boundary.initShapeOf (n * n) M) * (1 / 2) ^
        (QMCLeafB.SimLoop.simRounds n
          (QMCLeafB.EngineIterates.volPot (n * n) (QMCLeafB.Boundary.initShapeOf (n * n) M))
          ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) m : ℕ)
      < ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (n * n) :=
  QMCLeafB.SimLoop.simRounds_budget M hM hδq hcAq hm1

/-- **Halving time for `RunData.hhalve`**: `4(n·n)` rounds halve the potential factor at
  the shallow regime's contraction ceiling (the `hhalve` slot of `RunData`). -/
theorem runData_hhalve_close (N : ℕ) (hN : 2 ≤ N) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R N 0))⁻¹ ^ (4 * N) ≤ 1 / 2 :=
  QMCLeafB.SimLoop.halving_time_explicit hN

/-! ### `hspec`: agreement from the BitProgram contract

  `QMCLeafB.BitProgram.answerBit_engineOf` — the induced engine's bit is the decider by
  constructor-collapse; and `leafB_of_bracket_decider` gives the verbatim solution once the
  bracketed endpoint closures are the three direct fact forms (`feasble-witness`,
  `soundAt_of_le_one`, `soundAt_false_at_floor`). No `hspec`-explicit lemma is needed: the
  engine-agreement is dischargee'run-bundle form `solution_of_loop_via_runData`. -/

/-- The `hspec`-side agreement is the BitProgram constructor-collapse. Said form:
    class-of-engine `eng`'s `sbit` evaluates at each threshold to whatever response the engine
    constructed. -/
theorem hspec_via_engineOf {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h : QMCLeafB.BitProgram.Sound o)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.EngineRuntime.answerBit (QMCLeafB.BitProgram.engineOf o h G) t = o G t :=
  QMCLeafB.BitProgram.answerBit_engineOf o h G t

end QMCLeafB.ClosingBracket
end


