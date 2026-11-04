-- Prove2me | Definitions.Def_QMCLeafB_runparts_top_m2
-- name    : QMCLeafB_runparts_top_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:56:59.449233+00:00
-- url     : https://prove2.me/theorems/c665e248-3271-42a2-8d37-0f781c9ddcf5
-- title:
--   QMCLeafB runparts_top_m2
-- statement:
--   # leaf B phase 13 — brick `runparts-top` (swarm `smw17fqzz`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_runparams_m2
import Definitions.Def_QMCLeafB_verdict_readout_m2
/-
# leaf B phase 13 — brick `runparts-top` (swarm `smw17fqzz`, member m2)

`QMCLeafB.FinalStroke.RunParts o G t P` is the *run half* of `RunData`: the recorded answer
sequence `ok`, the recorded cut stream `cd`, the margins `del`, and twelve fields.  This file
records the two structural facts about that bundle that shrink the work of building it:

* §1 **the `true` verdict is free.**  If a feasible witness at `t + εw` exists and the verdict bit
  is `true`, then `RunParts` holds with the *constant* run `ok ≡ true` and no cuts at all: every
  cut-side field of `RunParts` (`hwit hrho hcne hdel0 hcheck hle hcut`) is guarded by
  `ok k = false`, hence vacuous, and `hcert` does not look at `k`.  So the entire ellipsoid run is
  needed **only on the `false` side**.
* §2 **the top slice is decided by the identity.**  For `t ≥ -εw` the identity matrix is a witness
  (`VerdictSound.exists_trace_le_of_neg_eps_le`), so wherever the loop's verdict says `true` on
  `[-εw, 0]` the run bundle exists outright — no computation, no cut chain.  This is the
  `RunParts`-level form of `VerdictSound.soundEpsOnBracket_of_runData_interior`'s `htop` slot: that
  theorem asks the verdict to be `true` on the top slice and `hd` only strictly below it, and §2
  says the `hd` obligation on the top slice is then *automatic* rather than merely unasked.
* §3 the dual is *not* available: `tr (wMatrix G · X)` can be negative (take the signed cut
  `X = [[1,-1],[-1,1]]` on a single edge), so on the interior `t < -εw` a witness may well exist.
  The `false` side therefore needs the actual ellipsoid run, and the `true` side is what §1/§2
  reduce to a single certificate.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RunPartsTop

open QuantumMaxCutEnergy

local instance instRequestCodingRunPartsTop : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  `anyOk` of the constant-`true` run -/

/-- The constant-`true` run reports `true` at every positive round count. -/
theorem anyOk_const_true (T : ℕ) (hT : 1 ≤ T) :
    QMCLeafB.SimLoop.anyOk (fun _ => true) T = true := by
  cases T with
  | zero => omega
  | succ k =>
      rw [QMCLeafB.SimLoop.anyOk_succ]
      rfl

/-! ## 2.  The `true` verdict needs no cut at all -/

/-- **`RunParts` from a feasible witness, at verdict `true`.**  The run is the constant one:
`ok ≡ true`, the recorded cuts and margins arbitrary (`⟨0,0,0⟩`, `0`).  All twelve cut-side fields
are guarded by `ok k = false`, so they are vacuous; `hcert` is the given witness (it does not depend
on the round); `hverdict` is `anyOk_const_true`. -/
noncomputable def runParts_of_witness
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (P : QMCLeafB.FinalStroke.RunParams G) (hP : 1 ≤ P.K * P.m)
    (hcert : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (ho : o G t = true) :
    QMCLeafB.FinalStroke.RunParts o G t P where
  ok := fun _ => true
  cd := fun _ => ⟨0, 0, 0⟩
  del := fun _ => 0
  hcert := by
    intro _ _ _
    exact hcert
  hwit := by
    intro k _ hk
    exact absurd hk (by simp)
  hrho := by
    intro k _ hk
    exact absurd hk (by simp)
  hcne := by
    intro k _ hk
    exact absurd hk (by simp)
  hdel0 := by
    intro k _ hk
    exact absurd hk (by simp)
  hcheck := by
    intro k _ hk
    exact absurd hk (by simp)
  hle := by
    intro k _ hk
    exact absurd hk (by simp)
  hcut := by
    intro k _ hk
    exact absurd hk (by simp)
  hverdict := by
    rw [ho]
    exact (anyOk_const_true (P.K * P.m) hP).symm

/-- **`RunParts` on the top slice of the bracket.**  For `t ≥ -εw` the identity is a unit-diagonal
semidefinite witness with trace `0 ≤ t + εw`, so wherever the loop says `true` the run bundle is
automatic. -/
noncomputable def runParts_top_slice
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (P : QMCLeafB.FinalStroke.RunParams G) (hP : 1 ≤ P.K * P.m)
    (htop : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ))
    (ho : o G t = true) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  runParts_of_witness P hP
    ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, by
      rw [QMCLeafB.FinishLine.one_trace_eq_zero]
      have heps := QMCLeafB.VerdictSound.eps_nonneg G
      linarith⟩
    ho

/-! ## 3.  Axiom audit -/

#print axioms QMCLeafB.RunPartsTop.anyOk_const_true
#print axioms QMCLeafB.RunPartsTop.runParts_of_witness
#print axioms QMCLeafB.RunPartsTop.runParts_top_slice

end QMCLeafB.RunPartsTop


