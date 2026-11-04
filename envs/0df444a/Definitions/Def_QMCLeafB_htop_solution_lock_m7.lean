-- Prove2me | Definitions.Def_QMCLeafB_htop_solution_lock_m7
-- name    : QMCLeafB_htop_solution_lock_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:14:53.476131+00:00
-- url     : https://prove2.me/theorems/fa7fca71-97a1-4585-a318-d07adc8e0b01
-- title:
--   QMCLeafB htop_solution_lock_m7
-- statement:
--   # leaf B phase 16 — the statement lock at `roundGU` (swarm `smw1ez4a9`, member m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_roundGU_endgame_m7
/-
# leaf B phase 16 — the statement lock at `roundGU` (swarm `smw1ez4a9`, member m7)

The endgame `RoundGUEndgame.solution_roundGU_of_init_hd_round` concludes
`QMCLeafB.FinishLine.SolutionStatement`, which is *definitionally* the `d9f601e5` sentence
(`Check_brick_finish_line.solutionStatement_iff_wMatrix` is `Iff.rfl`).  This file writes that
sentence out verbatim and closes it by `exact`, so the coordinator's last node is a copy of
`solution_of_hd` below with the two open supplies filled in:

* `init` + its five facts (brick 1's rebuilt `init0`; `RStInit.init0` already satisfies four of them,
  the fifth — `hnorm` — is `RStInit.init_normalised`),
* `hd`: one `RunParts` bundle per interior `(G,t)` at the SHELF round and the `paramsKbc2` family
  (brick 4).

Everything else in the leaf — the program, the fuel, the round count and its side condition, the size
ledger, the halving, the budget, `htop`, the tape-freeness — is discharged.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open QuantumMaxCutEnergy

local instance instRequestCodingLock : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`d9f601e5`, verbatim, from the endgame.**  `QMCLeafB.FinishLine.SolutionStatement` is this
sentence by definition, so the proof is `exact`. -/
theorem solution_of_hd
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : OAI.MetricKMedian.Binary.Automatic.Poly init)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ p, QMCLeafB.RoundProgram.fvR (init p) = 0)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round init k hk hinit hnorm hfv hstT hmass
    hinitTape hd

/-- The same sentence in the `wMatrix` spelling, which is how the shelf states it. -/
theorem solution_of_hd_wMatrix
    (init : QMCLeafB.FuelWire.Pkg → QMCLeafB.RoundProgram.RSt) (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : OAI.MetricKMedian.Binary.Automatic.Poly init)
    (hnorm : ∀ p, (QMCLeafB.RoundProgram.stX (init p)).length
      = QMCLeafB.RoundProgram.stN (init p) * QMCLeafB.RoundProgram.stN (init p))
    (hfv : ∀ p, QMCLeafB.RoundProgram.fvR (init p) = 0)
    (hstT : ∀ p, QMCLeafB.RoundProgram.stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  solution_of_hd init k hk hinit hnorm hfv hstT hmass hinitTape hd

/-- The lock: the two spellings of the sentence agree with `SolutionStatement`, by `rfl`. -/
theorem solutionStatement_lock :
    QMCLeafB.FinishLine.SolutionStatement ↔
      ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Iff.rfl

#print axioms solution_of_hd
#print axioms solution_of_hd_wMatrix
#print axioms solutionStatement_lock


