-- Prove2me | Definitions.Def_QMCLeafB_hdasm
-- name    : QMCLeafB_hdasm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:56:10.913099+00:00
-- url     : https://prove2.me/theorems/fc52e5a3-e828-4b4c-abe7-18fe24162c89
-- title:
--   QMCLeafB hdasm
-- statement:
--   # leaf B phase 30 — m7: the template fires through the two-class `hd` reduction
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_solution_m1
import Definitions.Def_QMCLeafB_hd_m7
/-
# leaf B phase 30 — m7: the template fires through the two-class `hd` reduction

`Solutions/solution_m1.lean` states `SubM1.solution` with SIX inputs.  This file plugs
`HdM7.hd_of_bit_classes` into it, so that the template's `hd` input disappears into the two class
productions (W) and (E) and everything else stays verbatim.  The point is an *interface* receipt: the
reduction's `RunParts` term has the template's exact type, at the template's `Tbc2` and
`paramsKbc2`, with the template's own `loopBit`.

Consequently the campaign's remaining named obligations are exactly

  (1) init / round / verdict with their three `Poly` proofs,
  (2) the size ledger `M C₀ c kr` with `hkr/hMinv/hstep/hM`,
  (3) `hinitTape`,
  (4) `htop` on the top slice,
  (5) (W): bit `true` ⇒ a real unit-diagonal PSD point at `t + Rq/40000`,
  (6) (E): bit `false` ⇒ the relaxed body empty — needed only on `tEmpty G ≤ t < -Rq G/40000`
      by `HdM7Band.runParts_false_lowband`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HdAsmM7

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of `solution_m1` (it is `local` there, so it must be re-declared here). -/
local instance instRequestCodingHdAsm : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`d9f601e5` from the five remaining inputs plus the two `hd` classes.** -/
theorem solution_of_classes {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict SubM1.Tbc2 G t = true)
    (hW : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.loopBit init round verdict SubM1.Tbc2 G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.loopBit init round verdict SubM1.Tbc2 G t = false →
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) :
    QMCLeafB.Audit25M8.Target :=
  SubM1.solution k hk init round verdict hinit hr hv M C₀ c kr hkr hMinv hstep hM hinitTape htop
    (QMCLeafB.HdM7.hd_of_bit_classes
      (QMCLeafB.FinalStroke.loopBit init round verdict SubM1.Tbc2) hW hE)

#print axioms QMCLeafB.HdAsmM7.solution_of_classes

end QMCLeafB.HdAsmM7


