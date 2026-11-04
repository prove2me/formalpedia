-- Prove2me | Definitions.Def_QMCLeafB_assembly_fuel_m4
-- name    : QMCLeafB_assembly_fuel_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:09:13.023976+00:00
-- url     : https://prove2.me/theorems/526beb4a-7174-41e5-81db-aa331ba98e5e
-- title:
--   QMCLeafB assembly_fuel_m4
-- statement:
--   # leaf B phase 14 — `fuel-assembly` (swarm `smw1a99tp`, member m4, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_fuelwire_m4
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 14 — `fuel-assembly` (swarm `smw1a99tp`, member m4, direction d4)

The RSt conformance instance of the fuel wire: `Check_fuelwire_m4`'s
`solution_of_runParts_interior_halve` (the closing stroke at m2's per-order parameter family
`paramsHalve`, with the fuel, `hfuelLen`, `hspec` and every numeric slot discharged) applied to the
**concrete** `σ = RoundProgram.RSt` loop:

* `init := RStInit.init0` with `poly_init0` and `init0_tape` — m1's item 2 (`Check_initpoly_m1`);
* `round := RoundProgram.round` with `poly_round` — m3's `RoundProgram`;
* `verdict := RoundProgram.verdict` with `poly_verdict` — m3's read-out
  (`decide (0 < (stOks s).filter id).length`).

What is left of the leaf's `SolutionStatement` is then exactly three hypotheses:

1. `hd` — the `RunParts` bundle per bracketed interior `(G, t)` at `paramsHalve` (item 1, m5/d1);
2. `horbit` — the joint (state, fuel) orbit size ledger (m6/d5);
3. `htop` — the verdict bit is `true` on the closed top slice `[-Rq G/40000, 0]`.

Note the tolerance is `dq = 1`, which is what `init0` is built at (`MOf n = 2n² + 2`, i.e.
`initShapeOf (N*N) (2n² + 2·1²)`), so `RunParts.hwit`'s shape at `paramsHalve` is exactly
`MatQ.correct`'s conclusion for `stX (init0 p)`.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.FuelAssembly

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingFuelAssembly : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The loop's round count at `paramsHalve`. -/
noncomputable def T0Halve (G : QuantumMaxCutEnergy.Input) (_t : ℚ) : ℕ :=
  (QMCLeafB.FuelWire.paramsHalve G).K * (QMCLeafB.FuelWire.paramsHalve G).m

/-- **The concrete loop bit** of the RSt program at `paramsHalve`'s round count. -/
noncomputable def loopBitRSt : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
    QMCLeafB.RoundProgram.verdict T0Halve

theorem loopBitRSt_eq (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    loopBitRSt G t
      = QMCLeafB.RoundProgram.verdict
          (Nat.iterate QMCLeafB.RoundProgram.round
            ((QMCLeafB.FuelWire.paramsHalve G).K * (QMCLeafB.FuelWire.paramsHalve G).m)
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) := rfl

/-- **`d9f601e5` from the RSt run brick.**  The whole leaf at the concrete RSt program: items 2
(`init`), 3 (per-order halving and parameters) and 4 (fuel) are discharged, and the residuals are
exactly the run bundle, the orbit ledger and the top-slice verdict. -/
theorem solution_RSt (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : QMCLeafB.RoundProgram.RSt × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (QMCLeafB.RoundProgram.round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      loopBitRSt G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts (loopBitRSt) G t (QMCLeafB.FuelWire.paramsHalve G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_halve k hk
    QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    sizes horbit QMCLeafB.RStInit.init0_tape htop hd

end QMCLeafB.FuelAssembly

/-! ## Axiom audit -/

#print axioms QMCLeafB.FuelAssembly.T0Halve
#print axioms QMCLeafB.FuelAssembly.loopBitRSt_eq
#print axioms QMCLeafB.FuelAssembly.solution_RSt


