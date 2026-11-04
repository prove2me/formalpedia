-- Prove2me | Definitions.Def_QMCLeafB_conformance
-- name    : QMCLeafB_conformance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:49:34.228204+00:00
-- url     : https://prove2.me/theorems/aa869fca-68be-4de9-9d27-bd409dc8f30e
-- title:
--   QMCLeafB conformance
-- statement:
--   # leaf B phase 14 — `conformance` (swarm `smw1a99tp`, member m4, direction d8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_integration_m6
import Definitions.Def_QMCLeafB_fuelwire_m4
import Definitions.Def_QMCLeafB_topSlice
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_round_program_m3
import Definitions.Def_QMCLeafB_halve_perG_m2
/-
# leaf B phase 14 — `conformance` (swarm `smw1a99tp`, member m4, direction d8)

**Cross-brick conformance audit.**  Every brick of this phase is proved in its own file against its
own hypothesis shape; nothing so far forces those shapes to *agree*.  This file makes the agreement a
theorem: it assembles `FinishLine.SolutionStatement` from the union of the delivered bricks

* `init0 := RStInit.init0` with `poly_init0` / `init0_tape` — m1's item 2;
* `round := RoundProgram.round`, `verdict := RoundProgram.verdict` with `poly_round` /
  `poly_verdict` — m3's program;
* the numeric half at `rmax := RundataHalving.rmaxOf (G.n·G.n)`, `m := HalvePerG.mHalve (G.n·G.n)`,
  `dq := 1`, `K := Kbc (mHalve (G.n·G.n)) G` — m2's `hhalve_perG`/`rmaxOf_nonneg`/`one_le_mHalve`
  and m1's `budgetRounds_le_bitCost`, whose conclusion is `budgetRounds ≤ Kbc`
  (`FuelWire.budgetRounds_le_Kbc`);
* the fuel — m4's `FuelWire.fuelOfProd` at the same count, with `Automatic.Poly` and the exact length
  `Kbc (mHalve N) G · mHalve N` (`poly_Kbc_mHalve_mul`, `Kbc_mHalve_le_seed`);
* the size ledger — m6's `IntegrateM6.orbit_envelope`, which turns the one-step charge
  `(hMinv, hstep, hM)` into the orbit envelope `horbit`;
* the stroke — m4's `TopSliceRange.solution_of_runParts_interior_halve_hn`, i.e. the shelf's interior
  stroke with `htop` asked only for `2 ≤ G.n` (`Check_topslice_range_m4` shows the unrestricted form
  is false: at order one the loop's bit is `false` at every count).

Residual: exactly three items — m6's one-step size ledger, the top-slice verdict at `2 ≤ G.n`, and one
`RunParts` per interior `(G, t)` at `FuelWire.paramsHalve` (item 1).

No `sorry`, no `axiom`; audits at the end, including every brick's headline lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.Conformance

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingConformance : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The union theorem.**  `FinishLine.SolutionStatement` for the concrete RSt loop from the delivered
bricks: only the one-step round-size ledger (m6), the top-slice verdict at `2 ≤ G.n`, and the interior
run bundle (item 1) are left. -/
theorem solution_union (kf : ℕ) (hkf : 20 ≤ 2 ^ kf)
    (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (QMCLeafB.RoundProgram.round s) ≤ M s + c)
    (hstep : ∀ s, (enc (QMCLeafB.RoundProgram.round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.FuelWire.Kbc (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.FuelWire.paramsHalve G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.TopSliceRange.solution_of_runParts_interior_halve_hn kf hkf
    QMCLeafB.RStInit.init0 QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    QMCLeafB.RStInit.poly_init0 QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) kr)
    (QMCLeafB.IntegrateM6.orbit_envelope QMCLeafB.RoundProgram.round M C₀ c kr hkr
      hMinv hstep hM)
    QMCLeafB.RStInit.init0_tape htop hd

end QMCLeafB.Conformance

/-! ## Axiom audit — the assembled theorem and every brick's headline lemma -/

#print axioms QMCLeafB.Conformance.solution_union

-- m4 (fuel wire), item 4, and the top-slice range fix
#print axioms QMCLeafB.FuelWire.fuelOf_length
#print axioms QMCLeafB.FuelWire.poly_fuelOf
#print axioms QMCLeafB.FuelWire.endgame_of_fuel_interior
#print axioms QMCLeafB.FuelWire.solution_of_runParts_interior_monoF
#print axioms QMCLeafB.FuelWire.poly_Kbc_mHalve_mul
#print axioms QMCLeafB.FuelWire.Kbc_mHalve_le_seed
#print axioms QMCLeafB.TopSliceRange.soundEpsOnBracket_of_runData_interior_hn
#print axioms QMCLeafB.TopSliceRange.htop_interior_false

-- m1, item 2 (init as a Poly program)
#print axioms QMCLeafB.RStInit.poly_init0
#print axioms QMCLeafB.RStInit.init0_tape
#print axioms QMCLeafB.RStInit.stX_correct

-- m3, the round/verdict programs
#print axioms QMCLeafB.RoundProgram.poly_round
#print axioms QMCLeafB.RoundProgram.poly_verdict

-- m2, the per-order constants
#print axioms QMCLeafB.HalvePerG.hhalve_perG
#print axioms QMCLeafB.HalvePerG.paramsK

-- m1, the round-count estimate
#print axioms QMCLeafB.RoundCountEstimate.budgetRounds_le_bitCost

-- m6, the size ledger
#print axioms QMCLeafB.IntegrateM6.orbit_envelope
#print axioms QMCLeafB.IntegrateM6.solution_of_bricks


