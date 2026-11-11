-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:00:30.218975+00:00
-- url     : https://prove2.me/theorems/7fd2a5c1-7bd0-4124-9c1e-d211adfbe8d6
-- title:
--   Actual Execution Cost
-- statement:
--   Definitions and structural lemmas for Actual Execution Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable def actualScanQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r)) (R : StateRows P) : Option (Event P J r) × ℕ :=
  scanQuery (fun e R => stateEventQuery P J r lambda K e R) events R
noncomputable def actualStepQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) : StateRows P × ℕ :=
  let scan := actualScanQuery P J r lambda K events R
  match scan.1 with
  | none => (R,scan.2)
  | some e => let update := refreshStateRowsQuery P J r e T R
              (update.1,scan.2+update.2)
noncomputable def actualPrefixQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) : ℕ → StateRows P × ℕ
  | 0 => initialRowsQuery P T
  | n+1 => let priorRun := actualPrefixQuery P J r lambda K events T n
           let next := actualStepQuery P J r lambda K events T priorRun.1
           (next.1,priorRun.2+next.2)
open scoped Classical in
noncomputable def actualExecutionCost (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) : ℝ≥0∞ :=
  if Halts (eventSupport P J r) (eventBad P J r lambda K) T then
    let eventRows := eventUniverseQuery P J hr
    let priorRun := actualPrefixQuery P J r lambda K eventRows.1 T
      (haltTime (eventSupport P J r) (eventBad P J r lambda K) T)
    let finalScan := actualScanQuery P J r lambda K eventRows.1 priorRun.1
    let result := outputStateRowsQuery P J lambda priorRun.1
    (eventRows.2+priorRun.2+finalScan.2+result.2 : ℕ)
  else ∞
end QEC.Coding.BDL26RandomPerturbation


