-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:36:27.197022+00:00
-- url     : https://prove2.me/theorems/fce7b25b-565c-4ae2-befd-f8717466ee96
-- title:
--   Execution
-- statement:
--   Definitions and structural lemmas for Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Execution.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventScanKey_injective
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullEventQuery_correct

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
noncomputable instance geometricEventOrder (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : LinearOrder (Event P J radius) :=
  let order := LinearOrder.lift' (eventScanKey P J radius) (eventScanKey_injective P J radius)
  { order.toPartialOrder with
    le_total := order.le_total
    toDecidableLE := order.toDecidableLE
    toDecidableLT := order.toDecidableLT
    toDecidableEq := Subtype.instDecidableEq
    compare := fun a b => @compareOfLessAndEq (Event P J radius) a b order.toLT
      (order.toDecidableLT a b) Subtype.instDecidableEq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }
instance geometricEventMeasurableSpace (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : MeasurableSpace (Event P J radius) := ⊤
instance geometricEventMeasurableSingleton (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius : ℝ) : MeasurableSingletonClass (Event P J radius) :=
  ⟨fun _ => trivial⟩
noncomputable instance geometricBadDecidable (P : TannerSquarePresentation)
    (J : Vertex P → Space) (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    DecidablePred (· ∈ eventBad P J radius lambda K e) := fun p =>
  if h : (fullEventQuery P J radius lambda K e p).1 = true then
    isTrue ((fullEventQuery_correct P J radius lambda K e p).mp h)
  else isFalse (fun hp => h ((fullEventQuery_correct P J radius lambda K e p).mpr hp))
noncomputable def geometricOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    Vertex P → Space :=
  output (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
end QEC.Coding.BDL26RandomPerturbation


