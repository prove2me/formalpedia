-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:47:11.099584+00:00
-- url     : https://prove2.me/theorems/8d51fd3a-8990-4596-b0f0-ad598d154186
-- title:
--   Native Geometric Execution Cost
-- statement:
--   Definitions and structural lemmas for Native Geometric Execution Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_event_injective

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
def prefixBudget (S : OddScale) (n K m : ℕ) : ℕ :=
  incomingBudget S n+1+
    m*(scanBudget S n K (SR.count S n)+35*SR.count S n+4)+m^2
structure StopObservation (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) where
  state : Prefix S n J r
  emitted : Option (List (SR.Index S n × Space))
def stopFromQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    ℕ → Prefix S n J r → PrefixRun (StopObservation S n J r)
  | 0, state => ⟨⟨state,none⟩,0⟩
  | fuel+1, state =>
      let query := scanQ S n J hr lambda K state.rows
      match query.1 with
      | none =>
          let emitted := BDL26NativeStateRows.emitQ state.rows
          ⟨⟨state,some emitted.value⟩,query.2+emitted.operations+3⟩
      | some row =>
          let refreshed := SR.refreshQ T (support S n J r row) state.rows
          let appended := BDL26NativeMasterCandidates.appendQ state.trace [some row]
          let rest := stopFromQ S n J hr lambda K T fuel ⟨refreshed.value,appended.value⟩
          ⟨rest.value,query.2+refreshed.operations+appended.operations+rest.operations+4⟩
def stopQ (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n)
    (fuel : ℕ) : PrefixRun (StopObservation S n J r) :=
  let initialized := SR.initializeQ S n T
  let rest := stopFromQ S n J hr lambda K T fuel ⟨initialized.value,[]⟩
  ⟨rest.value,initialized.operations+rest.operations+1⟩
def nativeOperationCost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n J hr lambda K T then
    ((stopQ S n J hr lambda K T
      (nativeHaltTime S n J hr lambda K T+1)).operations : ℝ≥0∞)
  else ∞
def executionBudget (S : OddScale) (n K m : ℕ) : ℕ :=
  prefixBudget S n K m+scanBudget S n K (SR.count S n)+5*SR.count S n+3
def operationConstantTerm (S : OddScale) (n K : ℕ) : ℕ :=
  incomingBudget S n+scanBudget S n K (SR.count S n)+5*SR.count S n+4
def operationLinearTerm (S : OddScale) (n K : ℕ) : ℕ :=
  scanBudget S n K (SR.count S n)+35*SR.count S n+4
instance liveRowFinite (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Finite (LiveRow S n J r) :=
  Finite.of_injective (event S n J r) (event_injective S n J r)
instance liveRowMeasurable (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    MeasurableSpace (LiveRow S n J r) := ⊤
instance liveRowSingleton (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    MeasurableSingletonClass (LiveRow S n J r) := ⟨fun _ => trivial⟩
def readLabelCost {A : Type*} [DecidableEq A] (a : A) : List A → ℕ
  | [] => 1
  | b::L => if b=a then 2 else readLabelCost a L+2
def refreshLabelCost {A : Type*} [DecidableEq A] (U : List A) : List A → ℕ
  | [] => 0
  | a::L => (BDL26NativeStateRows.memberQ a U).operations+
      (if (BDL26NativeStateRows.memberQ a U).value then 7 else 1)+
      refreshLabelCost U L+3
def expectedOperationBudget (S : OddScale) (n K D : ℕ) : ℕ :=
  operationConstantTerm S n K+
    operationLinearTerm S n K*(Fintype.card (Triangle (Presentation S n)))^4+
    2*(Fintype.card (Triangle (Presentation S n)))^8*(D+2)^2
def nativeOperationDegree : ℕ := 1772
def nativeOperationCoefficient (K D : ℕ) : ℕ :=
  (scanPolynomialConstant K+28)*132^1768+
    (scanPolynomialConstant K+39)*132^1768*65^4+2*65^8*(D+2)^2
end QEC.Coding.BDL26NativeGeometricExecutionCost


