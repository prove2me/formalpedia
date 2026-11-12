-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:51:42.768398+00:00
-- url     : https://prove2.me/theorems/808ea170-1e15-4268-a3f9-9b4483481727
-- title:
--   Native Geometric Joint Execution
-- statement:
--   Definitions and structural lemmas for Native Geometric Joint Execution, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
abbrev Input (S : OddScale) (n : ℕ) := Vertex (Presentation S n) → Space
abbrev JointInput (S : OddScale) (n : ℕ) := Input S n × NativeTable S n
abbrev Code (S : OddScale) (n : ℕ) := GeneratedRow S n
instance codeFintype (S : OddScale) (n : ℕ) : Fintype (Code S n) :=
  Fintype.ofEquiv (MasterEvent (Presentation S n)) (MC.masterEquiv S n).symm
theorem code_countable (S : OddScale) (n : ℕ) : Countable (Code S n) :=
  (MC.masterEquiv S n).injective.countable
instance codeCountable (S : OddScale) (n : ℕ) : Countable (Code S n) :=
  code_countable S n
instance codeMeasurable (S : OddScale) (n : ℕ) : MeasurableSpace (Code S n) := ⊤
instance codeSingleton (S : OddScale) (n : ℕ) :
    MeasurableSingletonClass (Code S n) := ⟨fun _ => trivial⟩
abbrev Trace (S : OddScale) (n : ℕ) := List (Option (Code S n))
instance traceMeasurable (S : OddScale) (n : ℕ) : MeasurableSpace (Trace S n) := ⊤
instance traceSingleton (S : OddScale) (n : ℕ) :
    MeasurableSingletonClass (Trace S n) := ⟨fun _ => trivial⟩
local instance labelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance labelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
abbrev CountState (S : OddScale) (n : ℕ) :=
  (SR.Index S n → ℕ) × Trace S n × ℕ
def sampleRows (S : OddScale) (n : ℕ) (T : NativeTable S n)
    (c : SR.Index S n → ℕ) : SR.Rows (SR.Index S n) :=
  SR.rowsFor (SR.indices (SR.count S n)) T c
def eraseChoice (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    Option (LiveRow S n J r) → Option (Code S n) := Option.map Subtype.val
def codeSupport (S : OddScale) (n : ℕ) : Option (Code S n) → List (SR.Index S n)
  | none => []
  | some row => row.val.2.getD []
def codeCandidateQ (S : OddScale) (n : ℕ) (J : Input S n)
    (r : ℝ) (row : Code S n) : Option (Code S n) × ℕ :=
  let q := eligibleQ S n J r row.val.1
  (if q.1 then some row else none, q.2+1)
def codeCompareQ (S : OddScale) (n : ℕ) (a b : Code S n) : Bool × ℕ :=
  let A := fourKeyQ a.val.1
  let B := fourKeyQ b.val.1
  let compared := lexLEQuery A.1 B.1
  (compared.1,A.2+B.2+compared.2+1)
def codeRawUniverseQ (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let generated := MC.masterCandidatesQ S n
  let scanned := filterMapQuery (codeCandidateQ S n J r) (MC.Rows S n).attach
  (scanned.1,generated.operations+scanned.2+1)
def codeUniverseQ (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let raw := codeRawUniverseQ S n J r
  let sorted := sortQuery (codeCompareQ S n) raw.1
  (sorted.1,raw.2+sorted.2)
def codeEventQ (S : OddScale) (n : ℕ) (J : Input S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n)
    (R : SR.Rows (SR.Index S n)) : Bool × ℕ :=
  let net := gridListQuery K
  let query := listAnyQuery (fun g =>
    let center := centerQ S n J lambda K row.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n J lambda R c center.1)
      (MC.codeList row.val.1)
    (triangles.1,center.2+triangles.2+2)) net.1
  (query.1,net.2+query.2+1)
def codeScanQ (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    Option (Code S n) × ℕ :=
  let candidates := codeUniverseQ S n J r
  let scan := scanQuery (codeEventQ S n J lambda K) candidates.1 R
  (scan.1,candidates.2+scan.2+1)
def readFee {A : Type*} [DecidableEq A] (a : A) : List A → ℕ
  | [] => 1
  | b::L => if b=a then 2 else readFee a L+2
def refreshFee {A : Type*} [DecidableEq A] (U : List A) : List A → ℕ
  | [] => 0
  | a::L => (BDL26NativeStateRows.memberQ a U).operations+
      (if (BDL26NativeStateRows.memberQ a U).value then 7 else 1)+refreshFee U L+3
def countedPrefix (S : OddScale) (n : ℕ) (J : Input S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → CountState S n
  | 0 => ((fun _ => 0),[],incomingBudget S n+1)
  | m+1 =>
      let prior := countedPrefix S n J r lambda K T m
      let chosen := codeScanQ S n J r lambda K (sampleRows S n T prior.1)
      (SR.advanceList (codeSupport S n chosen.1) prior.1,
        prior.2.1++[chosen.1],
        prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
          (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)
def codedChoice (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :=
  eraseChoice S n J r (choice S n J hr lambda K T m)
def prefixObservation (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (SR.Index S n → ℕ × Space) × Trace S n × ℕ :=
  ((fun a => (SR.readQ a (prefixQ S n J hr lambda K T m).value.rows).value),
    (prefixQ S n J hr lambda K T m).value.trace.map (eraseChoice S n J r),
    (prefixQ S n J hr lambda K T m).operations)
def originalCode (S : OddScale) (n : ℕ) (J : Input S n) (r : ℝ)
    (e : Event S n J r) : Code S n :=
  (MC.masterEquiv S n).symm ⟨e.val,e.property.1⟩
instance nativeTable_probability (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) : IsProbabilityMeasure (nativeTableMeasure S n p) := by
  letI (a : SR.Index S n) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 (SR.decode S n a)
  change IsProbabilityMeasure (tableLaw (fun a : SR.Index S n =>
    vertexLaw (Presentation S n) ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m) (SR.decode S n a)))
  infer_instance
instance originalTable_probability (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) : IsProbabilityMeasure (tableMeasure (Presentation S n) p) := by
  letI (v : Vertex (Presentation S n)) := vertexLaw_probability (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  change IsProbabilityMeasure (tableLaw (vertexLaw (Presentation S n)
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)))
  infer_instance
def jointOutput (S : OddScale) (n : ℕ) {L : ℝ} (p : GeometricParameters L)
    (z : JointInput S n) : Input S n × Input S n := (z.1,nativeOutput S n z.1 p z.2)
def assignmentTable (S : OddScale) (n : ℕ) (w : Input S n) : NativeTable S n :=
  fun a => w (SR.decode S n a.1)
end QEC.Coding.BDL26NativeGeometricJointExecution


