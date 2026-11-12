-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T11:33:17.080984+00:00
-- url     : https://prove2.me/theorems/e4ceb055-6a12-45bc-8654-f9edd647f7cd
-- title:
--   Native Finite Composition
-- statement:
--   Definitions and structural lemmas for Native Finite Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOutput
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_decode_encode_table
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_encodeTable
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decode_encode_table


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
local instance labelListMeasurable (A : Type*) [Countable A] :
    MeasurableSpace (List A) := ⊤
local instance labelListSingleton (A : Type*) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => trivial⟩
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
theorem measurable_comp_pointwise {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (g : Ω → A) (out : Ω → B)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ z, out z = f (g z)) : Measurable out := by
  have hm : Measurable (f ∘ g) := hf.comp hg
  have h : out = f ∘ g := funext he
  rw [h]
  exact hm
abbrev Rows (S : OddScale) (n : ℕ) := List (Vertex (Presentation S n) × Space)
def canonicalRows (S : OddScale) (n : ℕ) (J : Input S n) : Rows S n :=
  (vertexInputList (Presentation S n)).map (fun v => (v,J v))
def rowMap (S : OddScale) (n : ℕ) (I : Rows S n) : Input S n :=
  fun v => (pointRowQuery v I).1
namespace Paid
def Sim {A : Type*} (d : ℕ) (x y : A × ℕ) : Prop :=
  x.1=y.1 ∧ x.2 ≤ d*y.2
def initializePayload {N M : ℕ} (h : N=M)
    (read : Fin M → Space × ℕ) (L : List (Fin N)) :
    BDL26NativeStateRows.Run (SR.Rows (Fin M)) :=
  BDL26NativeStateRows.mapQ (fun i =>
    let a := Fin.cast h i
    let x := read a
    ⟨(a,0,x.1),x.2+6,1⟩) L
def incomingQ (S : OddScale) (n : ℕ) (I : Rows S n) :
    BDL26NativeStateRows.Run (SR.Rows (SR.Index S n)) :=
  let generated := BDL26NativePresentationGenerator.setupQ S n
  let size := BDL26NativeStateRows.lengthQ generated.1.data.vertices
  let addresses := BDL26NativeStateRows.indicesQ size.value
  let rows := initializePayload (BDL26NativeStateRows.length_value generated.1.data.vertices)
    (fun a => pointRowQuery (SR.decode S n a) I) addresses.value
  ⟨rows.value,generated.2+size.operations+addresses.operations+rows.operations+2,
    BDL26NativePresentationGenerator.allocatedRecords S n+
      size.allocations+addresses.allocations+rows.allocations+1⟩
def readSum {A : Type*} (L : List A) (read : A → Space × ℕ) : ℕ :=
  (L.map (fun a => (read a).2)).sum
def incomingExtra (S : OddScale) (n : ℕ) (I : Rows S n) : ℕ :=
  readSum (SR.indices (SR.count S n)) (fun a => pointRowQuery (SR.decode S n a) I)
def multiplier {S : OddScale} {n : ℕ} (I : Rows S n) : ℕ := 2*I.length+1
def pairQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (a b : MD.Code) : Bool × ℕ :=
  let A := NC.colorOfCodeQ S n a
  let B := NC.colorOfCodeQ S n b
  match A.value, B.value with
  | some (ca, xa), some (cb, xb) =>
      let I := incomingQ S n I
      let x := SR.readQ ca.1 I.value
      let y := SR.readQ cb.1 I.value
      let close := anchorCloseProgram.run (fun _ => y.value.2) x.value.2 r
      (decide (xa = xb) && close.1,
        A.operations+B.operations+I.operations+x.operations+y.operations+close.2+5)
  | _, _ => (false, A.operations+B.operations+2)
def eligibleQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (codes : MD.FourCodes) : Bool × ℕ :=
  listAllQuery (fun a => listAllQuery (pairQ S n I r a) (MC.codeList codes))
    (MC.codeList codes)
def codeCandidateQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r : ℝ) (row : Code S n) : Option (Code S n) × ℕ :=
  let q := eligibleQ S n I r row.val.1
  (if q.1 then some row else none, q.2+1)
def codeRawUniverseQ (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let generated := MC.masterCandidatesQ S n
  let scanned := filterMapQuery (codeCandidateQ S n I r) (MC.Rows S n).attach
  (scanned.1,generated.operations+scanned.2+1)
def codeUniverseQ (S : OddScale) (n : ℕ) (I : Rows S n) (r : ℝ) :
    List (Code S n) × ℕ :=
  let raw := codeRawUniverseQ S n I r
  let sorted := sortQuery (codeCompareQ S n) raw.1
  (sorted.1,raw.2+sorted.2)
def triangleCodeQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (c : MD.Code) (center : Space) : Bool × ℕ :=
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ c atlas.value
  match found.value with
  | none => (false,atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n I
      let x := pointQ S n lambda I.value R v.1
      let y := pointQ S n lambda I.value R v.2.1
      let z := pointQ S n lambda I.value R v.2.2
      let q := triangleQuery ![x.1,y.1,z.1] center 2
      (q.1,atlas.operations+found.operations+I.operations+x.2+y.2+z.2+q.2+4)
def centerQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (codes : MD.FourCodes) (g : Grid K) : Space × ℕ :=
  let anchor := anchorCodeQ codes
  let atlas := MD.atlasQ S n
  let found := MD.atlasReadQ anchor.1 atlas.value
  match found.value with
  | none => (0,anchor.2+atlas.operations+found.operations+1)
  | some v =>
      let I := incomingQ S n I
      let j := SR.readQ v.1 I.value
      let grid := gridPointQuery K g
      let point := pointSnapshotQuery lambda j.value.2 grid.1
      (point.1,anchor.2+atlas.operations+found.operations+I.operations+j.operations+grid.2+point.2+3)
def codeEventQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (lambda : ℝ) (K : ℕ) (row : Code S n)
    (R : SR.Rows (SR.Index S n)) : Bool × ℕ :=
  let net := gridListQuery K
  let query := listAnyQuery (fun g =>
    let center := centerQ S n I lambda K row.val.1 g
    let triangles := listAllQuery (fun c => triangleCodeQ S n I lambda R c center.1)
      (MC.codeList row.val.1)
    (triangles.1,center.2+triangles.2+2)) net.1
  (query.1,net.2+query.2+1)
def codeScanQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    Option (Code S n) × ℕ :=
  let candidates := codeUniverseQ S n I r
  let scan := scanQuery (codeEventQ S n I lambda K) candidates.1 R
  (scan.1,candidates.2+scan.2+1)
def canonicalExtra (S : OddScale) (n : ℕ) : ℕ :=
  incomingExtra S n (canonicalRows S n (fun _ => 0))
def readFee {A : Type*} [DecidableEq A] (a : A) : List A → ℕ
  | [] => 1
  | b::L => if b=a then 2 else readFee a L+2
def refreshFee {A : Type*} [DecidableEq A] (U : List A) : List A → ℕ
  | [] => 0
  | a::L => (BDL26NativeStateRows.memberQ a U).operations+
      (if (BDL26NativeStateRows.memberQ a U).value then 7 else 1)+refreshFee U L+3
abbrev State (S : OddScale) (n : ℕ) := SR.Rows (SR.Index S n) × Trace S n
def prefixQ (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → PrefixRun (State S n)
  | 0 => let q := SR.initializeQ S n T; ⟨(q.value,[]),q.operations+1⟩
  | m+1 =>
    let prior := prefixQ S n I r lambda K T m
    let chosen := codeScanQ S n I r lambda K prior.value.1
    let updated := SR.refreshQ T (codeSupport S n chosen.1) prior.value.1
    let appended := BDL26NativeMasterCandidates.appendQ prior.value.2 [chosen.1]
    ⟨(updated.value,appended.value),
      prior.operations+chosen.2+updated.operations+appended.operations+4⟩
def countedPrefix (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ → CountState S n
  | 0 => ((fun _ => 0),[],incomingBudget S n+1)
  | m+1 =>
    let prior := countedPrefix S n I r lambda K T m
    let chosen := codeScanQ S n I r lambda K (sampleRows S n T prior.1)
    (SR.advanceList (codeSupport S n chosen.1) prior.1,
      prior.2.1++[chosen.1],
      prior.2.2+chosen.2+refreshFee (codeSupport S n chosen.1)
        (SR.indices (SR.count S n))+(2*prior.2.1.length+1)+4)
def stopFromQ (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) : ℕ → State S n →
      PrefixRun (State S n × Option (List (SR.Index S n × Space)))
  | 0,state => ⟨(state,none),0⟩
  | fuel+1,state =>
    let query := codeScanQ S n I r lambda K state.1
    match query.1 with
    | none =>
      let out := BDL26NativeStateRows.emitQ state.1
      ⟨(state,some out.value),query.2+out.operations+3⟩
    | some row =>
      let refreshed := SR.refreshQ T (codeSupport S n (some row)) state.1
      let appended := BDL26NativeMasterCandidates.appendQ state.2 [some row]
      let rest := stopFromQ S n I r lambda K T fuel (refreshed.value,appended.value)
      ⟨rest.value,query.2+refreshed.operations+appended.operations+rest.operations+4⟩
def stopQ (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) (fuel : ℕ) :=
  let init := SR.initializeQ S n T
  let rest := stopFromQ S n I r lambda K T fuel (init.value,[])
  (⟨rest.value,init.operations+rest.operations+1⟩ :
    PrefixRun (State S n × Option (List (SR.Index S n × Space))))
def choice (S : OddScale) (n : ℕ) (I : Rows S n) (r lambda : ℝ) (K : ℕ)
    (T : NativeTable S n) (m : ℕ) : Option (Code S n) :=
  (codeScanQ S n I r lambda K (prefixQ S n I r lambda K T m).value.1).1
def emitted (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : List (SR.Index S n × Space) :=
  (BDL26NativeStateRows.emitQ
    (prefixQ S n I r lambda K T
      (nativeHaltTime S n (rowMap S n I) hr lambda K T)).value.1).value
def stoppedOperations (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℕ :=
  let prior := prefixQ S n I r lambda K T (nativeHaltTime S n (rowMap S n I) hr lambda K T)
  let terminal := codeScanQ S n I r lambda K prior.value.1
  let out := BDL26NativeStateRows.emitQ prior.value.1
  prior.operations+terminal.2+out.operations+3
def operationCost (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n (rowMap S n I) hr lambda K T then
    (stoppedOperations S n I hr lambda K T : ℝ≥0∞) else ∞
def additionalIncomingCost (S : OddScale) (n : ℕ) (I : Rows S n) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) : ℝ≥0∞ :=
  if NativeHalts S n (rowMap S n I) hr lambda K T then
    ((stoppedOperations S n I hr lambda K T-
      (BDL26NativeGeometricExecutionCost.stopQ S n (rowMap S n I) hr lambda K T
        (nativeHaltTime S n (rowMap S n I) hr lambda K T+1)).operations : ℕ) : ℝ≥0∞)
  else 0
end Paid
def perturbRowsQ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n)
    (W : List (SR.Index (perturbationOddScale p) n × Space)) :
    Rows (perturbationOddScale p) n × ℕ :=
  mapQuery (fun v =>
    let j := pointRowQuery v I
    let w := pointRowQuery ((SR.decode (perturbationOddScale p) n).symm v) W
    let q := pointSnapshotQuery p.lambda j.1 w.1
    ((v,q.1),j.2+w.2+q.2+3)) (vertexInputList (Presentation (perturbationOddScale p) n))
def nativePerturbed {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) : StageMaps p n :=
  perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda
    (nativeOutput (perturbationOddScale p) n J p T)
def successor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) : StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (nativePerturbed p n J T)
def perturbLabelCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (mapQuery (fun v : Vertex (StagePresentation p n) =>
    ((),labelReadCost v (vertexInputList (StagePresentation p n))+
      labelReadCost ((SR.decode (perturbationOddScale p) n).symm v)
        (SR.indices (SR.count (perturbationOddScale p) n))+24+3))
    (vertexInputList (StagePresentation p n))).2
def deterministicCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  perturbLabelCost p n+materializationLabelCost p n
def stageQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : Rows (perturbationOddScale p) n) (T : NativeTable (perturbationOddScale p) n) :
    Rows (perturbationOddScale p) (n+1) × ℝ≥0∞ :=
  let emitted := Paid.emitted _ n I (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T
  let perturbed := perturbRowsQ p n I emitted
  let materialized := materializeRows p n perturbed.1
  (materialized.1,Paid.operationCost _ n I (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda) T+(perturbed.2 : ℝ≥0∞)+(materialized.2 : ℝ≥0∞))
theorem measurable_nativePerturbed {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : JointInput (perturbationOddScale p) n => nativePerturbed p n z.1 z.2) := by
  apply measurable_pi_lambda
  intro v
  exact ((((measurable_pi_apply v).comp measurable_fst).const_smul (1/2 : ℝ)).const_smul
    (p.lambda : ℝ)).add ((measurable_pi_apply v).comp (measurable_joint_nativeOutput _ n p))
theorem measurable_successor {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : JointInput (perturbationOddScale p) n => successor p n z.1 z.2) :=
  (continuous_replacementOutput _ n (state _ n)).measurable.comp (measurable_nativePerturbed p n)
def jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : JointInput (perturbationOddScale p) n) : ℝ≥0∞ :=
  (stageQuery p n (canonicalRows _ n z.1) z.2).2
abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space
abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  NativeTable (perturbationOddScale p) n
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n
instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => successor p n (evaluate p n z.1) z.2
def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)
theorem measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        successor p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          successor p n w.1 w.2) := measurable_successor p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => successor p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair
def freshLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageTables p n) :=
  nativeTableMeasure (perturbationOddScale p) n p
instance freshLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (freshLaw p n) :=
  inferInstanceAs (IsProbabilityMeasure (nativeTableMeasure (perturbationOddScale p) n p))
def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (freshLaw p n)
instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (freshLaw p n))
      infer_instance
def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)
instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable
def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)
def run {L : ℝ} (p : GeometricParameters L) : (N : ℕ) → Experiment p N →
    Rows (perturbationOddScale p) N × ℝ≥0∞
  | 0, _ => (canonicalRows (perturbationOddScale p) 0 (BDL26RandomSeedEmbedding.seedPoint _),0)
  | N+1,z =>
    let prior := run p N z.1
    let next := stageQuery p N prior.1 z.2
    (next.1,prior.2+next.2)
def inputRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Rows (perturbationOddScale p) i.val :=
  (run p i.val (experimentPrefix p i.val N (by omega) z)).1
def stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ :=
  (stageQuery p i.val (inputRows p N i z) (tableAt p N i z)).2
def totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  (run p N z).2
def stageHalts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  NativeHalts (perturbationOddScale p) i.val (stageInput p N i z) (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)
def stageGood {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z) ∈
    BDL26NativeGeometricAvoidance.NativeGood (perturbationOddScale p) i.val
      (stageInput p N i z) p
def finiteSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) : Set (Experiment p N) :=
  {z | (∀ i : Fin N, stageHalts p N i z ∧ stageGood p N i z) ∧
    ∀ i : Fin (N+1), IsBoundedDensityLocalMap (StagePresentation p i.val) (history p N z i) p.t}
def nativeCoefficient {L : ℝ} (p : GeometricParameters L) : ℕ :=
  nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)
def stageBudget {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (2*Fintype.card (Vertex (StagePresentation p n))+1)*
    (nativeCoefficient p*(stageQubits p n+1)^1772)+deterministicCost p n
def totalCoefficient {L : ℝ} (p : GeometricParameters L) : ℕ :=
  131*nativeCoefficient p+65568*66^2
namespace Decoded
def successor {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : BDL26FiniteEmbeddingExperiment.StageMaps p n)
    (T : OriginalTable (perturbationOddScale p) n) :
    BDL26FiniteEmbeddingExperiment.StageMaps p (n+1) :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda
      (result (Presentation (perturbationOddScale p) n)
        (NC.nativeKey (perturbationOddScale p) n)
        (NC.nativeKey_injective (perturbationOddScale p) n) J p T))
theorem successor_encoded {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : BDL26FiniteEmbeddingExperiment.StageMaps p n)
    (T : OriginalTable (perturbationOddScale p) n) :
    successor p n J T = BDL26NativeFiniteComposition.successor p n J
      (SR.encodeSamples (perturbationOddScale p) n T) := by
  have hd : decodedTable (perturbationOddScale p) n
      (SR.encodeSamples (perturbationOddScale p) n T) = T :=
    Resampling.VariableRelabeling.decode_encode_table (SR.decode (perturbationOddScale p) n) T
  have ho := nativeOutput_decoded (perturbationOddScale p) n J p
    (SR.encodeSamples (perturbationOddScale p) n T)
  have he : nativeOutput (perturbationOddScale p) n J p
      (SR.encodeSamples (perturbationOddScale p) n T) =
      result (Presentation (perturbationOddScale p) n)
        (NC.nativeKey (perturbationOddScale p) n)
        (NC.nativeKey_injective (perturbationOddScale p) n) J p T :=
    ho.trans (congrArg (fun t => result (Presentation (perturbationOddScale p) n)
      (NC.nativeKey (perturbationOddScale p) n)
      (NC.nativeKey_injective (perturbationOddScale p) n) J p t) hd)
  exact congrArg (fun out : Input (perturbationOddScale p) n =>
    replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
      (perturbedMap (Presentation (perturbationOddScale p) n) J p.lambda out)) he.symm
theorem measurable_successor {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (fun z : Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n =>
      successor p n z.1 z.2) := by
  have he : (fun z : Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n =>
      successor p n z.1 z.2) = (fun z => BDL26NativeFiniteComposition.successor p n z.1
        (SR.encodeSamples (perturbationOddScale p) n z.2)) :=
    funext (fun z => successor_encoded p n z.1 z.2)
  rw [he]
  exact measurable_comp_pointwise
    (Ω := Input (perturbationOddScale p) n × OriginalTable (perturbationOddScale p) n)
    (A := JointInput (perturbationOddScale p) n)
    (B := BDL26FiniteEmbeddingExperiment.StageMaps p (n+1))
    (fun w => BDL26NativeFiniteComposition.successor p n w.1 w.2)
    (fun z => (z.1,SR.encodeSamples (perturbationOddScale p) n z.2)) _
    (BDL26NativeFiniteComposition.measurable_successor p n)
    (measurable_fst.prodMk
      ((Resampling.VariableRelabeling.measurable_encodeTable (SR.decode _ n)).comp measurable_snd))
    (fun _ => rfl)
abbrev StageMaps {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Vertex (state (perturbationOddScale p) n).presentation → Space
abbrev StageTables {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)
def Experiment {L : ℝ} (p : GeometricParameters L) : ℕ → Type
  | 0 => Unit
  | n+1 => Experiment p n × StageTables p n
instance experimentMeasurableSpace {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → MeasurableSpace (Experiment p n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n+1 => (experimentMeasurableSpace p n).prod inferInstance
def experimentPrefix {L : ℝ} (p : GeometricParameters L) (m : ℕ) :
    (n : ℕ) → m ≤ n → Experiment p n → Experiment p m
  | 0, h, z => by
      have hm : m = 0 := by omega
      subst m
      exact z
  | n+1, h, z =>
      if he : m = n+1 then he.symm ▸ z
      else experimentPrefix p m n (by omega) z.1
def tableAt {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageTables p i.val :=
  fun z => (experimentPrefix p (i.val+1) n i.isLt z).2
def evaluate {L : ℝ} (p : GeometricParameters L) : (n : ℕ) → Experiment p n → StageMaps p n
  | 0, _ => BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)
  | n+1, z => successor p n (evaluate p n z.1) z.2
def history {L : ℝ} (p : GeometricParameters L) (n : ℕ) (z : Experiment p n)
    (i : Fin (n+1)) : StageMaps p i.val :=
  evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stageInput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val :=
  fun z => evaluate p i.val (experimentPrefix p i.val n (by omega) z)
def stagePair {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    Experiment p n → StageMaps p i.val × StageTables p i.val :=
  fun z => (stageInput p n i z, tableAt p n i z)
theorem measurable_evaluate {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        successor p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          successor p n w.1 w.2) := measurable_successor p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => successor p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair
def freshLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageTables p n) :=
  tableMeasure (Presentation (perturbationOddScale p) n) p
instance freshLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (freshLaw p n) :=
  inferInstanceAs (IsProbabilityMeasure (tableMeasure (Presentation (perturbationOddScale p) n) p))
def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (freshLaw p n)
instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (freshLaw p n))
      infer_instance
def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)
instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable
def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)
end Decoded
def decodeExperiment {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Experiment p N → Decoded.Experiment p N
  | 0,_ => ()
  | N+1,z => (decodeExperiment p N z.1,decodedTable (perturbationOddScale p) N z.2)
def encodeExperiment {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Decoded.Experiment p N → Experiment p N
  | 0,_ => ()
  | N+1,z => (encodeExperiment p N z.1,SR.encodeSamples (perturbationOddScale p) N z.2)
namespace Paid
def prefixObservation (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (SR.Index S n → ℕ × Space) × Trace S n × ℕ :=
  ((fun a => (SR.readQ a (prefixQ S n I r lambda K T m).value.1).value),
    (prefixQ S n I r lambda K T m).value.2,(prefixQ S n I r lambda K T m).operations)
end Paid
abbrev StageObservation {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  StageMaps p n ×
  (ℕ → (SR.Index (perturbationOddScale p) n → ℕ × Space) × Trace (perturbationOddScale p) n × ℕ) ×
  (ℕ → Option (Code (perturbationOddScale p) n)) × Bool × ℕ ×
  StageMaps p n × StageMaps p n × StageMaps p (n+1) × ℝ≥0∞
def jointObservation {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : JointInput (perturbationOddScale p) n) : StageObservation p n :=
  (z.1,
   (fun time => Paid.prefixObservation _ n (canonicalRows _ n z.1)
     (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) z.2 time),
   (fun time => BDL26NativeGeometricJointExecution.codedChoice _ n z.1
     (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 time),
   (if NativeHalts _ n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 then true else false),
   nativeHaltTime _ n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2,
   nativeOutput _ n z.1 p z.2,nativePerturbed p n z.1 z.2,successor p n z.1 z.2,
   jointStageCost p n z)
abbrev Observation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) ×
  ((i : Fin N) → StageObservation p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞
def observation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : Observation p N :=
  (history p N z,(fun i => jointObservation p i.val (stagePair p N i z)),
    (fun i => stageCost p N i z),totalCost p N z)
end QEC.Coding.BDL26NativeFiniteComposition


