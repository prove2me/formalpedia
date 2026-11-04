-- Prove2me | Definitions.Def_QMCLeafB_brick_rq_program
-- name    : QMCLeafB_brick_rq_program
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:15:32.98623+00:00
-- url     : https://prove2.me/theorems/f4291f3e-9399-4fd5-8eeb-3b7afe9dd9fc
-- title:
--   QMCLeafB brick_rq_program
-- statement:
--   # leaf B phase 5 — brick `rq-program` (m8)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineRuntime_m6
/-
# leaf B phase 5 — brick `rq-program` (m8)

The total-weight program `hR` of `QMCLeafB.EngineRuntime.leafB_of_decider`:

    hR : Poly (fun a : Input × List Bool => Rq a.1)

`Rq G = 2 * ∑ e, (G.weights e : ℚ)` is the start width of the leaf's bisection (the bracket is
`(−Rq G, 0)`), so the closing theorem needs it as a polynomial-time program read off the request
encoding `QuantumMaxCutEnergy.encodeRequest`.

The Def layer (`Definitions.Def_QuantumMaxCutFiniteNumericRuntime`) already has both halves, so
nothing new is computed here — this file is the wiring:

* `QMCNumericRuntime.requestEdgesProgram` parses the encoded request into the weighted edge list
  `inputEdges G` (endpoint slots zipped with the rational weights), self-delimiting against the
  random tape;
* `QMCNumericRuntime.edgeWeightSum_poly` sums the rational weights of such a list;
* `QMCNumericRuntime.inputEdges_weight_sum` says that sum is `∑ e, (G.weights e : ℚ)`.

`Rq` is that composite, doubled.

Contents:
* `Rq_eq_two_edgeWeightSum` — `Rq` is twice the Def edge-weight sum;
* `RqProgram` — the `PolyProgram` at the leaf's own encoder `encodeRequest`;
* `Rq_eq_two_weightsList`, `RqProgram_via_weights` — the same, redundantly, from the other Def
  parser (`requestWeightsProgram` composed with `PolyProgram.ratSum`), so the brick does not depend
  on a single parser route;
* `Rq_poly` — the `Poly` statement, in exactly the shape of `hR` and under exactly the
  `Coding` instance (`QMCLeafB.EngineRuntime.instRequestCoding'`) the closing theorem uses;
* `leafB_of_engine_bits'`, `leafB_of_decider_of_hR` — the closing theorem with the `hR` slot
  filled.  After this file `QMCLeafB.EngineRuntime.leafB_of_decider` needs the decider `o`, its agreement `hag` and its
  program `ho` only: the total weight is discharged;
* `oFeas`, `answerBit_answerTotal_wMatrix`, `leafB_of_feasBit_poly` — the residual stated exactly:
  the leaf's sentence from `Poly (fun p => QMCLeafB.EngineRuntime.feasBit (wMatrix p.1.1) p.2)` alone (the `bit-program`
  brick's target, consumed here);
* `Rq_poly_req`, `leafB_of_decider_of_hR_req` — the same statement under an independently declared
  request coding, so a merge cannot break the fit on the `Coding` instance;
* `RqProgram` (and `doubleProgram`) use no `Coding` instance at all, so they drop into any file
  importing the Def layer.

No `sorry`, no `axiom`; axiom audit at the end.
-/

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.BrickRQ

open QMCLeafB.EngineRuntime
open QMCLeafB.ThresholdDriver

/-! ## 1.  The mathematics: `Rq` is the doubled Def edge-weight sum -/

theorem Rq_eq_two_edgeWeightSum (G : QuantumMaxCutEnergy.Input) :
    Rq G = 2 * QMCNumericRuntime.edgeWeightSum (QMCNumericRuntime.inputEdges G) := by
  unfold Rq
  rw [QMCNumericRuntime.inputEdges_weight_sum]

/-! ## 2.  The program at the leaf's encoder -/

/-- Doubling a rational is a program. -/
noncomputable def doubleProgram : PolyProgram Ratio.encode Ratio.encode
    (fun q : ℚ => 2 * q) :=
  (Automatic.Poly.comp Automatic.Poly.rat_mul
    (Automatic.Poly.pair (Automatic.Poly.const (2 : ℚ)) Automatic.Poly.identity)).program

/-- **The total-weight program.**  Parse the request into its weighted edge list
(`requestEdgesProgram`), sum the weights (`edgeWeightSum_poly`), double. -/
noncomputable def RqProgram :
    PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) := by
  have hE : PolyProgram QuantumMaxCutEnergy.encodeRequest
      (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode))
      (fun a : QuantumMaxCutEnergy.Input × List Bool => QMCNumericRuntime.inputEdges a.1) :=
    QMCNumericRuntime.requestEdgesProgram
  have hW : PolyProgram
      (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode)) Ratio.encode
      QMCNumericRuntime.edgeWeightSum :=
    QMCNumericRuntime.edgeWeightSum_poly.program
  refine ((hE.comp hW).comp doubleProgram).congr _ ?_
  intro a
  exact (Rq_eq_two_edgeWeightSum a.1).symm

/-! ## 3.  The redundant route, through the weight-list parser

The Def layer offers a second, independent way to read the weights off the request
(`requestWeightsProgram`, no endpoint slots).  The same `hR` comes out of it, so the brick
survives a change of parser on either side. -/

theorem Rq_eq_two_weightsList (G : QuantumMaxCutEnergy.Input) :
    Rq G = 2 * ((QMCNumericRuntime.weightsList G).map (fun q : ℚ≥0 => (q : ℚ))).sum := by
  unfold Rq
  have h := congrArg (fun q : ℚ≥0 => (q : ℚ)) (QMCNumericRuntime.sum_weightsList G)
  push_cast at h
  rw [h]

/-- The same `hR`, from `requestWeightsProgram` and the rational list sum. -/
noncomputable def RqProgram_via_weights :
    PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) := by
  have hw : PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList Ratio.encode)
      (fun a : QuantumMaxCutEnergy.Input × List Bool =>
        (QMCNumericRuntime.weightsList a.1).map (fun q : ℚ≥0 => (q : ℚ))) :=
    QMCNumericRuntime.requestWeightsProgram
  have hs : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun a : QuantumMaxCutEnergy.Input × List Bool =>
        ((QMCNumericRuntime.weightsList a.1).map (fun q : ℚ≥0 => (q : ℚ))).sum) :=
    hw.comp OAI.MetricKMedian.Binary.PolyProgram.ratSum
  refine (hs.comp doubleProgram).congr _ ?_
  intro a
  exact (Rq_eq_two_weightsList a.1).symm

/-! ## 4.  The `Poly` statement in the closing theorem's own shape -/

local instance instEngineCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩


section RequestFinal


/-- **`hR`, the total-weight program of `QMCLeafB.EngineRuntime.leafB_of_decider`.** -/
theorem Rq_poly : Automatic.Poly
    (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) :=
  ⟨RqProgram⟩

/-- The redundant route gives the same statement. -/
theorem Rq_poly' : Automatic.Poly
    (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) :=
  ⟨RqProgram_via_weights⟩

end RequestFinal

/-! ## 5.  The closing theorem with the `hR` slot filled -/

/-- **The leaf, from a program for the thirteen answer bits.**  `leafB_of_engine_bits` with its
`hR` argument supplied by this brick; the only remaining hypothesis is a `PolyProgram` for the
engine's thirteen bits. -/
theorem leafB_of_engine_bits'
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hb : PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList encodeBool)
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        bitsOf (E request.1) 13 (-Rq request.1, 0))) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_engine_bits E hb RqProgram

/-- The same, through the redundant parser route. -/
theorem leafB_of_engine_bits''
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hb : PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList encodeBool)
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        bitsOf (E request.1) 13 (-Rq request.1, 0))) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  leafB_of_engine_bits E hb RqProgram_via_weights

section Decider




/-- **The leaf, from the single-query decider alone.**  `QMCLeafB.EngineRuntime.leafB_of_decider` with `hR` discharged:
`agm_classical_sdp_lower_value_tm2` (d9f601e5) follows from a Boolean decider `o` for the
threshold body, its agreement `hag` with the engine's answers, and one poly-time program `ho` for
it.  Phase 5's remaining obligation is `ho`. -/
theorem leafB_of_decider_of_hR
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), answerBit (E G) t = o G t)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.EngineRuntime.leafB_of_decider o E hag ho Rq_poly

end Decider

section Feasible




/-- The threshold-feasibility truth value of the leaf's instance `G`, at a rational threshold. -/
noncomputable def oFeas : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => QMCLeafB.EngineRuntime.feasBit (QMCLeafB.wMatrix G) t

/-- The classical answer's bit is the feasibility truth value, per instance. -/
theorem answerBit_answerTotal_wMatrix (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    answerBit (answerTotal (QMCLeafB.wMatrix G)) t = oFeas G t :=
  QMCLeafB.EngineRuntime.answerBit_answerTotal (QMCLeafB.wMatrix G) t

/-- **The exact residual of leaf B phase 5.**  With the total weight discharged here, the leaf's
sentence follows from one `Poly` statement: the feasibility predicate `QMCLeafB.EngineRuntime.feasBit` read off the
request encoding.  (Supplying that program is the `bit-program` brick; this theorem is only its
consumer, and instantiates nothing beyond `hR`.) -/
theorem leafB_of_feasBit_poly
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => oFeas p.1.1 p.2)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.EngineRuntime.leafB_of_decider oFeas (fun G => answerTotal (QMCLeafB.wMatrix G))
    (fun G t => answerBit_answerTotal_wMatrix G t) ho Rq_poly

end Feasible


/-! ## 6.  The same statement under a freshly declared request coding

Consumers (`QMCLeafB.EngineRuntime.leafB_of_decider`, m1's assembly, any merged file) each spell the request coding
themselves as `⟨encodeRequest⟩`.  That is *the same structure value* as
`QMCLeafB.EngineRuntime.instRequestCoding'`, so the statement below is the same `Poly` proposition;
it is recorded here with an independently declared instance so that neither the merge nor a
renaming of that instance can break the fit. -/

section FreshCoding

local instance instRequestCoding : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- `hR` under an independently declared request coding. -/
theorem Rq_poly_req : Automatic.Poly
    (fun a : QuantumMaxCutEnergy.Input × List Bool => Rq a.1) :=
  ⟨RqProgram⟩

/-- The closing theorem again, with `hR` supplied under the fresh coding. -/
theorem leafB_of_decider_of_hR_req
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (E : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, Answer (QMCLeafB.wMatrix G) t)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), answerBit (E G) t = o G t)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.EngineRuntime.leafB_of_decider o E hag ho Rq_poly_req

end FreshCoding

end QMCLeafB.BrickRQ

/-! ## Axiom audit -/

#print axioms QMCLeafB.BrickRQ.Rq_eq_two_edgeWeightSum
#print axioms QMCLeafB.BrickRQ.RqProgram
#print axioms QMCLeafB.BrickRQ.Rq_eq_two_weightsList
#print axioms QMCLeafB.BrickRQ.RqProgram_via_weights
#print axioms QMCLeafB.BrickRQ.Rq_poly
#print axioms QMCLeafB.BrickRQ.Rq_poly'
#print axioms QMCLeafB.BrickRQ.leafB_of_engine_bits'
#print axioms QMCLeafB.BrickRQ.leafB_of_engine_bits''
#print axioms QMCLeafB.BrickRQ.leafB_of_decider_of_hR
#print axioms QMCLeafB.BrickRQ.answerBit_answerTotal_wMatrix
#print axioms QMCLeafB.BrickRQ.leafB_of_feasBit_poly
#print axioms QMCLeafB.BrickRQ.Rq_poly_req
#print axioms QMCLeafB.BrickRQ.leafB_of_decider_of_hR_req


