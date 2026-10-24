-- Prove2me | Definitions.Def_PricingWithTips3DM_68d8756d3d1b4518f6d0de29
-- name    : PricingWithTips3DM_68d8756d3d1b4518f6d0de29
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:56:34.157684+00:00
-- url     : https://prove2.me/theorems/6394bff4-55b1-436b-841e-1631a2733eac
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralCandidatesTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_4df0781f09048295ca076ad8
import Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native Cartesian literal-candidate generation by reusing the verified
CLIQUE certificate pair generator.

Clause indices are represented by even certificate vertices `2*q`; literal
codes by odd vertices `2*r+1`.  In a certificate containing all evens first
and all odds second, exactly the even/odd raw pairs form the desired Cartesian
product.  A later fixed transducer filters those records and halves both unary
fields, yielding `(q,r)` without runtime multiplication or division.
-/

noncomputable section

namespace PricingWithTips.FixedShapeLiteralCandidatesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open _root_.Turing

def clauseCountPolynomial : Polynomial Nat := Polynomial.X
def literalCountPolynomial : Polynomial Nat := Polynomial.X

def evenVertexFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    0 2 clauseCountPolynomial input

def negativeOddVertexFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    1 4 literalCountPolynomial input

def positiveOddVertexFrames (input : List CNFSym) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    3 4 literalCountPolynomial input

def oddVertexFrames (input : List CNFSym) : List UnaryFrameSym :=
  negativeOddVertexFrames input ++ positiveOddVertexFrames input

noncomputable def evenVertexFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id evenVertexFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) 0 2 clauseCountPolynomial

noncomputable def negativeOddVertexFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id negativeOddVertexFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) 1 4 literalCountPolynomial

noncomputable def positiveOddVertexFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id positiveOddVertexFrames :=
  exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
    (Γ := CNFSym) 3 4 literalCountPolynomial

def encodeUnaryFramePair : UnaryFrameSym → UnaryFrameSym × UnaryFrameSym
  | .tick => (.tick, .tick)
  | .separator => (.tick, .separator)
  | .frameEnd => (.tick, .frameEnd)

def decodeUnaryFramePair : UnaryFrameSym → UnaryFrameSym → UnaryFrameSym
  | _, .tick => .tick
  | _, .separator => .separator
  | _, .frameEnd => .frameEnd

@[simp] theorem decode_encodeUnaryFramePair (symbol : UnaryFrameSym) :
    decodeUnaryFramePair (encodeUnaryFramePair symbol).1
      (encodeUnaryFramePair symbol).2 = symbol := by
  cases symbol <;> rfl

noncomputable def oddVertexFrames_computableInPolyTime :
    TM2ComputableInPolyTime id id oddVertexFrames :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeUnaryFramePair decodeUnaryFramePair decode_encodeUnaryFramePair
    negativeOddVertexFrames_computableInPolyTime
    positiveOddVertexFrames_computableInPolyTime

def vertexRecordSpec : StatefulFlatMapSpec Bool UnaryFrameSym CliqueSym where
  initial := true
  action atStart symbol :=
    match symbol with
    | .tick => (if atStart then [.vertexMark, .tick] else [.tick], false)
    | .separator =>
        (if atStart then [.vertexMark, .recordEnd] else [.recordEnd], true)
    | .frameEnd => ([], true)
  finish _ := []

def vertexRecordFormatter (input : List UnaryFrameSym) : List CliqueSym :=
  rewriteStatefulFlatMap vertexRecordSpec input

noncomputable def vertexRecordFormatter_computableInPolyTime :
    TM2ComputableInPolyTime id id vertexRecordFormatter :=
  statefulFlatMap_computableInPolyTime vertexRecordSpec

private theorem formatter_inside (count : Nat) (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom vertexRecordSpec false
        (List.replicate count .tick ++ .separator :: tail) =
      List.replicate count .tick ++ .recordEnd ::
        rewriteStatefulFlatMapFrom vertexRecordSpec true tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: rewriteStatefulFlatMapFrom vertexRecordSpec false
          (List.replicate count .tick ++ .separator :: tail) = _
      rw [ih]
      simp [List.replicate_succ]

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prependCliqueTicks, ih, List.replicate_succ, List.cons_append]

private theorem formatter_value_append (value : Nat)
    (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom vertexRecordSpec true
        (encodeUnaryFrameBlock value ++ tail) =
      encodeCliqueVertex value ++
        rewriteStatefulFlatMapFrom vertexRecordSpec true tail := by
  cases value with
  | zero => rfl
  | succ value =>
      simp only [encodeUnaryFrameBlock, List.replicate_succ,
        List.cons_append]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simp only [vertexRecordSpec]
      simp only [if_true, List.append_assoc, List.singleton_append,
        List.cons_append]
      change .vertexMark :: .tick ::
          rewriteStatefulFlatMapFrom vertexRecordSpec false
            (List.replicate value .tick ++ .separator :: tail) = _
      rw [formatter_inside]
      simp only [encodeCliqueVertex, prependCliqueTicks_eq_replicate,
        List.replicate_succ, List.cons_append, List.append_assoc,
        List.nil_append]
      rfl

theorem formatter_frame (values : List Nat) :
    vertexRecordFormatter (encodeUnaryFrame values) =
      values.flatMap encodeCliqueVertex := by
  unfold vertexRecordFormatter rewriteStatefulFlatMap encodeUnaryFrame
  change rewriteStatefulFlatMapFrom vertexRecordSpec true
      (values.flatMap encodeUnaryFrameBlock) = _
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.flatMap_cons, List.flatMap_cons, formatter_value_append]
      exact congrArg (encodeCliqueVertex value ++ ·) ih

def candidateVertices (input : List CNFSym) : List Nat :=
  (List.range input.length).map (2 * ·) ++
    (List.range input.length).map (fun v => 4 * v + 1) ++
    (List.range input.length).map (fun v => 4 * v + 3)

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

theorem evenFrames_eq (input : List CNFSym) :
    evenVertexFrames input =
      encodeUnaryFrame ((List.range input.length).map (2 * ·)) := by
  simp only [evenVertexFrames, exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn, clauseCountPolynomial,
    List.ofFn_eq_map, Polynomial.eval_X, Polynomial.eval_zero,
    Polynomial.eval_ofNat, Nat.zero_add, Nat.reduceMul]
  apply congrArg encodeUnaryFrame
  have h := congrArg (List.map fun r : Nat => r * 2)
    (map_finRange_val input.length)
  simpa only [List.map_map, Function.comp_def, Nat.mul_comm] using h

theorem oddFrames_eq (input : List CNFSym) :
    oddVertexFrames input =
      encodeUnaryFrame
        ((List.range input.length).map (fun v => 4 * v + 1) ++
          (List.range input.length).map (fun v => 4 * v + 3)) := by
  simp only [oddVertexFrames, negativeOddVertexFrames,
    positiveOddVertexFrames,
    exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn, literalCountPolynomial,
    List.ofFn_eq_map, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  simp only [encodeUnaryFrame, List.flatMap_append]
  apply congrArg₂ (· ++ ·)
  · have h := congrArg (List.map fun v : Nat => 4 * v + 1)
      (map_finRange_val input.length)
    apply congrArg (List.flatMap encodeUnaryFrameBlock)
    simpa only [List.map_map, Function.comp_def, Nat.add_comm,
      Nat.mul_comm, Polynomial.eval_ofNat] using h
  · have h := congrArg (List.map fun v : Nat => 4 * v + 3)
      (map_finRange_val input.length)
    apply congrArg (List.flatMap encodeUnaryFrameBlock)
    simpa only [List.map_map, Function.comp_def, Nat.add_comm,
      Nat.mul_comm, Polynomial.eval_ofNat] using h

def evenVertexRecords (input : List CNFSym) : List CliqueSym :=
  vertexRecordFormatter (evenVertexFrames input)

def oddVertexRecords (input : List CNFSym) : List CliqueSym :=
  vertexRecordFormatter (oddVertexFrames input)

noncomputable def evenVertexRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id evenVertexRecords := by
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    evenVertexFrames_computableInPolyTime
    vertexRecordFormatter_computableInPolyTime)

noncomputable def oddVertexRecords_computableInPolyTime :
    TM2ComputableInPolyTime id id oddVertexRecords := by
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    oddVertexFrames_computableInPolyTime
    vertexRecordFormatter_computableInPolyTime)

def certificateBody (input : List CNFSym) : List CliqueSym :=
  evenVertexRecords input ++ oddVertexRecords input

noncomputable def certificateBody_computableInPolyTime :
    TM2ComputableInPolyTime id id certificateBody := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    evenVertexRecords_computableInPolyTime oddVertexRecords_computableInPolyTime

def certificateMarkSpec : StatefulFlatMapSpec Unit CNFSym CliqueSym where
  initial := ()
  action _ _ := ([], ())
  finish _ := [.certificateMark]

def certificateMarkStream (input : List CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap certificateMarkSpec input

theorem certificateMarkStream_eq (input : List CNFSym) :
    certificateMarkStream input = [.certificateMark] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      change rewriteStatefulFlatMapFrom certificateMarkSpec ()
          (symbol :: input) = _
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact ih

noncomputable def certificateMarkStream_computableInPolyTime :
    TM2ComputableInPolyTime id id certificateMarkStream :=
  statefulFlatMap_computableInPolyTime certificateMarkSpec

def candidateCertificateStream (input : List CNFSym) : List CliqueSym :=
  encodeCliqueCertificate (candidateVertices input)

theorem candidateCertificateStream_eq (input : List CNFSym) :
    candidateCertificateStream input =
      certificateMarkStream input ++ certificateBody input := by
  simp only [certificateMarkStream_eq, certificateBody, evenVertexRecords,
    oddVertexRecords, evenFrames_eq, oddFrames_eq, formatter_frame]
  simp [candidateCertificateStream, candidateVertices,
    encodeCliqueCertificate, certificateBody, List.flatMap_append]

noncomputable def candidateCertificateStream_computableInPolyTime :
    TM2ComputableInPolyTime id encodeCliqueCertificate candidateVertices := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    certificateMarkStream_computableInPolyTime
    certificateBody_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← candidateCertificateStream_eq] at output
        exact output }

def rawCandidatePairs (input : List CNFSym) : List (Nat × Nat) :=
  PairGenerator.certificateRawPairs (candidateVertices input)

noncomputable def rawCandidatePairs_computableInPolyTime :
    TM2ComputableInPolyTime id
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      rawCandidatePairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    candidateCertificateStream_computableInPolyTime
    PairGenerator.rawPairs_computableInPolyTime
  change TM2ComputableInPolyTime id
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun input => PairGenerator.certificateRawPairs (candidateVertices input))
  simpa [Function.comp_def] using Classical.choice composed

end PricingWithTips.FixedShapeLiteralCandidatesTM2


