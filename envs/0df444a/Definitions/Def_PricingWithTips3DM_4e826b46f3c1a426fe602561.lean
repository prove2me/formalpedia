-- Prove2me | Definitions.Def_PricingWithTips3DM_4e826b46f3c1a426fe602561
-- name    : PricingWithTips3DM_4e826b46f3c1a426fe602561
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:56:51.832854+00:00
-- url     : https://prove2.me/theorems/08fd3395-7cb8-44b3-995e-5155e002a8cf
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeTrueEdgesTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_b062d0f04915c2cc3bdb50d7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native sparse-edge generator for the true-ring family. -/

noncomputable section

namespace PricingWithTips.FixedShapeTrueEdgesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeBaselineTM2
open PricingWithTips.FixedShapeQueryStream

/-- Row-major ordinal stride of the triples `(2*r, r, r)`. -/
def trueStridePolynomial : Polynomial Nat :=
  2 * dimensionPolynomial ^ 2 + dimensionPolynomial + 1

def trueCountPolynomial : Polynomial Nat :=
  Polynomial.X * (Polynomial.X + 1)

@[simp] theorem trueStridePolynomial_eval (L : Nat) :
    trueStridePolynomial.eval L =
      2 * ((L + 1) * (L * 2)) ^ 2 + (L + 1) * (L * 2) + 1 := by
  simp [trueStridePolynomial]

@[simp] theorem trueCountPolynomial_eval (L : Nat) :
    trueCountPolynomial.eval L = (L + 1) * L := by
  simp [trueCountPolynomial]
  ring

def trueOrdinalFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    0 0 0 0 0 trueStridePolynomial trueCountPolynomial input

def trueEdgeStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatSpec (trueOrdinalFrames input)

def trueEdges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (List.range ((input.length + 1) * input.length)).map fun r =>
    (0, r * (2 * dimension input ^ 2 + dimension input + 1))

private theorem range_blocks (a b : Nat) :
    (List.range a).flatMap (fun i =>
      (List.range b).map (fun j => b * i + j)) =
      List.range (a * b) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_singleton, Nat.succ_mul]
      rw [List.range_add]
      congr
      simp [Nat.mul_comm]

theorem trueEdges_eq_sparse (input : List CLRS.Chapter34.CNFSym) :
    trueEdges input =
      (PricingWithTips.FixedShapeSparseCells.trueTriples input).map
        (fun t => (0,
          PricingWithTips.FixedShapeSparseCells.ordinal (dimension input) t)) := by
  unfold trueEdges
  rw [← range_blocks (input.length + 1) input.length]
  simp [PricingWithTips.FixedShapeSparseCells.trueTriples,
    PricingWithTips.FixedShapeSparseCells.ordinal,
    Hardness.Cert.SatToMatching3DCode.extIdxN,
    Hardness.Cert.SatToMatching3DCode.ringIdxN,
    List.map_flatMap, List.map_map, Function.comp_def]
  apply congrArg (fun f => List.flatMap f (List.range (input.length + 1)))
  funext i
  apply List.map_congr_left
  intro j hj
  congr 2
  ring

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

theorem trueOrdinalFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    trueOrdinalFrames input =
      (List.range ((input.length + 1) * input.length)).flatMap fun r =>
        encodeUnaryFrame
          [0, 0, r * (2 * dimension input ^ 2 + dimension input + 1)] := by
  simp [trueOrdinalFrames,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows_eq_ofFn,
    exactPolynomialAffineUnaryTripleProgression,
    affineUnaryTripleRowValues, List.ofFn_eq_map]
  simp only [dimension]
  have h := congrArg
    (List.flatMap fun r : Nat => encodeUnaryFrame
      [0, 0, r *
        (2 * ((input.length + 1) * (input.length * 2)) ^ 2 +
          (input.length + 1) * (input.length * 2) + 1)])
    (map_finRange_val ((input.length + 1) * input.length))
  simpa only [List.flatMap_map, Function.comp_apply, Nat.zero_add,
    Nat.mul_comm] using h

theorem trueEdgeStream_eq (input : List CLRS.Chapter34.CNFSym) :
    trueEdgeStream input = (trueEdges input).flatMap encodeCliqueEdge := by
  rw [trueEdgeStream, trueOrdinalFrames_eq]
  let ordinals :=
    (List.range ((input.length + 1) * input.length)).map fun r =>
      r * (2 * dimension input ^ 2 + dimension input + 1)
  have hframes :
      (List.range ((input.length + 1) * input.length)).flatMap
          (fun r => encodeUnaryFrame
            [0, 0, r * (2 * dimension input ^ 2 + dimension input + 1)]) =
        ordinals.flatMap fun n => encodeUnaryFrame [0, 0, n] := by
    simp [ordinals, List.flatMap_map]
  rw [hframes]
  rw [format_rows]
  simp [trueEdges, ordinals, List.flatMap_map]

noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id trueEdgeStream := by
  let source :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym)
      0 0 0 0 0 trueStridePolynomial trueCountPolynomial
  let formatter := statefulFlatMap_computableInPolyTime formatSpec
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    source formatter
  change Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap formatSpec
      (exactPolynomialAffineUnaryTripleProgressionFrameStream
        0 0 0 0 0 trueStridePolynomial trueCountPolynomial input))
  simpa [Function.comp_def] using Classical.choice composed

end PricingWithTips.FixedShapeTrueEdgesTM2


