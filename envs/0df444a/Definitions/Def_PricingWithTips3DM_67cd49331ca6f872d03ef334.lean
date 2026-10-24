-- Prove2me | Definitions.Def_PricingWithTips3DM_67cd49331ca6f872d03ef334
-- name    : PricingWithTips3DM_67cd49331ca6f872d03ef334
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:46:42.398922+00:00
-- url     : https://prove2.me/theorems/2d16c162-faa2-4aad-bfd6-fe02ca38dbef
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeQueryStream
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_0113804d1513567e5f178f47
import Definitions.Def_PricingWithTips3DM_4bd2af069f75145d9047c380
import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
import Definitions.Def_PricingWithTips3DM_cc9697f2568a1572df678eb7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
Generate the complete dense-table query stream with existing native TM2
components.  Cell ordinal `i` is represented by the normalized Clique edge
`(0, i)`.  This lets the verified batch edge lookup turn a sparse list of
true cell ordinals into the exact dense Boolean incidence table.
-/

noncomputable section

namespace PricingWithTips.FixedShapeQueryStream

open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34
open PricingWithTips.FixedShapeBaselineTM2
open PricingWithTips.FixedShape3DM

abbrev FormatMode := Option Bool

/-- Format a generated unary row `[0, 0, i]` as `encodeCliqueEdge (0, i)`. -/
def formatSpec : StatefulFlatMapSpec FormatMode UnaryFrameSym CliqueSym where
  initial := none
  action
    | none, .separator => ([.edgeMark], some false)
    | some false, .separator => ([.pairSep], some true)
    | some true, .tick => ([.tick], some true)
    | some true, .separator => ([.recordEnd], none)
    | mode, _ => ([], mode)
  finish _ := []

def ordinalFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    0 0 0 0 0 1 tablePolynomial input

def queryStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatSpec (ordinalFrames input)

def queries (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (List.range (dimension input ^ 3)).map fun i => (0, i)

private theorem prependCliqueTicks_eq_replicate (n : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks n tail = List.replicate n .tick ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

private theorem value_ticks (n : Nat) (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatSpec (some true)
        (List.replicate n .tick ++ .separator :: tail) =
      List.replicate n CliqueSym.tick ++ [.recordEnd] ++
        rewriteStatefulFlatMapFrom formatSpec none tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      change CliqueSym.tick ::
          rewriteStatefulFlatMapFrom formatSpec (some true)
            (List.replicate n .tick ++ .separator :: tail) = _
      rw [ih]
      rfl

theorem format_row (n : Nat) (tail : List UnaryFrameSym) :
    rewriteStatefulFlatMapFrom formatSpec none
        (encodeUnaryFrame [0, 0, n] ++ tail) =
      encodeCliqueEdge (0, n) ++
        rewriteStatefulFlatMapFrom formatSpec none tail := by
  simp only [encodeUnaryFrame, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, encodeUnaryFrameBlock, List.replicate_zero,
    List.nil_append, List.append_assoc]
  change rewriteStatefulFlatMapFrom formatSpec none
      (.separator :: .separator ::
        (List.replicate n .tick ++ .separator :: tail)) = _
  change CliqueSym.edgeMark :: CliqueSym.pairSep ::
      rewriteStatefulFlatMapFrom formatSpec (some true)
        (List.replicate n .tick ++ .separator :: tail) = _
  rw [value_ticks]
  simp [encodeCliqueEdge, prependCliqueTicks_eq_replicate]

theorem format_rows (ns : List Nat) :
    rewriteStatefulFlatMap formatSpec
        (ns.flatMap fun n => encodeUnaryFrame [0, 0, n]) =
      ns.flatMap fun n => encodeCliqueEdge (0, n) := by
  unfold rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom formatSpec none _ = _
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      rw [List.flatMap_cons]
      rw [format_row, ih]
      simp

theorem ordinalFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    ordinalFrames input =
      (List.range (dimension input ^ 3)).flatMap fun i =>
        encodeUnaryFrame [0, 0, i] := by
  simp [ordinalFrames,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows_eq_ofFn,
    exactPolynomialAffineUnaryTripleProgression,
    affineUnaryTripleRowValues, List.ofFn_eq_map]
  simp only [dimension]
  have h := congrArg
    (List.flatMap fun i : Nat => encodeUnaryFrame [0, 0, i])
    (map_finRange_val
      (((input.length + 1) * (input.length * 2)) ^ 3))
  simpa only [List.flatMap_map, Function.comp_apply] using h

theorem queryStream_eq (input : List CLRS.Chapter34.CNFSym) :
    queryStream input = (queries input).flatMap encodeCliqueEdge := by
  rw [queryStream, ordinalFrames_eq, format_rows]
  simp [queries, List.flatMap_map]

noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id queryStream := by
  let source :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym)
      0 0 0 0 0 1 tablePolynomial
  let formatter := statefulFlatMap_computableInPolyTime formatSpec
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    source formatter
  change Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap formatSpec
      (exactPolynomialAffineUnaryTripleProgressionFrameStream
        0 0 0 0 0 1 tablePolynomial input))
  simpa [Function.comp_def] using Classical.choice composed

end PricingWithTips.FixedShapeQueryStream


