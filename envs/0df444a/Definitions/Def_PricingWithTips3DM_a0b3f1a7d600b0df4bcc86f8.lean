-- Prove2me | Definitions.Def_PricingWithTips3DM_a0b3f1a7d600b0df4bcc86f8
-- name    : PricingWithTips3DM_a0b3f1a7d600b0df4bcc86f8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:41:57.246785+00:00
-- url     : https://prove2.me/theorems/70585208-c5d3-4322-87c3-ce06226ee956
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeTaggedKeysTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Position-tagged literal keys

The certificate pair generator distinguishes the clause and literal sections
by parity.  This fixed transducer maps a canonical literal key `(q,r)` to the
tagged key `(2*q, 2*r+1)`: clause vertices are even and literal vertices are
odd.  Same-section raw pairs can therefore never occur in the sparse table.
-/

noncomputable section

namespace PricingWithTips.FixedShapeTaggedKeysTM2

open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34
open _root_.Turing

abbrev Mode := Bool × Bool

private def startMode : Mode := (false, false)
private def clauseMode : Mode := (true, false)
private def literalMode : Mode := (false, true)
private def afterRecordMode : Mode := (true, true)

def spec : StatefulFlatMapSpec Mode CliqueSym CliqueSym where
  initial := startMode
  action mode symbol :=
    if mode = startMode then
      if symbol = .edgeMark then ([.edgeMark], clauseMode) else ([], startMode)
    else if mode = clauseMode then
      match symbol with
      | .tick => ([.tick, .tick], clauseMode)
      | .pairSep => ([.pairSep], literalMode)
      | .recordEnd => ([.pairSep, .tick, .recordEnd], afterRecordMode)
      | _ => ([], clauseMode)
    else if mode = literalMode then
      match symbol with
      | .tick => ([.tick, .tick], literalMode)
      | .recordEnd => ([.tick, .recordEnd], afterRecordMode)
      | _ => ([], literalMode)
    else if symbol = .edgeMark then ([.edgeMark], clauseMode)
    else ([], afterRecordMode)
  finish _ := []

def tagKeyStream (input : List CliqueSym) : List CliqueSym :=
  rewriteStatefulFlatMap spec input

noncomputable def tagKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id tagKeyStream :=
  statefulFlatMap_computableInPolyTime spec

private theorem clause_ticks (q : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec clauseMode
        (List.replicate q .tick ++ .pairSep :: tail) =
      List.replicate (2 * q) .tick ++ .pairSep ::
        rewriteStatefulFlatMapFrom spec literalMode tail := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: .tick ::
          rewriteStatefulFlatMapFrom spec clauseMode
            (List.replicate q .tick ++ .pairSep :: tail) = _
      rw [ih]
      simp [List.replicate_succ, Nat.mul_succ]

private theorem literal_ticks (r : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec literalMode
        (List.replicate r .tick ++ .recordEnd :: tail) =
      List.replicate (2 * r + 1) .tick ++ .recordEnd ::
        rewriteStatefulFlatMapFrom spec afterRecordMode tail := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      change .tick :: .tick ::
          rewriteStatefulFlatMapFrom spec literalMode
            (List.replicate r .tick ++ .recordEnd :: tail) = _
      rw [ih]
      simp [List.replicate_succ, Nat.mul_succ]

private theorem after_record (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec afterRecordMode
        (.edgeMark :: tail) =
      .edgeMark :: rewriteStatefulFlatMapFrom spec clauseMode tail := by
  rfl

private theorem prepend_eq (n : Nat) (tail : List CliqueSym) :
    prependCliqueTicks n tail = List.replicate n .tick ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prependCliqueTicks, List.replicate_succ, ih]

theorem one_key (q r : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec startMode
        (encodeCliqueEdge (q, r) ++ tail) =
      encodeCliqueEdge (2 * q, 2 * r + 1) ++
        rewriteStatefulFlatMapFrom spec afterRecordMode tail := by
  simp only [encodeCliqueEdge, prepend_eq, List.cons_append,
    List.append_assoc]
  rw [rewriteStatefulFlatMapFrom.eq_def]
  change .edgeMark :: rewriteStatefulFlatMapFrom spec clauseMode
      (List.replicate q .tick ++ .pairSep ::
        (List.replicate r .tick ++ .recordEnd :: tail)) = _
  rw [clause_ticks, literal_ticks]
  simp [encodeCliqueEdge, prepend_eq, List.append_assoc]

private theorem after_keys (keys : List (Nat × Nat)) :
    rewriteStatefulFlatMapFrom spec afterRecordMode
        (keys.flatMap encodeCliqueEdge) =
      (keys.map fun key => (2 * key.1, 2 * key.2 + 1)).flatMap
        encodeCliqueEdge := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      rcases key with ⟨q, r⟩
      rw [List.flatMap_cons]
      simp only [encodeCliqueEdge, prepend_eq, List.cons_append,
        List.append_assoc]
      rw [after_record, clause_ticks, literal_ticks]
      simp only [List.map_cons, List.flatMap_cons]
      simp only [List.nil_append]
      rw [ih]
      simp [encodeCliqueEdge, prepend_eq, List.append_assoc]

theorem tag_keys (keys : List (Nat × Nat)) :
    tagKeyStream (keys.flatMap encodeCliqueEdge) =
      (keys.map fun key => (2 * key.1, 2 * key.2 + 1)).flatMap
        encodeCliqueEdge := by
  unfold tagKeyStream rewriteStatefulFlatMap
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      rcases key with ⟨q, r⟩
      change rewriteStatefulFlatMapFrom spec startMode
          (encodeCliqueEdge (q, r) ++ keys.flatMap encodeCliqueEdge) = _
      rw [one_key, after_keys]
      simp only [List.map_cons, List.flatMap_cons]

def taggedGuardedBaseKeyStream (input : List CNFSym) : List CliqueSym :=
  tagKeyStream
    (PricingWithTips.FixedShapeGuardedKeysTM2.guardedBaseKeyStream input)

noncomputable def taggedGuardedBaseKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id taggedGuardedBaseKeyStream := by
  exact Classical.choice (TM2Comp.TM2ComputableInPolyTime.comp_scratch
    PricingWithTips.FixedShapeGuardedKeysTM2.guardedBaseKeyStream_computableInPolyTime
    tagKeyStream_computableInPolyTime)

end PricingWithTips.FixedShapeTaggedKeysTM2


