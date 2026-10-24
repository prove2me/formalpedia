-- Prove2me | Definitions.Def_PricingWithTips3DM_b062d0f04915c2cc3bdb50d7
-- name    : PricingWithTips3DM_b062d0f04915c2cc3bdb50d7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:53:41.572474+00:00
-- url     : https://prove2.me/theorems/b4f55295-8d84-4fbd-8f4d-3dbc004febab
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeSparseCells
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_67cd49331ca6f872d03ef334
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
Sparse list semantics for the four families of true cells in the fixed-shape
SAT-to-3DM gadget.  Unlike the dense table, this list has only polynomially
many generated records and is the intended right-hand input to the verified
batch membership machine.
-/

namespace PricingWithTips.FixedShapeSparseCells

open PricingWithTips.FixedShape3DM PricingWithTips.FixedShapeCell
open Hardness Hardness.Cert SatToMatching3DCode

abbrev Triple := FixedShapeCell.Triple

def trueTriples (input : List CLRS.Chapter34.CNFSym) : List Triple :=
  (List.range (input.length + 1)).flatMap fun i =>
    (List.range input.length).map fun j =>
      (extIdxN input.length i j 0,
        (ringIdxN input.length i j, ringIdxN input.length i j))

def falseTriples (input : List CLRS.Chapter34.CNFSym) : List Triple :=
  (List.range (input.length + 1)).flatMap fun i =>
    (List.range input.length).map fun j =>
      (extIdxN input.length i j 1,
        (ringIdxN input.length i j,
          ringIdxN input.length i
            (if j + 1 = input.length then 0 else j + 1)))

def testTriples (input : List CLRS.Chapter34.CNFSym) : List Triple :=
  (paddedCNF input).zipIdx.flatMap fun q => q.1.map fun l =>
    (extIdxN input.length l.var q.2 (bitOf l.polarity),
      (testIdxN input.length input.length q.2,
        testIdxN input.length input.length q.2))

def junkTriples (input : List CLRS.Chapter34.CNFSym) : List Triple :=
  (List.range input.length).flatMap fun j =>
    (List.range input.length).flatMap fun i =>
      (List.range (dimension input)).map fun w =>
        (w, (junkIdxN input.length input.length j i,
          junkIdxN input.length input.length j i))

def triples (input : List CLRS.Chapter34.CNFSym) : List Triple :=
  trueTriples input ++ falseTriples input ++ testTriples input ++
    junkTriples input

theorem mem_trueTriples_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    t ∈ trueTriples input ↔ trueCell input t = true := by
  rw [trueCell_iff]
  simp [trueTriples, eq_comm]

theorem mem_falseTriples_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    t ∈ falseTriples input ↔ falseCell input t = true := by
  rw [falseCell_iff]
  simp [falseTriples, eq_comm]

theorem mem_testTriples_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    t ∈ testTriples input ↔ testCell input t = true := by
  rw [testCell_iff]
  simp [testTriples, eq_comm]

theorem mem_junkTriples_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    t ∈ junkTriples input ↔ junkCell input t = true := by
  rw [junkCell_iff]
  simp [junkTriples, eq_comm]

theorem mem_triples_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    t ∈ triples input ↔ cell input t = true := by
  simp only [triples, List.mem_append, mem_trueTriples_iff,
    mem_falseTriples_iff, mem_testTriples_iff, mem_junkTriples_iff,
    cell, Bool.or_eq_true]
  tauto

/-- Row-major ordinal used by `FixedShapeQueryStream.queries`. -/
def ordinal (n : Nat) (t : Triple) : Nat :=
  (t.1 * n + t.2.1) * n + t.2.2

def edges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (triples input).map fun t => (0, ordinal (dimension input) t)

end PricingWithTips.FixedShapeSparseCells


