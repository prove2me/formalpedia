-- Prove2me | Definitions.Def_PricingWithTips3DM_e58fd6b74f120a88d8a5f9c8
-- name    : PricingWithTips3DM_e58fd6b74f120a88d8a5f9c8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:00:20.803732+00:00
-- url     : https://prove2.me/theorems/8874cf41-5e12-4e2b-b2f5-4c0ecb696158
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeBatchSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_db4e278a2acaaf8b3ea05b7b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Semantic connection between sparse ordinal edges and the dense table. -/

namespace PricingWithTips.FixedShapeBatchSemantics

open CLRS.Chapter34
open PricingWithTips.FixedShape3DM PricingWithTips.FixedShapeCell
open PricingWithTips.FixedShapeEncoding PricingWithTips.FixedShapeQueryStream
open PricingWithTips.FixedShapeSparseCells PricingWithTips.FixedShapeOrdinal

def sparseInstance (input : List CLRS.Chapter34.CNFSym) : CliqueInstance where
  vertexCount := dimension input ^ 3 + 1
  targetSize := 0
  edges := FixedShapeSparseCells.edges input

def pointwiseBits (I : CliqueInstance) (queries : List (Nat × Nat)) :
    List Bool :=
  queries.map fun edge => decide (edge ∈ I.edges)

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

theorem ordinal_enumeration (n : Nat) :
    (List.range n).flatMap (fun b =>
      (List.range n).flatMap (fun s =>
        (List.range n).map (fun d => (b * n + s) * n + d))) =
      List.range (n ^ 3) := by
  rw [show n ^ 3 = n * (n * n) by ring]
  rw [← range_blocks n (n * n)]
  apply congrArg (fun f => List.flatMap f (List.range n))
  funext b
  rw [← range_blocks n n]
  simp only [List.map_flatMap, List.map_map, Function.comp_apply]
  apply congrArg (fun f => List.flatMap f (List.range n))
  funext s
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply]
  ring

private theorem finRange_vals (n : Nat) :
    (List.finRange n).map (fun i => i.1) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

private theorem finRange_map_vals {α : Type} (n : Nat) (f : Nat → α) :
    (List.finRange n).map (fun i => f i.1) = (List.range n).map f := by
  calc
    _ = ((List.finRange n).map (fun i => i.1)).map f := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [finRange_vals]

private theorem finRange_flatMap_vals {α : Type} (n : Nat)
    (f : Nat → List α) :
    (List.finRange n).flatMap (fun i => f i.1) =
      (List.range n).flatMap f := by
  calc
    _ = ((List.finRange n).map (fun i => i.1)).flatMap f := by
      rw [List.flatMap_map]
    _ = _ := by rw [finRange_vals]

theorem table_eq_ranges (input : List CLRS.Chapter34.CNFSym) :
    table input =
      (List.range (dimension input)).flatMap (fun b =>
        (List.range (dimension input)).flatMap (fun s =>
          (List.range (dimension input)).map (fun d =>
            cell input (b, s, d)))) := by
  unfold table denseTable
  calc
    _ = (List.range (dimension input)).flatMap (fun b =>
        (List.finRange (dimension input)).flatMap (fun s =>
          (List.finRange (dimension input)).map (fun d =>
            cell input (b, s.1, d.1)))) :=
      finRange_flatMap_vals _ _
    _ = (List.range (dimension input)).flatMap (fun b =>
        (List.range (dimension input)).flatMap (fun s =>
          (List.finRange (dimension input)).map (fun d =>
            cell input (b, s, d.1)))) := by
      apply List.flatMap_congr
      intro b hb
      simpa using (finRange_flatMap_vals (dimension input)
        (fun s : Nat =>
          (List.finRange (dimension input)).map (fun d =>
            cell input (b, s, d.1))))
    _ = _ := by
      apply List.flatMap_congr
      intro b hb
      apply List.flatMap_congr
      intro s hs
      simpa using (finRange_map_vals (dimension input)
        (fun d : Nat => cell input (b, s, d)))

theorem queryMembershipBits_eq_table
    (input : List CLRS.Chapter34.CNFSym) :
    pointwiseBits (sparseInstance input) (queries input) =
      table input := by
  unfold pointwiseBits queries sparseInstance
  simp only [List.map_map, Function.comp_apply]
  rw [← ordinal_enumeration (dimension input)]
  simp only [List.map_flatMap, List.map_map, Function.comp_apply]
  rw [table_eq_ranges]
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro s hs
  apply List.map_congr_left
  intro d hd
  have hb' : b < dimension input := List.mem_range.mp hb
  have hs' : s < dimension input := List.mem_range.mp hs
  have hd' : d < dimension input := List.mem_range.mp hd
  apply Bool.eq_iff_iff.mpr
  simpa [FixedShapeSparseCells.ordinal] using
    (query_mem_edges_iff_cell input (b, s, d) hb' hs' hd')

end PricingWithTips.FixedShapeBatchSemantics


