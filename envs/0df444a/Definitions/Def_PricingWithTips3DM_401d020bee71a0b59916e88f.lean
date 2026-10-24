-- Prove2me | Definitions.Def_PricingWithTips3DM_401d020bee71a0b59916e88f
-- name    : PricingWithTips3DM_401d020bee71a0b59916e88f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:50:08.083231+00:00
-- url     : https://prove2.me/theorems/0392f16a-afce-4700-82d0-782357cf2f71
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeDenseTableSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_0a86702738a5c2a52d5525ca
import Definitions.Def_PricingWithTips3DM_a38456326d7cda81d9ab9d0a
import Definitions.Def_PricingWithTips3DM_e58fd6b74f120a88d8a5f9c8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Semantic correctness of the native sparse-edge/dense-table pipeline. -/

namespace PricingWithTips.FixedShapeDenseTableSemantics

open CLRS.Chapter34
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeCell
open PricingWithTips.FixedShapeSparseCells
open PricingWithTips.FixedShapeOrdinal
open PricingWithTips.FixedShapeTrueEdgesTM2
open PricingWithTips.FixedShapeFalseEdgesTM2
open PricingWithTips.FixedShapeJunkEdgesTM2
open PricingWithTips.FixedShapeLiteralSelectorTM2
open PricingWithTips.FixedShapeLiteralSelectorSemantics
open PricingWithTips.FixedShapeDenseTableTM2
open PricingWithTips.FixedShapeEncoding
open PricingWithTips.FixedShapeQueryStream
open PricingWithTips.FixedShapeBatchSemantics

theorem query_mem_trueEdges_iff (input : List CNFSym)
    (t : FixedShapeCell.Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, ordinal (dimension input) t) ∈ trueEdges input ↔
      trueCell input t = true := by
  rw [trueEdges_eq_sparse]
  constructor
  · intro hedge
    obtain ⟨u, hu, hedgeEq⟩ := List.mem_map.mp hedge
    have htrueu := (mem_trueTriples_iff input u).mp hu
    have hcellu : cell input u = true := by simp [cell, htrueu]
    rcases cell_true_bounds input u hcellu with ⟨hub, hus, hud⟩
    have hord : ordinal (dimension input) u = ordinal (dimension input) t :=
      congrArg Prod.snd hedgeEq
    have hut := ordinal_injective_of_lt (dimension input) u t
      hus hud hs hd hord
    simpa [hut] using htrueu
  · intro htrue
    exact List.mem_map.mpr
      ⟨t, (mem_trueTriples_iff input t).mpr htrue, rfl⟩

theorem query_mem_generatedEdges_iff (input : List CNFSym)
    (t : FixedShapeCell.Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, ordinal (dimension input) t) ∈ generatedEdges input ↔
      cell input t = true := by
  simp only [generatedEdges, List.mem_append,
    query_mem_trueEdges_iff input t hb hs hd,
    query_mem_falseEdges_iff input t hb hs hd,
    query_mem_junkEdges_iff input t hb hs hd,
    query_mem_literalEdges_iff input t hb hs hd,
    cell, Bool.or_eq_true]
  tauto

theorem denseBits_eq_table (input : List CNFSym) :
    denseBits input = table input := by
  unfold denseBits queries generatedInstance
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
  simpa [ordinal] using
    (query_mem_generatedEdges_iff input (b, s, d) hb' hs' hd')

end PricingWithTips.FixedShapeDenseTableSemantics


