-- Prove2me | Definitions.Def_PricingWithTips3DM_0dd2a1f65dab48349fe246d7
-- name    : PricingWithTips3DM_0dd2a1f65dab48349fe246d7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:36:56.749516+00:00
-- url     : https://prove2.me/theorems/84501712-157d-4bf5-a750-30ae8c4def4f
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeEncoding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_8bb7a9085d938ded48e0f995
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Exact dense incidence encoding of the fixed-shape reduction. -/

namespace PricingWithTips.FixedShapeEncoding

open PricingWithTips.FixedShape3DM PricingWithTips.FixedShapeCell

def denseTable (n : ℕ) (edge : Fin n → Fin n → Fin n → Bool) : List Bool :=
  (List.finRange n).flatMap fun b =>
    (List.finRange n).flatMap fun s =>
      (List.finRange n).map fun d => edge b s d

theorem denseTable_congr {n : ℕ} {edge edge' : Fin n → Fin n → Fin n → Bool}
    (h : ∀ b s d, edge b s d = edge' b s d) :
    denseTable n edge = denseTable n edge' := by
  unfold denseTable
  apply List.flatMap_congr
  intro b hb
  apply List.flatMap_congr
  intro s hs
  apply List.map_congr_left
  intro d hd
  exact h b s d

theorem denseTable_length (n : ℕ)
    (edge : Fin n → Fin n → Fin n → Bool) :
    (denseTable n edge).length = n ^ 3 := by
  simp [denseTable, List.length_flatMap, Nat.pow_succ]
  ring

def table (input : List CLRS.Chapter34.CNFSym) : List Bool :=
  denseTable (dimension input) fun b s d =>
    cell input (b.1, s.1, d.1)

@[simp] theorem table_length (input : List CLRS.Chapter34.CNFSym) :
    (table input).length = dimension input ^ 3 := by
  exact denseTable_length _ _

theorem reduction_edge_eq_cell (input : List CLRS.Chapter34.CNFSym)
    (b s d : Fin (dimension input)) :
    (reduction input).2 b s d = cell input (b.1, s.1, d.1) := by
  change decide ((b, s, d) ∈ normalizedTriples input) = _
  exact (cell_eq_decide_normalized input (b, s, d)).symm

theorem encode_reduction_eq (input : List CLRS.Chapter34.CNFSym) :
    encodeThreeDMInstance (reduction input) =
      List.replicate (dimension input) true ++ [false] ++ table input := by
  change List.replicate (dimension input) true ++ [false] ++
      denseTable (dimension input) (reduction input).2 = _
  rw [denseTable_congr (reduction_edge_eq_cell input)]
  rfl

end PricingWithTips.FixedShapeEncoding


