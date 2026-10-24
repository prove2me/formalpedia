-- Prove2me | Definitions.Def_PricingWithTips3DM_858097c622c6feaeb2b60704
-- name    : PricingWithTips3DM_858097c622c6feaeb2b60704
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:03:48.621885+00:00
-- url     : https://prove2.me/theorems/2cd69fa3-ea39-4b2f-af96-b18c0fc37ed9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteRowSlices
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8f5a0e5f7c4d0ac6c65b2125
import Definitions.Def_PricingWithTips3DM_9a3f6d04d98bfcc3d719183a
import Mathlib.Algebra.BigOperators.Group.List.Basic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fixed-width row slices for stack routes

Cell routes are flattened for the affine source controller but grouped into
fixed-width symbol rows by the stack semantics.  These two generic lemmas
commute `take` and `drop` with that flattening at row boundaries.
-/

namespace List

/-- The length sum of a fixed-width row prefix is the requested row count
times the common width. -/
private theorem take_map_length_sum_eq_mul
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    ((rows.map length).take count).sum = count * width := by
  rw [← List.map_take]
  have hmap :
      (rows.take count).map length =
        (rows.take count).map (fun _ => width) := by
    apply List.map_congr_left
    intro row hrow
    exact hrows row (List.mem_of_mem_take hrow)
  rw [hmap]
  simp [hcount]

/-- Taking a whole number of fixed-width rows after flattening is the same as
taking those rows before flattening. -/
theorem flatten_take_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.take (count * width) = (rows.take count).flatten := by
  rw [← take_map_length_sum_eq_mul rows count width hcount hrows]
  exact List.take_sum_flatten rows count

/-- Dropping a whole number of fixed-width rows after flattening is the same
as dropping those rows before flattening. -/
theorem flatten_drop_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.drop (count * width) = (rows.drop count).flatten := by
  rw [← take_map_length_sum_eq_mul rows count width hcount hrows]
  exact List.drop_sum_flatten rows count

/-- Flattening fixed-width rows multiplies the row count by their width. -/
theorem flatten_length_fixedWidth
    {α : Type} (rows : List (List α)) (width : Nat)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.length = rows.length * width := by
  rw [List.length_flatten]
  have hmap :
      rows.map length = rows.map (fun _ => width) := by
    apply List.map_congr_left
    intro row hrow
    exact hrows row hrow
  rw [hmap]
  simp

/-- Removing one fixed-width row from the flattened suffix retains exactly
the preceding grouped rows. -/
theorem flatten_rdrop_one_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hlength : rows.length = count + 1)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.rdrop width = (rows.take count).flatten := by
  unfold List.rdrop
  rw [flatten_length_fixedWidth rows width hrows, hlength]
  have hsub : (count + 1) * width - width = count * width := by
    simp [Nat.add_mul]
  rw [hsub]
  exact flatten_take_fixedWidth rows count width (by omega) hrows

end List

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Descriptor-family prefix deletion commutes with projecting the first
coordinate of every generated row. -/
theorem transitionStackRouteFirstValues_drop
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    transitionStackRouteFirstValues
        (transitionStackRouteDropFamily amount progressions) =
      (transitionStackRouteFirstValues progressions).drop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteDropFamily_rows, List.map_drop]

/-- Descriptor-family suffix trimming commutes with projecting the first
coordinate of every generated row. -/
theorem transitionStackRouteFirstValues_trimSuffix
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    transitionStackRouteFirstValues
        (transitionStackRouteTrimSuffix amount progressions) =
      (transitionStackRouteFirstValues progressions).rdrop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteTrimSuffix_rows]
  unfold List.rdrop
  rw [List.map_take, List.length_map]

end CLRS.Chapter34.Turing.CookLevin


