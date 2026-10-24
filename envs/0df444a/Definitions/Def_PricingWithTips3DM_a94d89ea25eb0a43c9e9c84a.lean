-- Prove2me | Definitions.Def_PricingWithTips3DM_a94d89ea25eb0a43c9e9c84a
-- name    : PricingWithTips3DM_a94d89ea25eb0a43c9e9c84a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:54:12.742772+00:00
-- url     : https://prove2.me/theorems/f49aa475-56a1-4c4c-92ef-1c84c63984fc
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteHeightSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0494881124b985a9615d29a0
import Definitions.Def_PricingWithTips3DM_8970352f95a930544ed229af
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Stack-route normalization for the real widened height source

The widened source height vector has two affine pieces: public coordinates and
a fixed false overflow suffix.  This module connects the generic family
normalizers to that concrete Cook--Levin source, including routes that cross
the segment boundary at small tableau heights.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The two fixed descriptor segments of one widened stack-height vector. -/
noncomputable def transitionStackRouteHeightSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List TransitionWidenedFallbackSegment :=
  [transitionWidenedFallbackPublicHeightSegment tm k,
    transitionWidenedFallbackOverflowHeightSegment tm]

/-- Runtime progressions obtained from the fixed height-segment table. -/
noncomputable def transitionStackRouteHeightProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List AffineUnaryTripleProgression :=
  (transitionStackRouteHeightSegments tm k).map
    (transitionWidenedFallbackSegmentProgression seed)

/-- First-track values denoted by a family of affine triple progressions. -/
def transitionStackRouteFirstValues
    (progressions : List AffineUnaryTripleProgression) : List Nat :=
  (progressions.flatMap affineUnaryTripleProgressionRows).map fun row => row.1

/-- The two-segment descriptor family denotes the canonical widened height
source exactly. -/
theorem transitionStackRouteHeightProgressions_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteFirstValues
        (transitionStackRouteHeightProgressions tm seed k) =
      transitionWidenedFallbackStackHeightValues tm seed k := by
  unfold transitionStackRouteFirstValues
  simp only [transitionStackRouteHeightProgressions,
    transitionStackRouteHeightSegments, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  change
    transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackPublicHeightSegment tm k) ++
        transitionWidenedFallbackSegmentValues seed
          (transitionWidenedFallbackOverflowHeightSegment tm) = _
  rw [transitionWidenedFallbackPublicHeightSegment_values,
    transitionWidenedFallbackOverflowHeightSegment_values]
  exact (transitionWidenedFallbackStackHeightValues_eq_parts tm seed k).symm

/-- Carried prefix deletion on the concrete descriptor family is exactly
prefix deletion on the widened height source. -/
theorem transitionStackRouteHeightDrop_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (amount : Nat) :
    transitionStackRouteFirstValues
        (transitionStackRouteDropFamily amount
          (transitionStackRouteHeightProgressions tm seed k)) =
      (transitionWidenedFallbackStackHeightValues tm seed k).drop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteDropFamily_rows, List.map_drop]
  exact congrArg (List.drop amount)
    (transitionStackRouteHeightProgressions_values tm seed k)

/-- Suffix trimming on the concrete descriptor family is exactly suffix
trimming on the widened height source. -/
theorem transitionStackRouteHeightTrimSuffix_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (amount : Nat) :
    transitionStackRouteFirstValues
        (transitionStackRouteTrimSuffix amount
          (transitionStackRouteHeightProgressions tm seed k)) =
      (transitionWidenedFallbackStackHeightValues tm seed k).rdrop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteTrimSuffix_rows]
  unfold List.rdrop
  rw [List.map_take]
  have hvalues :
      ((transitionStackRouteHeightProgressions tm seed k).flatMap
          affineUnaryTripleProgressionRows).map (fun row => row.1) =
        transitionWidenedFallbackStackHeightValues tm seed k := by
    simpa only [transitionStackRouteFirstValues] using
      transitionStackRouteHeightProgressions_values tm seed k
  have hlength := congrArg List.length hvalues
  simp only [List.length_map] at hlength
  rw [hvalues, hlength]

end CLRS.Chapter34.Turing.CookLevin


