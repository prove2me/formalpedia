-- Prove2me | Definitions.Def_PricingWithTips3DM_fe7acafb16602f26daa60f56
-- name    : PricingWithTips3DM_fe7acafb16602f26daa60f56
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:55:38.438274+00:00
-- url     : https://prove2.me/theorems/a1d79e1e-512e-42eb-af31-c1bf48ca55f8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteHeightActions
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a94d89ea25eb0a43c9e9c84a
import Definitions.Def_PricingWithTips3DM_6c6d3d95ade0edcb4d22e302
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Descriptor routes for primitive stack-height actions

This module crosses the first semantic boundary from normalized affine
descriptors to actual Cook--Levin stack actions.  It proves that the routed
height stream is exactly the height component produced by the list-valued
push and pop semantics on the real widened source stack.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- A descriptor-only push route: insert the false height wire and discard
the old bottom height coordinate. -/
noncomputable def transitionStackRoutePushHeightValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List Nat :=
  seed.start :: transitionStackRouteFirstValues
    (transitionStackRouteTrimSuffix 1
      (transitionStackRouteHeightProgressions tm seed k))

/-- A descriptor-only pop route.  At zero capacity pop is the identity;
otherwise it inserts the fresh top-height wire, drops the old top two
coordinates, and appends the false bottom coordinate. -/
noncomputable def transitionStackRoutePopHeightValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (fresh : Nat) : List Nat :=
  match workHeight tm seed.height with
  | 0 => transitionStackRouteFirstValues
      (transitionStackRouteHeightProgressions tm seed k)
  | _ + 1 => fresh :: transitionStackRouteFirstValues
      (transitionStackRouteDropFamily 2
        (transitionStackRouteHeightProgressions tm seed k)) ++ [seed.start]

/-- The height component read from the real widened source stack is exactly
the first-track stream of its two affine descriptors. -/
theorem transitionWidenedStackHeightValues_eq_routeSource
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (TransitionStackValueBlock.ofWires
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)).heightValues =
      transitionStackRouteFirstValues
        (transitionStackRouteHeightProgressions tm seed k) := by
  rw [transitionStackRouteHeightProgressions_values]
  unfold TransitionStackValueBlock.ofWires transitionStackHeightWireValues
    transitionWidenedFallbackStackHeightValues
  apply List.ofFn_inj.mpr
  funext index
  exact arithmeticWidenedCfgWires_stackHeight tm seed k index

/-- The descriptor push route agrees exactly with the height component of the
actual list-valued push operation, including zero capacity. -/
theorem transitionStackRoutePushHeightValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (symbol : SymbolWires tm k) :
    transitionStackRoutePushHeightValues tm seed k =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).push tm k (workHeight tm seed.height)
            seed.start symbol).heightValues := by
  have hsource :
      (TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).heightValues =
        transitionWidenedFallbackStackHeightValues tm seed k :=
    (transitionWidenedStackHeightValues_eq_routeSource tm seed k).trans
      (transitionStackRouteHeightProgressions_values tm seed k)
  have hlength :
      (TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).heightValues.length =
        workHeight tm seed.height + 1 := by
    simp [TransitionStackValueBlock.ofWires,
      transitionStackHeightWireValues]
  unfold transitionStackRoutePushHeightValues
  rw [transitionStackRouteHeightTrimSuffix_values]
  rw [← hsource]
  unfold List.rdrop
  rw [hlength]
  by_cases hzero : workHeight tm seed.height = 0
  · simp [TransitionStackValueBlock.push, hzero]
  · obtain ⟨height, hheight⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simp [TransitionStackValueBlock.push, hheight]

/-- The descriptor pop route agrees exactly with the height component of the
actual list-valued pop operation, including its zero-capacity identity case. -/
theorem transitionStackRoutePopHeightValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (fresh : Nat) :
    transitionStackRoutePopHeightValues tm seed k fresh =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).pop tm k (workHeight tm seed.height)
            seed.start (seed.start + 1) fresh).heightValues := by
  unfold transitionStackRoutePopHeightValues
  by_cases hzero : workHeight tm seed.height = 0
  · simp only [hzero, TransitionStackValueBlock.pop]
    exact (transitionWidenedStackHeightValues_eq_routeSource tm seed k).symm
  · obtain ⟨height, hheight⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simp only [hheight, TransitionStackValueBlock.pop]
    rw [transitionStackRouteHeightDrop_values]
    rw [← (transitionWidenedStackHeightValues_eq_routeSource tm seed k).trans
      (transitionStackRouteHeightProgressions_values tm seed k)]

end CLRS.Chapter34.Turing.CookLevin


