-- Prove2me | Definitions.Def_PricingWithTips3DM_47ce758a1b8edbdd7291bd45
-- name    : PricingWithTips3DM_47ce758a1b8edbdd7291bd45
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:23:01.891049+00:00
-- url     : https://prove2.me/theorems/9a7a82b6-39e9-456a-afe3-9d95bcb67b2a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextBranchRoute
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_e7e154daad0333a0009b2895
import Definitions.Def_PricingWithTips3DM_5a2dd8815216c377c022b769
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical routed outputs of branch-ending statements

The output of any statement whose linear spine ends in `branch` is the final
whole-row mux.  This file packages that row as a canonical list of wire
coordinates relative to an arbitrary affine statement context.  Unlike the
earlier label-family progression, this interface is compositional: a nested
branch can use it directly as one arm of its parent mux.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Canonical coordinate-order output row of a branch mux at `offset` from the
current statement context. -/
def transitionStmtBranchRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) : List Nat :=
  List.ofFn fun coordinate :
      Fin (cfgBitCount tm (workHeight tm seed.height)) =>
    ((seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height)) +
      offset.eval (workHeight tm seed.height) + 3 + 3 * coordinate.val

@[simp] theorem transitionStmtBranchRouteValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) :
    (transitionStmtBranchRouteValues tm seed labelOffset context offset).length =
      cfgBitCount tm (workHeight tm seed.height) := by
  simp [transitionStmtBranchRouteValues]

/-- The canonical branch route is exactly the semantic output row of the
original statement, even when either branch arm contains further branches. -/
theorem transitionStmtBranchRouteValues_eq_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (offset : TransitionAffineNat)
    (hoffset : transitionStmtFinalBranchMuxOffsetAffine tm q = some offset) :
    transitionStmtBranchRouteValues tm seed labelOffset context offset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          ((seed.start + labelOffset.eval seed.height) +
            context.gateOffset.eval (workHeight tm seed.height))
          (context.rowWires tm seed labelOffset) q hsupport) := by
  unfold transitionStmtBranchRouteValues transitionCfgWireValues
  rw [transitionStmtOutputWires_eq_finalBranchMux tm
    (workHeight tm seed.height) hwork seed.start (seed.start + 1)
    ((seed.start + labelOffset.eval seed.height) +
      context.gateOffset.eval (workHeight tm seed.height))
    (context.rowWires tm seed labelOffset) q hsupport offset hoffset]
  apply List.ofFn_inj.mpr
  funext coordinate
  unfold arithmeticMuxCfgWires
  simp only [Equiv.apply_symm_apply]

end CLRS.Chapter34.Turing.CookLevin


