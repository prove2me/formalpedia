-- Prove2me | Definitions.Def_PricingWithTips3DM_2636ce82c20efc281e868199
-- name    : PricingWithTips3DM_2636ce82c20efc281e868199
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:34:31.926922+00:00
-- url     : https://prove2.me/theorems/f1a80930-ed54-4f56-926c-3a7b24a18532
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackSourceAffine
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_7ada2cf993767e58b7faa8c2
import Definitions.Def_PricingWithTips3DM_76f3edf0f9cf98bff8b9f29f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Affine forms for fixed source-stack prefix coordinates

Continuation phases inspect a bounded prefix of the widened source after a
verifier-fixed push/pop route.  The published tableau height contains twice
the maximum number of stack actions, so every original coordinate that can
reach this prefix is still a genuine public-row coordinate.  This file gives
the corresponding affine forms for arbitrary fixed cells, extending the
cell-zero forms used by statement heads.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine public-row coordinate of one symbol bit in an arbitrary fixed
stack cell. -/
noncomputable def transitionWidenedStackCellForm
    (tm : _root_.Turing.FinTM2) (k : tm.K) (cell : Nat)
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    AffineUnaryTripleForm :=
  let heightSucc : TransitionAffineNat :=
    { constant := 1, coefficient := 1 }
  let cellOffset := TransitionAffineNat.const
    (code.val + ((reachableAlphabet tm k).card + 1) * cell)
  transitionAbsoluteRowBaseForm
    ((((TransitionAffineNat.const (transitionEqPrefixWidth tm)).add
      (transitionStackBitOffsetAffine tm k)).add heightSucc).add cellOffset)

/-- The generalized definition agrees definitionally with the established
cell-zero form. -/
theorem transitionWidenedStackCellForm_zero
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    transitionWidenedStackCellForm tm k 0 code =
      transitionWidenedStackCellZeroForm tm k code := by
  simp [transitionWidenedStackCellForm,
    transitionWidenedStackCellZeroForm, TransitionAffineNat.const,
    TransitionAffineNat.add]

/-- Every fixed cell below the public height evaluates to its literal
tableau-row wire inside the widened workspace. -/
theorem transitionWidenedStackCellForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (cell : Nat)
    (code : Fin ((reachableAlphabet tm k).card + 1))
    (hcell : cell < seed.height) :
    affineUnaryTripleFormValue
        (transitionWidenedStackCellForm tm k cell code)
        (transitionTailAffineSeed seed) =
      (arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stackCell k
          ⟨cell, lt_of_lt_of_le hcell (Nat.le_add_right _ _)⟩ code := by
  rw [transitionWidenedStackCellForm,
    transitionAbsoluteRowBaseForm_value]
  change seed.rowBase + _ =
    dite (cell < seed.height)
      (fun h => (arithmeticCfgWires tm seed.height seed.rowBase).stackCell k
        ⟨cell, h⟩ code)
      (fun _ => _)
  simp only [hcell, dite_true]
  rw [arithmeticCfgWires_stackCell]
  simp only [TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    transitionStackBitOffsetAffine_eval]
  simp [transitionEqPrefixWidth, TransitionAffineNat.eval]
  ring

/-- Every source cell that a fixed statement route may expose lies strictly
below the verifier's published public height. -/
theorem verifierTransitionRouteSourceCell_lt_height
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (cell : Nat)
    (hcell : cell ≤ 2 * maxStackActionsPerStep W.machine.tm) :
    cell < (verifierHeight W).eval input.length := by
  have hpadding := verifierHeight_actionPadding_le W input.length
  omega

/-- Seed-specialized affine equation for every coordinate permitted by the
static statement-route budget. -/
theorem verifierTransitionWidenedStackCellForm_value
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (k : W.machine.tm.K) (cell : Nat)
    (code : Fin ((reachableAlphabet W.machine.tm k).card + 1))
    (hcell : cell ≤ 2 * maxStackActionsPerStep W.machine.tm) :
    affineUnaryTripleFormValue
        (transitionWidenedStackCellForm W.machine.tm k cell code)
        (transitionTailAffineSeed seed) =
      (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
        seed.rowBase).stackCell k
          ⟨cell, by
            rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
            exact lt_of_lt_of_le
              (verifierTransitionRouteSourceCell_lt_height W input cell hcell)
              (Nat.le_add_right _ _)⟩ code := by
  apply transitionWidenedStackCellForm_value
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact verifierTransitionRouteSourceCell_lt_height W input cell hcell

end CLRS.Chapter34.Turing.CookLevin


