-- Prove2me | Definitions.Def_PricingWithTips3DM_a79ce5303af3440f3d4b538fPart1
-- name    : PricingWithTips3DM_a79ce5303af3440f3d4b538fPart1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:24:00.157042+00:00
-- url     : https://prove2.me/theorems/869df786-ca44-4993-89d2-a26414163c9d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3d06fdaba09255b5d609af60
import Definitions.Def_PricingWithTips3DM_1a1974f54f1a1e0128c37c0a
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One contiguous public-row segment together with its corresponding
contiguous workspace projection.  All three quantities are affine in the
runtime public height. -/
structure TransitionEqSegment where
  publicBase : TransitionAffineNat
  workspaceBase : TransitionAffineNat
  count : TransitionAffineNat
deriving DecidableEq, Repr

/-- Turn a height-affine natural into a fixed affine form over a transition
row seed. -/
def transitionHeightAffineForm
    (form : TransitionAffineNat) : AffineUnaryTripleForm :=
  { constant := form.constant
    first := form.coefficient
    second := 0
    third := 0 }

@[simp] theorem transitionHeightAffineForm_value
    (form : TransitionAffineNat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue (transitionHeightAffineForm form)
        (transitionTailAffineSeed seed) = form.eval seed.height := by
  simp [transitionHeightAffineForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval]

/-- Affine stack-prefix offset in the public row. -/
noncomputable def transitionStackBitOffsetAffine
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionAffineNat :=
  { constant := arithmeticStackOrdinal tm k
    coefficient := cfgStackBitOffsetHeightCoeff tm k }

@[simp] theorem transitionStackBitOffsetAffine_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionStackBitOffsetAffine tm k).eval height =
      cfgStackBitOffset tm height k := by
  rw [cfgStackBitOffset_eq_affine]
  rfl

/-- Halted, label, and state coordinates preceding all stacks. -/
def transitionEqPrefixWidth (tm : _root_.Turing.FinTM2) : Nat :=
  1 + (labelCount tm + 1) + stateCount tm

/-- Fixed prefix segment, identical in the public and workspace rows. -/
def transitionEqPrefixSegment
    (tm : _root_.Turing.FinTM2) : TransitionEqSegment :=
  { publicBase := TransitionAffineNat.const 0
    workspaceBase := TransitionAffineNat.const 0
    count := TransitionAffineNat.const (transitionEqPrefixWidth tm) }

/-- Public height coordinates of one fixed stack. -/
noncomputable def transitionEqStackHeightSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionEqSegment :=
  let header := TransitionAffineNat.const (transitionEqPrefixWidth tm)
  let stackOffset := transitionStackBitOffsetAffine tm k
  { publicBase := header.add stackOffset
    workspaceBase := header.add
      (stackOffset.shiftInput (maxPushesPerStep tm))
    count := { constant := 1, coefficient := 1 } }

/-- Public cell-symbol coordinates of one fixed stack. -/
noncomputable def transitionEqStackCellSegment
    (tm : _root_.Turing.FinTM2) (k : tm.K) : TransitionEqSegment :=
  let header := TransitionAffineNat.const (transitionEqPrefixWidth tm)
  let publicOffset := transitionStackBitOffsetAffine tm k
  let workspaceOffset :=
    publicOffset.shiftInput (maxPushesPerStep tm)
  let heightSucc : TransitionAffineNat :=
    { constant := 1, coefficient := 1 }
  let width := (reachableAlphabet tm k).card + 1
  { publicBase := (header.add publicOffset).add heightSucc
    workspaceBase := (header.add workspaceOffset).add
      (heightSucc.shiftInput (maxPushesPerStep tm))
    count := { constant := 0, coefficient := width } }

/-- Canonical fixed list of equality segments: common prefix, then height and
cell blocks for every stack in the machine's fixed finite ordering. -/
noncomputable def transitionEqSegments
    (tm : _root_.Turing.FinTM2) : List TransitionEqSegment :=
  transitionEqPrefixSegment tm ::
    (arithmeticRuntimeStackSourceIndices tm).flatMap fun index =>
      let k := (arithmeticStackEquiv tm).symm index
      [transitionEqStackHeightSegment tm k,
        transitionEqStackCellSegment tm k]

@[simp] theorem transitionEqPrefixSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    ((transitionEqPrefixSegment tm).publicBase.eval height,
      (transitionEqPrefixSegment tm).workspaceBase.eval height,
      (transitionEqPrefixSegment tm).count.eval height) =
      (0, 0, transitionEqPrefixWidth tm) := by
  simp [transitionEqPrefixSegment]

@[simp] theorem transitionEqStackHeightSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    ((transitionEqStackHeightSegment tm k).publicBase.eval height,
      (transitionEqStackHeightSegment tm k).workspaceBase.eval height,
      (transitionEqStackHeightSegment tm k).count.eval height) =
      (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k,
        transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k,
        height + 1) := by
  simp [transitionEqStackHeightSegment, workHeight]
  simp [TransitionAffineNat.eval]
  omega

@[simp] theorem transitionEqStackCellSegment_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    ((transitionEqStackCellSegment tm k).publicBase.eval height,
      (transitionEqStackCellSegment tm k).workspaceBase.eval height,
      (transitionEqStackCellSegment tm k).count.eval height) =
      (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k +
          (height + 1),
        transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k +
          (workHeight tm height + 1),
        height * ((reachableAlphabet tm k).card + 1)) := by
  simp only [transitionEqStackCellSegment,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    TransitionAffineNat.eval_shiftInput,
    transitionStackBitOffsetAffine_eval]
  simp [TransitionAffineNat.eval, workHeight]
  constructor
  · ring
  constructor <;> ring
end CLRS.Chapter34.Turing.CookLevin


