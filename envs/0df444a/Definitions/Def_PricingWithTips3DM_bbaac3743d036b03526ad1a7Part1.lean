-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part1
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:50:58.09424+00:00
-- url     : https://prove2.me/theorems/daa3202b-9866-4b9d-ae39-d1ac6ae0f100
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_7a943b958b08655a77c479c2
import Definitions.Def_PricingWithTips3DM_afa391945f44504e78ade3cb
import Definitions.Def_PricingWithTips3DM_ece69b1aeaa1b2e7e009b8f5
import Definitions.Def_PricingWithTips3DM_a109ba81e03654d2e3b00464
import Definitions.Def_PricingWithTips3DM_f6afa4e253c60b6b5fa62b42
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

noncomputable def cfgStackBitOffsetHeightCoeff
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact ∑ j : Fin (keyEquiv k),
    ((reachableAlphabet tm
      (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2)

/-- The dependent stack-bit prefix is affine in the runtime height. -/
theorem cfgStackBitOffset_eq_affine
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :
    cfgStackBitOffset tm H k =
      arithmeticStackOrdinal tm k + cfgStackBitOffsetHeightCoeff tm k * H := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  unfold cfgStackBitOffset cfgStackBitOffsetHeightCoeff
    arithmeticStackOrdinal
  change (∑ j : Fin (keyEquiv k),
      cfgStackBitWidth tm H
        (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))) = _
  calc
    (∑ j : Fin (keyEquiv k),
        cfgStackBitWidth tm H
          (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))) =
        ∑ j : Fin (keyEquiv k),
          (1 + ((reachableAlphabet tm
            (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2) *
              H) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [cfgStackBitWidth]
      ring
    _ = (∑ _j : Fin (keyEquiv k), 1) +
          ∑ j : Fin (keyEquiv k),
            ((reachableAlphabet tm
              (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2) *
                H := Finset.sum_add_distrib
    _ = (keyEquiv k).val +
          (∑ j : Fin (keyEquiv k),
            ((reachableAlphabet tm
              (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))).card + 2)) *
              H := by
      rw [← Finset.sum_mul]
      simp

/-- Constant part of the raw one-hot gate count. -/
def arithmeticRawOneHotGateCountConstant
    (tm : _root_.Turing.FinTM2) : Nat :=
  (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
    7 * arithmeticStackCount tm

/-- Height coefficient of the raw one-hot gate count. -/
noncomputable def arithmeticRawOneHotGateCountHeightCoeff
    (tm : _root_.Turing.FinTM2) : Nat := by
  letI : Fintype tm.K := tm.kFin
  exact ∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 10)

/-- The complete raw one-hot trace length is affine in runtime height. -/
theorem arithmeticRawOneHotGateCount_eq_affine
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    arithmeticRawOneHotGateCount tm H =
      arithmeticRawOneHotGateCountConstant tm +
        arithmeticRawOneHotGateCountHeightCoeff tm * H := by
  letI : Fintype tm.K := tm.kFin
  unfold arithmeticRawOneHotGateCount
    arithmeticRawOneHotGateCountConstant
    arithmeticRawOneHotGateCountHeightCoeff arithmeticStackCount
  calc
    (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
        ∑ k : tm.K,
          ((3 * (H + 1) + 4) +
            H * (3 * ((reachableAlphabet tm k).card + 1) + 4)) =
      (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
        ∑ k : tm.K,
          (7 + (3 * (reachableAlphabet tm k).card + 10) * H) := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
          7 * Fintype.card tm.K +
        (∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 10)) * H := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
      ring

def affineValidityForm (constant height start rowBase : Nat) :
    AffineUnaryTripleForm :=
  { constant := constant
    first := height
    second := start
    third := rowBase }

def arithmeticStackBlockStartConstant
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat :=
  arithmeticRawOneHotGateCountConstant tm + 5 +
    arithmeticStackOrdinal tm k

def arithmeticStackBlockStartHeightCoeff
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat :=
  arithmeticRawOneHotGateCountHeightCoeff tm +
    7 * arithmeticStackOrdinal tm k

/-- Eight unary values needed by one standalone stack invocation, in exact
consumption order.  The inserted zero emits the internal `frameEnd` between
the six-field header and the runtime-height payload; the final repeated
height receives the outer stack `frameEnd`. -/
noncomputable def arithmeticValidityTailStackOperandForms
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List AffineUnaryTripleForm :=
  let blockConstant := arithmeticStackBlockStartConstant tm k
  let blockHeight := arithmeticStackBlockStartHeightCoeff tm k
  let offsetConstant := arithmeticStackOrdinal tm k
  let offsetHeight := cfgStackBitOffsetHeightCoeff tm k
  let maskBaseConstant :=
    1 + (labelCount tm + 1) + stateCount tm + offsetConstant + 1
  let blankConstant :=
    1 + (labelCount tm + 1) + stateCount tm + offsetConstant + 1 +
      (reachableAlphabet tm k).card
  [ affineValidityForm (blockConstant + 1) (blockHeight + 1) 1 0,
    affineValidityForm blockConstant (blockHeight + 1) 1 0,
    affineValidityForm blankConstant (offsetHeight + 1) 0 1,
    affineValidityForm 0 1 0 0,
    affineValidityForm blockConstant blockHeight 1 0,
    affineValidityForm maskBaseConstant (offsetHeight + 1) 0 1,
    affineValidityForm 0 0 0 0,
    affineValidityForm 0 1 0 0 ]

/-- Fixed stack table in canonical machine-stack order. -/
noncomputable def arithmeticValidityTailStackOperandFormsFamily
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun j =>
    arithmeticValidityTailStackOperandForms tm
      ((arithmeticStackEquiv tm).symm j)

/-- Four fixed fields that precede the variable raw-output frame family in
the final-conjunction source invocation. -/
noncomputable def arithmeticValidityTailFinalPrefixForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  let rawConstant := arithmeticRawOneHotGateCountConstant tm
  let rawHeight := arithmeticRawOneHotGateCountHeightCoeff tm
  let stackCount := arithmeticStackCount tm
  [ affineValidityForm (rawConstant + 5 + stackCount)
      (rawHeight + 7 * stackCount) 1 0,
    affineValidityForm 0 1 0 0,
    affineValidityForm (rawConstant + 5) rawHeight 1 0,
    affineValidityForm (rawConstant + 4) rawHeight 1 0 ]

/-- Complete fixed affine table for one validity-tail row. -/
noncomputable def arithmeticValidityTailFixedOperandForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  arithmeticValidityTailStackOperandFormsFamily tm ++
    arithmeticValidityTailFinalPrefixForms tm

def validityRowAffineSeed (H start rowBase : Nat) :
    AffineUnaryTripleSeed :=
  { first := H, second := start, third := rowBase }

/-- Semantic fixed values, stated directly from the established compact
source frames rather than from the affine formulas. -/
noncomputable def arithmeticValidityTailFixedOperandValues
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List Nat :=
  ((arithmeticRuntimeStackSourceSeeds tm H start rowBase).flatMap fun seed =>
      [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
        seed.maskStart, seed.maskBase + seed.count, 0, seed.count]) ++
    [ arithmeticValidityFinalStart tm H start,
      H,
      arithmeticStackValidityStart tm H start,
      arithmeticHaltedMatchStart tm H start + 4 ]

theorem arithmeticValidityTailStackOperandForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineUnaryTripleMap (arithmeticValidityTailStackOperandForms tm k)
        (validityRowAffineSeed H start rowBase) =
      let seed := arithmeticRuntimeStackSourceSeed tm H start rowBase k
      [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
        seed.maskStart, seed.maskBase + seed.count, 0, seed.count] := by
  simp [arithmeticValidityTailStackOperandForms, affineUnaryTripleMap,
    affineUnaryTripleFormValue, affineValidityForm,
    validityRowAffineSeed, arithmeticRuntimeStackSourceSeed,
    arithmeticStackCellTraceStart, arithmeticStackBlockStart,
    arithmeticStackValidityStart, arithmeticHaltedMatchStart,
    arithmeticStackMaskWireBase, arithmeticStackCellBlankBase,
    arithmeticStackBlockStartConstant,
    arithmeticStackBlockStartHeightCoeff,
    arithmeticRawOneHotGateCount_eq_affine,
    cfgStackBitOffset_eq_affine]
  ring <;> simp

theorem arithmeticValidityTailFinalPrefixForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityTailFinalPrefixForms tm)
        (validityRowAffineSeed H start rowBase) =
      [ arithmeticValidityFinalStart tm H start,
        H,
        arithmeticStackValidityStart tm H start,
        arithmeticHaltedMatchStart tm H start + 4 ] := by
  simp [arithmeticValidityTailFinalPrefixForms, affineUnaryTripleMap,
    affineUnaryTripleFormValue, affineValidityForm,
    validityRowAffineSeed, arithmeticValidityFinalStart,
    arithmeticStackValidityStart, arithmeticHaltedMatchStart,
    arithmeticRawOneHotGateCount_eq_affine]
  ring <;> simp

/-- The fixed affine table is byte-value exact for every runtime row seed. -/
theorem arithmeticValidityTailFixedOperandForms_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
        (validityRowAffineSeed H start rowBase) =
      arithmeticValidityTailFixedOperandValues tm H start rowBase := by
  unfold arithmeticValidityTailFixedOperandForms
    arithmeticValidityTailFixedOperandValues
  rw [show affineUnaryTripleMap
      (arithmeticValidityTailStackOperandFormsFamily tm ++
        arithmeticValidityTailFinalPrefixForms tm)
      (validityRowAffineSeed H start rowBase) =
      affineUnaryTripleMap (arithmeticValidityTailStackOperandFormsFamily tm)
          (validityRowAffineSeed H start rowBase) ++
        affineUnaryTripleMap (arithmeticValidityTailFinalPrefixForms tm)
          (validityRowAffineSeed H start rowBase) by
    simp [affineUnaryTripleMap]]
  rw [arithmeticValidityTailFinalPrefixForms_eq]
  congr 1
  unfold arithmeticValidityTailStackOperandFormsFamily
    arithmeticRuntimeStackSourceSeeds
  rw [List.flatMap_map]
  simp only [affineUnaryTripleMap, List.map_flatMap]
  apply List.flatMap_congr
  intro j hj
  exact arithmeticValidityTailStackOperandForms_eq tm H start rowBase
    ((arithmeticStackEquiv tm).symm j)

/-- Fixed operand values for every canonical verifier row. -/
noncomputable def verifierValidityRowTailFixedOperandValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  (verifierValidityRowSeeds W input).flatMap fun seed =>
    arithmeticValidityTailFixedOperandValues W.machine.tm
      seed.height seed.start seed.rowBase

/-- The generic affine source consumes exactly the established row-seed byte
stream at the Cook--Levin specialization. -/
theorem verifierValidityRowTailAffineSeedEncoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTripleSeedFamily
        ((verifierValidityRowSeeds W input).map fun seed =>
          validityRowAffineSeed seed.height seed.start seed.rowBase) =
      verifierValidityRowSeedFrames W input := by
  rw [verifierValidityRowSeedFrames_eq_seeds]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTripleSeedFamily,
        encodeAffineUnaryTripleSeed, List.flatMap_cons]
      rw [ih]
      rfl

theorem verifierValidityRowTailAffineValues_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineUnaryTripleMapFamily
        (arithmeticValidityTailFixedOperandForms W.machine.tm)
        ((verifierValidityRowSeeds W input).map fun seed =>
          validityRowAffineSeed seed.height seed.start seed.rowBase) =
      verifierValidityRowTailFixedOperandValues W input := by
  unfold affineUnaryTripleMapFamily verifierValidityRowTailFixedOperandValues
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact arithmeticValidityTailFixedOperandForms_eq
    W.machine.tm seed.height seed.start seed.rowBase

/-- The raw verifier word polynomially computes all fixed affine values of
every tail invocation.  Runtime-height one-hot frames remain a separate,
already verified structured-row phase. -/
noncomputable def
    verifierValidityRowTailFixedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ =>
        encodeUnaryFrame (verifierValidityRowTailFixedOperandValues W input)) := by
  let seedSource := verifierValidityRowSeedFrames_computableInPolyTime W
  let affineSource := affineUnaryTripleMapFamily_computableInPolyTime
    (arithmeticValidityTailFixedOperandForms W.machine.tm)
  let repackagedSeedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTripleSeedFamily
        (fun input : List Γ =>
          (verifierValidityRowSeeds W input).map fun seed =>
            validityRowAffineSeed seed.height seed.start seed.rowBase) :=
    { tm := seedSource.tm
      inputAlphabet := seedSource.inputAlphabet
      outputAlphabet := seedSource.outputAlphabet
      time := seedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailAffineSeedEncoding_eq W input] using
          seedSource.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      repackagedSeedSource affineSource
  simpa [Function.comp_def,
    verifierValidityRowTailAffineValues_eq] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin


